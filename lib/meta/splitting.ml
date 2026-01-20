
module type MTPSPLITTING  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator list
    val applicable : operator -> bool
    val apply : operator -> StateSyn.__State list
    val menu : operator -> string
    val index : operator -> int
    val compare : operator -> operator -> order
  end;;




module MTPSplitting(MTPSplitting:sig
                                   module MTPGlobal : MTPGLOBAL
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Heuristic : HEURISTIC
                                   module MTPAbstract : MTPABSTRACT
                                   module MTPrint : MTPRINT
                                   module Names : NAMES
                                   module Conv : CONV
                                   module Whnf : WHNF
                                   module TypeCheck : TYPECHECK
                                   module Subordinate : SUBORDINATE
                                   module FunTypeCheck : FUNTYPECHECK
                                   module Index : INDEX
                                   module Print : PRINT
                                   module Unify : UNIFY
                                 end) : MTPSPLITTING =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type 'a flag =
      | Active of 'a 
      | InActive 
    type __Operator =
      | Operator of ((StateSyn.__State * int) * StateSyn.__State flag list *
      Heuristic.index) 
    type nonrec operator = __Operator
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module H = Heuristic
    let rec makeOperator __0__ __1__ __2__ __3__ __4__ __5__ __6__ =
      match (__0__, __1__, __2__, __3__, __4__, __5__, __6__) with
      | ((__S, k), __L, Splits n, g, __I, m, true) ->
          Operator
            ((__S, k), __L,
              {
                sd = n;
                ind = __I;
                c = (List.length __L);
                m;
                r = 1;
                p = (g + 1)
              })
      | ((__S, k), __L, Splits n, g, __I, m, false) ->
          Operator
            ((__S, k), __L,
              {
                sd = n;
                ind = __I;
                c = (List.length __L);
                m;
                r = 0;
                p = (g + 1)
              })(* non-recursive case *)(* recursive case *)
    let rec aux __7__ __8__ =
      match (__7__, __8__) with
      | (I.Null, I.Null) -> I.Null
      | (Decl (__G, __D), Decl (__B, Lemma _)) ->
          I.Decl ((aux (__G, __B)), (F.Prim __D))
      | ((Decl (_, __D) as G), (Decl (_, Parameter (Some l)) as B)) ->
          let LabelDec (name, _, __G2) = F.labelLookup l in
          let (Psi', __G') = aux' (__G, __B, (List.length __G2)) in
          I.Decl (Psi', (F.Block (F.CtxBlock ((Some l), __G'))))
    let rec aux' __9__ __10__ __11__ =
      match (__9__, __10__, __11__) with
      | (__G, __B, 0) -> ((aux (__G, __B)), I.Null)
      | (Decl (__G, __D), Decl (__B, Parameter (Some _)), n) ->
          let (Psi', __G') = aux' (__G, __B, (n - 1)) in
          (Psi', (I.Decl (__G', __D)))
    let rec conv (__Gs) (__Gs') =
      let exception Conv  in
        let rec conv __12__ __13__ =
          match (__12__, __13__) with
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (__G, Dec (_, __V)), s), (Decl (__G', Dec (_, __V')), s'))
              ->
              let (s1, s1') = conv ((__G, s), (__G', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((__V, s1), (__V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (__Gs, __Gs'); true with | Conv -> false
    let rec createEVarSpine (__G) (__Vs) =
      createEVarSpineW (__G, (Whnf.whnf __Vs))
    let rec createEVarSpineW __14__ __15__ =
      match (__14__, __15__) with
      | (__G, ((Uni (I.Type), s) as Vs)) -> (I.Nil, __Vs)
      | (__G, ((Root _, s) as Vs)) -> (I.Nil, __Vs)
      | (__G, (Pi (((Dec (_, __V1) as D), _), __V2), s)) ->
          let __X = I.newEVar (__G, (I.EClo (__V1, s))) in
          let (__S, __Vs) =
            createEVarSpine (__G, (__V2, (I.Dot ((I.Exp __X), s)))) in
          ((I.App (__X, __S)), __Vs)(* s = id *)(* s = id *)
    let rec createAtomConst (__G) (__H) =
      let cid = match __H with | Const cid -> cid | Skonst cid -> cid in
      let __V = I.constType cid in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root (__H, __S)), __Vs)
    let rec createAtomBVar (__G) k =
      let Dec (_, __V) = I.ctxDec (__G, k) in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root ((I.BVar k), __S)), __Vs)
    let rec someEVars __16__ __17__ __18__ =
      match (__16__, __17__, __18__) with
      | (__G, nil, s) -> s
      | (__G, (Dec (_, __V))::__L, s) ->
          someEVars
            (__G, __L,
              (I.Dot ((I.Exp (I.newEVar (__G, (I.EClo (__V, s))))), s)))
    let rec maxNumberParams a =
      let rec maxNumberParams' n =
        if n < 0
        then 0
        else
          (let LabelDec (name, __G1, __G2) = F.labelLookup n in
           let m' =
             foldr
               (fun (Dec (_, __V)) ->
                  fun m -> if (I.targetFam __V) = a then m + 1 else m) 0 __G2 in
           (maxNumberParams' (n - 1)) + m') in
      maxNumberParams' ((F.labelSize ()) - 1)
    let rec maxNumberLocalParams __19__ __20__ =
      match (__19__, __20__) with
      | (Pi ((Dec (_, __V1), _), __V2), a) ->
          let m = maxNumberLocalParams (__V2, a) in
          if (I.targetFam __V1) = a then m + 1 else m
      | (Root _, a) -> 0
    let rec maxNumberConstCases a = List.length (Index.lookup a)
    let rec maxNumberCases (__V) a =
      (+) ((+) (maxNumberParams a) maxNumberLocalParams (__V, a))
        maxNumberConstCases a
    let rec ctxSub __21__ __22__ =
      match (__21__, __22__) with
      | (nil, s) -> nil
      | ((__D)::__G, s) -> (::) (I.decSub (__D, s)) ctxSub (__G, (I.dot1 s))
    let rec createTags __23__ __24__ =
      match (__23__, __24__) with
      | (0, l) -> I.Null
      | (n, l) -> I.Decl ((createTags ((n - 1), l)), (S.Parameter (Some l)))
    let rec createLemmaTags =
      function
      | I.Null -> I.Null
      | Decl (__G, __D) ->
          I.Decl
            ((createLemmaTags __G),
              (S.Lemma (S.Splits (!MTPGlobal.maxSplit))))
    let rec constCases __25__ __26__ __27__ __28__ __29__ =
      match (__25__, __26__, __27__, __28__, __29__) with
      | (__G, __Vs, nil, abstract, ops) -> ops
      | (__G, __Vs, (Const c)::Sgn, abstract, ops) ->
          let (__U, __Vs') = createAtomConst (__G, (I.Const c)) in
          constCases
            (__G, __Vs, Sgn, abstract,
              (CSManager.trail
                 (fun () ->
                    try
                      if Unify.unifiable (__G, __Vs, __Vs')
                      then (Active (abstract __U)) :: ops
                      else ops
                    with | Error _ -> InActive :: ops)))
    let rec paramCases __30__ __31__ __32__ __33__ __34__ =
      match (__30__, __31__, __32__, __33__, __34__) with
      | (__G, __Vs, 0, abstract, ops) -> ops
      | (__G, __Vs, k, abstract, ops) ->
          let (__U, __Vs') = createAtomBVar (__G, k) in
          paramCases
            (__G, __Vs, (k - 1), abstract,
              (CSManager.trail
                 (fun () ->
                    try
                      if Unify.unifiable (__G, __Vs, __Vs')
                      then (Active (abstract __U)) :: ops
                      else ops
                    with | Error _ -> InActive :: ops)))
    let rec constAndParamCases ops0 c (__G) k (__V, s') abstract =
      constCases
        (__G, (__V, s'), (Index.lookup c), abstract,
          (paramCases (__G, (__V, s'), k, abstract, ops0)))
    let rec metaCases d ops0 c (__G) k (__Vs) abstract =
      let g = I.ctxLength __G in
      let rec select __35__ __36__ =
        match (__35__, __36__) with
        | (0, ops) -> ops
        | (d', ops) ->
            let n = (g - d') + 1 in
            let Dec (_, __V) = I.ctxDec (__G, n) in
            let ops' =
              if (I.targetFam __V) = c
              then
                let (__U, __Vs') = createAtomBVar (__G, n) in
                CSManager.trail
                  (fun () ->
                     try
                       ((if Unify.unifiable (__G, __Vs, __Vs')
                         then (Active (abstract __U)) :: ops
                         else ops)
                       (* abstract state *))
                     with | Error _ -> InActive :: ops)
              else ops in
            select ((d' - 1), ops') in
      select (d, ops0)
    let rec lowerSplitDest __37__ __38__ __39__ __40__ __41__ =
      match (__37__, __38__, __39__, __40__, __41__) with
      | (__G, k, ((Root (Const c, _) as V), s'), abstract, cases) ->
          cases (c, __G, (I.ctxLength __G), (__V, s'), abstract)
      | (__G, k, (Pi ((__D, __P), __V), s'), abstract, cases) ->
          let __D' = I.decSub (__D, s') in
          lowerSplitDest
            ((I.Decl (__G, __D')), (k + 1), (__V, (I.dot1 s')),
              (fun (__U) -> abstract (I.Lam (__D', __U))), cases)
    let rec abstractErrorLeft (__G, __B) s =
      raise (MTPAbstract.Error "Cannot split left of parameters")
    let rec abstractErrorRight (__G, __B) s =
      raise (MTPAbstract.Error "Cannot split right of parameters")
    let rec split ((Dec (_, __V) as D), __T) sc abstract =
      let rec split' n cases =
        if n < 0
        then
          let ((__G', __B'), s', (__G0, __B0), _) = sc (I.Null, I.Null) in
          let rec abstract' (__U') =
            let ((G'', B''), s'') =
              MTPAbstract.abstractSub'
                ((__G', __B'), (I.Dot ((I.Exp __U'), s')),
                  (I.Decl (__B0, __T))) in
            let _ =
              if !Global.doubleCheck
              then
                let Psi'' = aux (G'', B'') in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                let Psi = aux ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))) in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                FunTypeCheck.checkSub (Psi'', s'', Psi)
              else () in
            ((abstract ((G'', B''), s''))
              (* G' |- U' : V[s'] *)(* G' |- U'.s' : G, V[s'] *)) in
          ((lowerSplitDest
              (__G', 0, (__V, s'), abstract', (constAndParamCases cases)))
            (* |- G' = parameter blocks of G  ctx*)(* G' |- B' tags *)
            (* G' |- s' : G *))
        else
          (let LabelDec (name, __G1, __G2) = F.labelLookup n in
           let t = someEVars (I.Null, __G1, I.id) in
           let __B1 = createLemmaTags (F.listToCtx __G1) in
           let G2t = ctxSub (__G2, t) in
           let length = List.length __G2 in
           let __B2 = createTags (length, n) in
           let ((__G', __B'), s', (__G0, __B0), p) =
             sc ((Names.ctxName (F.listToCtx G2t)), __B2) in
           let rec abstract' (__U') =
             if p
             then
               raise (MTPAbstract.Error "Cannot split right of parameters")
             else
               (let ((G'', B''), s'') =
                  MTPAbstract.abstractSub
                    (t, __B1, (__G', __B'), (I.Dot ((I.Exp __U'), s')),
                      (I.Decl (__B0, __T))) in
                let _ =
                  if !Global.doubleCheck
                  then
                    let Psi'' = aux (G'', B'') in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                    let Psi =
                      aux ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))) in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                    FunTypeCheck.checkSub (Psi'', s'', Psi)
                  else () in
                ((abstract ((G'', B''), s''))
                  (* G' |- U.s' : G, V *)(* . |- t : G1 *)
                  (* . |- G'' ctx *)(* G'' |- B'' tags *)
                  (* G'' = G1'', G2', G2'' *)(* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)))
             (* G' |- U' : V[s'] *) in
           let cases' =
             lowerSplitDest
               (__G', 0, (__V, s'), abstract', (metaCases (length, cases))) in
           ((split' ((n - 1), cases'))
             (* . |- t : G1 *)(* . |- G2 [t] ctx *)
             (* G2 [t] |- B2 tags *)(* . |- G' ctx *)
             (* G' |- B' tags *)(* G' |- s : G = G0 *)
             (* G0 |- B0 tags *)(* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *))) in
      split' (((F.labelSize ()) - 1), nil)
    let rec occursInExp __42__ __43__ =
      match (__42__, __43__) with
      | (k, Uni _) -> false
      | (k, Pi (DP, __V)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), __V))
      | (k, Root (__C, __S)) ->
          (occursInCon (k, __C)) || (occursInSpine (k, __S))
      | (k, Lam (__D, __V)) ->
          (occursInDec (k, __D)) || (occursInExp ((k + 1), __V))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (__B) ->
                 __B || (occursInExp (k, (Whnf.normalize (__U, I.id)))))
            false
    let rec occursInCon __44__ __45__ =
      match (__44__, __45__) with
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false
      | (k, Def _) -> false
      | (k, Skonst _) -> false
    let rec occursInSpine __46__ __47__ =
      match (__46__, __47__) with
      | (_, I.Nil) -> false
      | (k, App (__U, __S)) ->
          (occursInExp (k, __U)) || (occursInSpine (k, __S))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec isIndexInit k = false
    let rec isIndexSucc (__D) isIndex k =
      (occursInDec (k, __D)) || (isIndex (k + 1))
    let rec isIndexFail (__D) isIndex k = isIndex (k + 1)
    let rec abstractInit
      (State (n, (__G, __B), (IH, OH), d, __O, __H, __F) as S) (__G', __B')
      s' =
      if !Global.doubleCheck then TypeCheck.typeCheckCtx __G' else ();
      if !Global.doubleCheck
      then FunTypeCheck.isFor (__G', (F.forSub (__F, s')))
      else ();
      S.State
        (n, (__G', __B'), (IH, OH), d, (S.orderSub (__O, s')),
          (map (fun i -> fun (__F') -> (i, (F.forSub (__F', s')))) __H),
          (F.forSub (__F, s')))
    let rec abstractCont (__D, __T) abstract (__G, __B) s =
      abstract
        (((I.Decl (__G, (Whnf.normalizeDec (__D, s)))),
           (I.Decl (__B, (S.normalizeTag (__T, s))))), (I.dot1 s))
    let rec makeAddressInit (__S) k = (__S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec occursInOrder __48__ __49__ __50__ __51__ =
      match (__48__, __49__, __50__, __51__) with
      | (n, Arg (__Us, Vt), k, sc) ->
          let __U' = Whnf.normalize __Us in
          if occursInExp (k, __U') then Some n else sc (n + 1)
      | (n, Lex (__Os), k, sc) -> occursInOrders (n, __Os, k, sc)
      | (n, Simul (__Os), k, sc) -> occursInOrders (n, __Os, k, sc)
    let rec occursInOrders __52__ __53__ __54__ __55__ =
      match (__52__, __53__, __54__, __55__) with
      | (n, nil, k, sc) -> sc n
      | (n, (__O)::__Os, k, sc) ->
          occursInOrder
            (n, __O, k, (fun n' -> occursInOrders (n', __Os, k, sc)))
    let rec inductionInit (__O) k =
      occursInOrder (0, __O, k, (fun n -> None))
    let rec inductionCont induction k = induction (k + 1)
    let rec expand' __56__ __57__ __58__ __59__ __60__ =
      match (__56__, __57__, __58__, __59__, __60__) with
      | (((I.Null, I.Null) as GB), isIndex, abstract, makeAddress, induction)
          ->
          (((fun (Gp) ->
               fun (Bp) ->
                 ((Gp, Bp), (I.Shift (I.ctxLength Gp)), GB, false))), nil)
      | (((Decl (__G, __D), Decl (__B, (Lemma (Splits _ as K) as T))) as GB),
         isIndex, abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__G, __B), (isIndexSucc (__D, isIndex)),
                (abstractCont ((__D, __T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __V) = __D in
          let rec sc' (Gp) (Bp) =
            let ((__G', __B'), s', (__G0, __B0), p') = sc (Gp, Bp) in
            let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
            ((((__G', __B'), (I.Dot ((I.Exp __X), s')),
                ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))), p'))
              (* G' |- X : V[s'] *)(* G' |- X.s' : G, D *)) in
          let ops' =
            if (not (isIndex 1)) && ((S.splitDepth __K) > 0)
            then
              let a = I.targetFam __V in
              (makeOperator
                 ((makeAddress 1), (split ((__D, __T), sc, abstract)), __K,
                   (I.ctxLength __G), (induction 1),
                   (maxNumberCases (__V, a)), (Subordinate.below (a, a))))
                :: ops
            else ops in
          (sc', ops')
      | ((Decl (__G, __D), Decl (__B, (Lemma (S.RL) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__G, __B), (isIndexSucc (__D, isIndex)),
                (abstractCont ((__D, __T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __V) = __D in
          let rec sc' (Gp) (Bp) =
            let ((__G', __B'), s', (__G0, __B0), p') = sc (Gp, Bp) in
            let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
            ((__G', __B'), (I.Dot ((I.Exp __X), s')),
              ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))), p') in
          (sc', ops)
      | ((Decl (__G, __D), Decl (__B, (Lemma (S.RLdone) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__G, __B), (isIndexSucc (__D, isIndex)),
                (abstractCont ((__D, __T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __V) = __D in
          let rec sc' (Gp) (Bp) =
            let ((__G', __B'), s', (__G0, __B0), p') = sc (Gp, Bp) in
            let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
            ((__G', __B'), (I.Dot ((I.Exp __X), s')),
              ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))), p') in
          (sc', ops)
      | ((Decl (__G, __D), Decl (__B, (Parameter (Some _) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__G, __B), (isIndexSucc (__D, isIndex)), abstractErrorLeft,
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __V) = __D in
          let rec sc' (Gp) (Bp) =
            let ((__G', __B'), s', (__G0, __B0), _) = sc (Gp, Bp) in
            (((I.Decl (__G', (Names.decName (__G', (I.decSub (__D, s')))))),
               (I.Decl (__B', __T))), (I.dot1 s'),
              ((I.Decl (__G0, __D)), (I.Decl (__B0, __T))), true) in
          (sc', ops)
    let rec expand (State (n, (__G0, __B0), _, _, __O, _, _) as S0) =
      let _ = if !Global.doubleCheck then FunTypeCheck.isState __S0 else () in
      let (_, ops) =
        expand'
          ((__G0, __B0), isIndexInit, (abstractInit __S0),
            (makeAddressInit __S0), (inductionInit __O)) in
      ops
    let rec index (Operator ((__S, index), Sl, { c = k })) = k
    let rec compare (Operator (_, _, __I1)) (Operator (_, _, __I2)) =
      H.compare (__I1, __I2)
    let rec isInActive = function | Active _ -> false | InActive -> true
    let rec applicable (Operator (_, Sl, __I)) =
      not (List.exists isInActive Sl)
    let rec apply (Operator (_, Sl, __I)) =
      map
        (function
         | Active (__S) ->
             (if !Global.doubleCheck then FunTypeCheck.isState __S else ();
              __S)
         | InActive -> raise (Error "Not applicable: leftover constraints"))
        Sl
    let rec menu
      (Operator
         ((State (n, (__G, __B), (IH, OH), d, __O, __H, __F), i), Sl, __I) as
         Op)
      =
      let rec active __61__ __62__ =
        match (__61__, __62__) with
        | (nil, n) -> n
        | ((InActive)::__L, n) -> active (__L, n)
        | ((Active _)::__L, n) -> active (__L, (n + 1)) in
      let rec inactive __63__ __64__ =
        match (__63__, __64__) with
        | (nil, n) -> n
        | ((InActive)::__L, n) -> inactive (__L, (n + 1))
        | ((Active _)::__L, n) -> inactive (__L, n) in
      let rec casesToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let rec flagToString __65__ __66__ =
        match (__65__, __66__) with
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (__G, (I.ctxDec (__G, i)))) ^
           " ")
          ^ (H.indexToString __I))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ""
    let expand = expand
    let menu = menu
    let applicable = applicable
    let apply = apply
    let index = index
    let compare = compare
  end ;;
