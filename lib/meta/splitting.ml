
(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
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
    val compare : (operator * operator) -> order
  end;;




(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
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
                                   (*! structure IntSyn : INTSYN !*)
                                   (*! structure FunSyn : FUNSYN !*)
                                   (*! sharing FunSyn.IntSyn = IntSyn !*)
                                   (*! sharing StateSyn'.FunSyn = FunSyn !*)
                                   (*! sharing StateSyn'.IntSyn = IntSyn !*)
                                   (*! sharing MTPAbstract.IntSyn = IntSyn !*)
                                   (* too be removed  -cs *)
                                   (*! sharing Names.IntSyn = IntSyn !*)
                                   (* too be removed  -cs *)
                                   (*! sharing Conv.IntSyn = IntSyn !*)
                                   (*! sharing Whnf.IntSyn = IntSyn !*)
                                   (*! sharing TypeCheck.IntSyn = IntSyn !*)
                                   (*! sharing Subordinate.IntSyn = IntSyn !*)
                                   (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
                                   (*! sharing Index.IntSyn = IntSyn !*)
                                   (*! sharing Print.IntSyn = IntSyn !*)
                                   module Unify : UNIFY
                                 end) : MTPSPLITTING =
  struct
    (*! sharing Unify.IntSyn = IntSyn !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn  !*)
    module StateSyn = StateSyn'
    exception Error of string 
    (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *)
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
    let rec makeOperator =
      function
      | ((S, k), __l, Splits n, g, I, m, true__) ->
          Operator
            ((S, k), __l,
              { sd = n; ind = I; c = (List.length __l); m; r = 1; p = (g + 1) })
      | ((S, k), __l, Splits n, g, I, m, false__) ->
          Operator
            ((S, k), __l,
              { sd = n; ind = I; c = (List.length __l); m; r = 0; p = (g + 1) })
    let rec aux =
      function
      | (I.Null, I.Null) -> I.Null
      | (Decl (__g, __d), Decl (B, Lemma _)) -> I.Decl ((aux (__g, B)), (F.Prim __d))
      | ((Decl (_, __d) as __g), (Decl (_, Parameter (Some l)) as B)) ->
          let LabelDec (name, _, G2) = F.labelLookup l in
          let (Psi', __g') = aux' (__g, B, (List.length G2)) in
          I.Decl (Psi', (F.Block (F.CtxBlock ((Some l), __g'))))
    let rec aux' =
      function
      | (__g, B, 0) -> ((aux (__g, B)), I.Null)
      | (Decl (__g, __d), Decl (B, Parameter (Some _)), n) ->
          let (Psi', __g') = aux' (__g, B, (n - 1)) in (Psi', (I.Decl (__g', __d)))
    let rec conv (__Gs, __Gs') =
      let exception Conv  in
        let rec conv =
          function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (__g, Dec (_, __v)), s), (Decl (__g', Dec (_, __v')), s')) ->
              let (s1, s1') = conv ((__g, s), (__g', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((__v, s1), (__v', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (__Gs, __Gs'); true__ with | Conv -> false__
    let rec createEVarSpine (__g, __Vs) = createEVarSpineW (__g, (Whnf.whnf __Vs))
    let rec createEVarSpineW =
      function
      | (__g, ((Uni (I.Type), s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, ((Root _, s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, (Pi (((Dec (_, V1) as __d), _), V2), s)) ->
          let x = I.newEVar (__g, (I.EClo (V1, s))) in
          let (S, __Vs) = createEVarSpine (__g, (V2, (I.Dot ((I.Exp x), s)))) in
          ((I.App (x, S)), __Vs)
    let rec createAtomConst (__g, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let __v = I.constType cid in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in ((I.Root (H, S)), __Vs)
    let rec createAtomBVar (__g, k) =
      let Dec (_, __v) = I.ctxDec (__g, k) in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in
      ((I.Root ((I.BVar k), S)), __Vs)
    let rec someEVars =
      function
      | (__g, nil, s) -> s
      | (__g, (Dec (_, __v))::__l, s) ->
          someEVars
            (__g, __l, (I.Dot ((I.Exp (I.newEVar (__g, (I.EClo (__v, s))))), s)))
    let rec maxNumberParams a =
      let rec maxNumberParams' n =
        if n < 0
        then 0
        else
          (let LabelDec (name, G1, G2) = F.labelLookup n in
           let m' =
             foldr
               (function
                | (Dec (_, __v), m) -> if (I.targetFam __v) = a then m + 1 else m)
               0 G2 in
           (maxNumberParams' (n - 1)) + m') in
      maxNumberParams' ((F.labelSize ()) - 1)
    let rec maxNumberLocalParams =
      function
      | (Pi ((Dec (_, V1), _), V2), a) ->
          let m = maxNumberLocalParams (V2, a) in
          if (I.targetFam V1) = a then m + 1 else m
      | (Root _, a) -> 0
    let rec maxNumberConstCases a = List.length (Index.lookup a)
    let rec maxNumberCases (__v, a) =
      (+) ((+) (maxNumberParams a) maxNumberLocalParams (__v, a))
        maxNumberConstCases a
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((__d)::__g, s) -> (::) (I.decSub (__d, s)) ctxSub (__g, (I.dot1 s))
    let rec createTags =
      function
      | (0, l) -> I.Null
      | (n, l) -> I.Decl ((createTags ((n - 1), l)), (S.Parameter (Some l)))
    let rec createLemmaTags =
      function
      | I.Null -> I.Null
      | Decl (__g, __d) ->
          I.Decl
            ((createLemmaTags __g), (S.Lemma (S.Splits (!MTPGlobal.maxSplit))))
    let rec constCases =
      function
      | (__g, __Vs, nil, abstract, ops) -> ops
      | (__g, __Vs, (Const c)::Sgn, abstract, ops) ->
          let (__u, __Vs') = createAtomConst (__g, (I.Const c)) in
          constCases
            (__g, __Vs, Sgn, abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (__g, __Vs, __Vs')
                         then (Active (abstract __u)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec paramCases =
      function
      | (__g, __Vs, 0, abstract, ops) -> ops
      | (__g, __Vs, k, abstract, ops) ->
          let (__u, __Vs') = createAtomBVar (__g, k) in
          paramCases
            (__g, __Vs, (k - 1), abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (__g, __Vs, __Vs')
                         then (Active (abstract __u)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec constAndParamCases ops0 (c, __g, k, (__v, s'), abstract) =
      constCases
        (__g, (__v, s'), (Index.lookup c), abstract,
          (paramCases (__g, (__v, s'), k, abstract, ops0)))
    let rec metaCases (d, ops0) (c, __g, k, __Vs, abstract) =
      let g = I.ctxLength __g in
      let rec select =
        function
        | (0, ops) -> ops
        | (d', ops) ->
            let n = (g - d') + 1 in
            let Dec (_, __v) = I.ctxDec (__g, n) in
            let ops' =
              if (I.targetFam __v) = c
              then
                let (__u, __Vs') = createAtomBVar (__g, n) in
                CSManager.trail
                  (function
                   | () ->
                       (try
                          if Unify.unifiable (__g, __Vs, __Vs')
                          then (Active (abstract __u)) :: ops
                          else ops
                        with | Error _ -> InActive :: ops))
              else ops in
            select ((d' - 1), ops') in
      select (d, ops0)
    let rec lowerSplitDest =
      function
      | (__g, k, ((Root (Const c, _) as __v), s'), abstract, cases) ->
          cases (c, __g, (I.ctxLength __g), (__v, s'), abstract)
      | (__g, k, (Pi ((__d, P), __v), s'), abstract, cases) ->
          let __d' = I.decSub (__d, s') in
          lowerSplitDest
            ((I.Decl (__g, __d')), (k + 1), (__v, (I.dot1 s')),
              (function | __u -> abstract (I.Lam (__d', __u))), cases)
    let rec abstractErrorLeft ((__g, B), s) =
      raise (MTPAbstract.Error "Cannot split left of parameters")
    let rec abstractErrorRight ((__g, B), s) =
      raise (MTPAbstract.Error "Cannot split right of parameters")
    let rec split (((Dec (_, __v) as __d), T), sc, abstract) =
      let rec split' (n, cases) =
        if n < 0
        then
          let ((__g', B'), s', (G0, B0), _) = sc (I.Null, I.Null) in
          let rec abstract' (__u') =
            let ((__g'', B''), s'') =
              MTPAbstract.abstractSub'
                ((__g', B'), (I.Dot ((I.Exp __u'), s')), (I.Decl (B0, T))) in
            let _ =
              if !Global.doubleCheck
              then
                let Psi'' = aux (__g'', B'') in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                let Psi = aux ((I.Decl (G0, __d)), (I.Decl (B0, T))) in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                FunTypeCheck.checkSub (Psi'', s'', Psi)
              else () in
            abstract ((__g'', B''), s'') in
          lowerSplitDest
            (__g', 0, (__v, s'), abstract', (constAndParamCases cases))
        else
          (let LabelDec (name, G1, G2) = F.labelLookup n in
           let t = someEVars (I.Null, G1, I.id) in
           let B1 = createLemmaTags (F.listToCtx G1) in
           let G2t = ctxSub (G2, t) in
           let length = List.length G2 in
           let B2 = createTags (length, n) in
           let ((__g', B'), s', (G0, B0), p) =
             sc ((Names.ctxName (F.listToCtx G2t)), B2) in
           let rec abstract' (__u') =
             if p
             then
               raise (MTPAbstract.Error "Cannot split right of parameters")
             else
               (let ((__g'', B''), s'') =
                  MTPAbstract.abstractSub
                    (t, B1, (__g', B'), (I.Dot ((I.Exp __u'), s')),
                      (I.Decl (B0, T))) in
                let _ =
                  if !Global.doubleCheck
                  then
                    let Psi'' = aux (__g'', B'') in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                    let Psi = aux ((I.Decl (G0, __d)), (I.Decl (B0, T))) in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                    FunTypeCheck.checkSub (Psi'', s'', Psi)
                  else () in
                abstract ((__g'', B''), s'')) in
           let cases' =
             lowerSplitDest
               (__g', 0, (__v, s'), abstract', (metaCases (length, cases))) in
           split' ((n - 1), cases')) in
      split' (((F.labelSize ()) - 1), nil)
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, __v)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), __v))
      | (k, Root (C, S)) -> (occursInCon (k, C)) || (occursInSpine (k, S))
      | (k, Lam (__d, __v)) -> (occursInDec (k, __d)) || (occursInExp ((k + 1), __v))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, B) -> B || (occursInExp (k, (Whnf.normalize (__u, I.id)))))
            false__
    let rec occursInCon =
      function
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, Skonst _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (__u, S)) -> (occursInExp (k, __u)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, __v)) = occursInExp (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec isIndexInit k = false__
    let rec isIndexSucc (__d, isIndex) k =
      (occursInDec (k, __d)) || (isIndex (k + 1))
    let rec isIndexFail (__d, isIndex) k = isIndex (k + 1)
    let rec abstractInit (State (n, (__g, B), (IH, OH), d, O, H, F) as S)
      ((__g', B'), s') =
      if !Global.doubleCheck then TypeCheck.typeCheckCtx __g' else ();
      if !Global.doubleCheck
      then FunTypeCheck.isFor (__g', (F.forSub (F, s')))
      else ();
      S.State
        (n, (__g', B'), (IH, OH), d, (S.orderSub (O, s')),
          (map (function | (i, __F') -> (i, (F.forSub (__F', s')))) H),
          (F.forSub (F, s')))
    let rec abstractCont ((__d, T), abstract) ((__g, B), s) =
      abstract
        (((I.Decl (__g, (Whnf.normalizeDec (__d, s)))),
           (I.Decl (B, (S.normalizeTag (T, s))))), (I.dot1 s))
    let rec makeAddressInit (S) k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec occursInOrder =
      function
      | (n, Arg (__Us, Vt), k, sc) ->
          let __u' = Whnf.normalize __Us in
          if occursInExp (k, __u') then Some n else sc (n + 1)
      | (n, Lex (__Os), k, sc) -> occursInOrders (n, __Os, k, sc)
      | (n, Simul (__Os), k, sc) -> occursInOrders (n, __Os, k, sc)
    let rec occursInOrders =
      function
      | (n, nil, k, sc) -> sc n
      | (n, (O)::__Os, k, sc) ->
          occursInOrder
            (n, O, k, (function | n' -> occursInOrders (n', __Os, k, sc)))
    let rec inductionInit (O) k =
      occursInOrder (0, O, k, (function | n -> None))
    let rec inductionCont induction k = induction (k + 1)
    let rec expand' =
      function
      | (((I.Null, I.Null) as GB), isIndex, abstract, makeAddress, induction)
          ->
          (((function
             | (Gp, Bp) ->
                 ((Gp, Bp), (I.Shift (I.ctxLength Gp)), GB, false__))), nil)
      | (((Decl (__g, __d), Decl (B, (Lemma (Splits _ as K) as T))) as GB),
         isIndex, abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__g, B), (isIndexSucc (__d, isIndex)),
                (abstractCont ((__d, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __v) = __d in
          let rec sc' (Gp, Bp) =
            let ((__g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let x = I.newEVar (__g', (I.EClo (__v, s'))) in
            ((__g', B'), (I.Dot ((I.Exp x), s')),
              ((I.Decl (G0, __d)), (I.Decl (B0, T))), p') in
          let ops' =
            if (not (isIndex 1)) && ((S.splitDepth K) > 0)
            then
              let a = I.targetFam __v in
              (makeOperator
                 ((makeAddress 1), (split ((__d, T), sc, abstract)), K,
                   (I.ctxLength __g), (induction 1), (maxNumberCases (__v, a)),
                   (Subordinate.below (a, a))))
                :: ops
            else ops in
          (sc', ops')
      | ((Decl (__g, __d), Decl (B, (Lemma (S.RL) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__g, B), (isIndexSucc (__d, isIndex)),
                (abstractCont ((__d, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __v) = __d in
          let rec sc' (Gp, Bp) =
            let ((__g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let x = I.newEVar (__g', (I.EClo (__v, s'))) in
            ((__g', B'), (I.Dot ((I.Exp x), s')),
              ((I.Decl (G0, __d)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (__g, __d), Decl (B, (Lemma (S.RLdone) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__g, B), (isIndexSucc (__d, isIndex)),
                (abstractCont ((__d, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __v) = __d in
          let rec sc' (Gp, Bp) =
            let ((__g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let x = I.newEVar (__g', (I.EClo (__v, s'))) in
            ((__g', B'), (I.Dot ((I.Exp x), s')),
              ((I.Decl (G0, __d)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (__g, __d), Decl (B, (Parameter (Some _) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((__g, B), (isIndexSucc (__d, isIndex)), abstractErrorLeft,
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, __v) = __d in
          let rec sc' (Gp, Bp) =
            let ((__g', B'), s', (G0, B0), _) = sc (Gp, Bp) in
            (((I.Decl (__g', (Names.decName (__g', (I.decSub (__d, s')))))),
               (I.Decl (B', T))), (I.dot1 s'),
              ((I.Decl (G0, __d)), (I.Decl (B0, T))), true__) in
          (sc', ops)
    let rec expand (State (n, (G0, B0), _, _, O, _, _) as S0) =
      let _ = if !Global.doubleCheck then FunTypeCheck.isState S0 else () in
      let (_, ops) =
        expand'
          ((G0, B0), isIndexInit, (abstractInit S0), (makeAddressInit S0),
            (inductionInit O)) in
      ops
    let rec index (Operator ((S, index), Sl, { c = k })) = k
    let rec compare (Operator (_, _, I1), Operator (_, _, I2)) =
      H.compare (I1, I2)
    let rec isInActive = function | Active _ -> false__ | InActive -> true__
    let rec applicable (Operator (_, Sl, I)) =
      not (List.exists isInActive Sl)
    let rec apply (Operator (_, Sl, I)) =
      map
        (function
         | Active (S) ->
             (if !Global.doubleCheck then FunTypeCheck.isState S else (); S)
         | InActive -> raise (Error "Not applicable: leftover constraints"))
        Sl
    let rec menu
      (Operator ((State (n, (__g, B), (IH, OH), d, O, H, F), i), Sl, I) as Op)
      =
      let rec active =
        function
        | (nil, n) -> n
        | ((InActive)::__l, n) -> active (__l, n)
        | ((Active _)::__l, n) -> active (__l, (n + 1)) in
      let rec inactive =
        function
        | (nil, n) -> n
        | ((InActive)::__l, n) -> inactive (__l, (n + 1))
        | ((Active _)::__l, n) -> inactive (__l, n) in
      let rec casesToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let rec flagToString =
        function
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (__g, (I.ctxDec (__g, i)))) ^ " ")
          ^ (H.indexToString I))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ""
    (* recursive case *)
    (* non-recursive case *)
    (* aux (__g, B) = __l'

       Invariant:
       If   . |- __g ctx
       and  __g |- B tags
       then . |- __l' = GxB lfctx
    *)
    (* conv ((__g, s), (__g', s')) = B

       Invariant:
       B iff __g [s]  == __g' [s']
       Might migrate in to conv module  --cs
    *)
    (* createEVarSpineW (__g, (__v, s)) = ((__v', s') , S')

       Invariant:
       If   __g |- s : G1   and  G1 |- __v = Pi {V1 .. Vn}. W : __l
       and  G1, V1 .. Vn |- W atomic
       then __g |- s' : G2  and  G2 |- __v' : __l
       and  S = X1; ...; Xn; Nil
       and  __g |- W [1.2...n. s o ^n] = __v' [s']
       and  __g |- S : __v [s] >  __v' [s']
    *)
    (* s = id *)
    (* s = id *)
    (* createAtomConst (__g, c) = (__u', (__v', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. __v
       then . |- __u' = c @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createAtomBVar (__g, k) = (__u', (__v', s'))

       Invariant:
       If   __g |- k : Pi {V1 .. Vn}. __v
       then . |- __u' = k @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* someEVars (__g, G1, s) = s'

       Invariant:
       If   |- __g ctx
       and  __g |- s : __g'
       then __g |- s' : __g', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)
    (* ctxSub (__g, s) = __g'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- __g ctx
       then G2 |- __g' = __g[s] ctx
    *)
    (* constCases (__g, (__v, s), I, abstract, ops) = ops'

       Invariant:
       If   __g |- s : __g'  __g' |- __v : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
    (* paramCases (__g, (__v, s), k, abstract, ops) = ops'

       Invariant:
       If   __g |- s : __g'  __g' |- __v : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in __g
    *)
    (* abstract state *)
    (* lowerSplitDest (__g, k, (__v, s'), abstract) = ops'

       Invariant:
       If  G0, __g |- s' : G1  G1 |- __v: type
       and  k = |local parameters in __g|
       and  __g is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with __v[s']
            (it contains constant and parameter cases)
    *)
    (* split (x:__d, sc, B, abstract) = cases'

       Invariant :
       If   |- __g ctx
       and  __g |- B tags
       and  __g |- __d : __l
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (__g', B'), s', (__g, B), p'
                              (. |- __g' = Gp, __g'' ctx
                               __g'' contains only parameter declarations from __g
                               __g' |- B' tags
                               __g' |- s' : __g
                               and p' holds iff (__g', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : __g)
            to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)
    (* |- __g' = parameter blocks of __g  ctx*)
    (* __g' |- B' tags *)
    (* __g' |- s' : __g *)
    (* __g' |- __u' : __v[s'] *)
    (* __g' |- __u'.s' : __g, __v[s'] *)
    (* . |- t : G1 *)
    (* . |- G2 [t] ctx *)
    (* G2 [t] |- B2 tags *)
    (* . |- __g' ctx *)
    (* __g' |- B' tags *)
    (* __g' |- s : __g = G0 *)
    (* G0 |- B0 tags *)
    (* abstract' __u = S'

                   Invariant:
                   If   __g' |- __u' : __v[s']
                   then |- S' state *)
    (* __g' |- __u' : __v[s'] *)
    (* __g' |- U.s' : __g, __v *)
    (* . |- t : G1 *)
    (* . |- __g'' ctx *)
    (* __g'' |- B'' tags *)
    (* __g'' = G1'', G2', G2'' *)
    (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
    (* occursInExp (k, __u) = B,

       Invariant:
       If    __u in nf
       then  B iff k occurs in __u
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* abstractInit S ((__g', B'), s') = S'

       Invariant:
       If   |- S = (n, (__g, B), (IH, OH), d, O, H, F) state
       and  |- __g' ctx
       and  __g' |- B' tags
       and  __g' |- s' : __g
       then |- S' = (n, (__g', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
    (* abstractCont ((x:__v, T), abstract) = abstract'

       Invariant:
       If   |- __g ctx
       and  __g |- __v : type
       and  __g |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : __g, __d)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : __g)
                 to S'               (|- S' state)
    *)
    (* no other case should be possible by invariant *)
    (* expand' ((__g, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- __g ctx
       and  __g |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : __g)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (__g', B'), s', (__g, B), p'
                              (. |- __g' = Gp, __g'' ctx
                               __g'' contains only parameter declarations from __g
                               __g' |- B' tags
                               __g' |- s' : __g
                               and p' holds iff (__g', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (__g, B) as the result of sc, just take (__g, B)
    *)
    (* __g' |- x : __v[s'] *)
    (* __g' |- X.s' : __g, __d *)
    (* no case of (I.Decl (__g, __d), I.Decl (__g, S.Parameter None)) *)
    (* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)
    (* index (Op) = k

       Invariant:
       If   Op = (_, Sl)
       then k = |Sl|
    *)
    (* isInActive (F) = B

       Invariant:
       B holds iff F is inactive
    *)
    (* applicable (Op) = B'

       Invariant:
       If   Op = (_, Sl)
       then B' holds iff Sl does not contain inactive states
    *)
    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
    (* menu (Op) = s'

       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have
        been calculated from a named state)
    *)
    let expand = expand
    let menu = menu
    let applicable = applicable
    let apply = apply
    let index = index
    let compare = compare
  end ;;
