
module type MTPSPLITTING  =
  sig
    module StateSyn :
    ((STATESYN)(* Splitting : Version 1.3 *)(* Author: Carsten Schuermann *))
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator list
    val applicable : operator -> bool
    val apply : operator -> StateSyn.__State list
    val menu : operator -> string
    val index : operator -> int
    val compare : (operator * operator) -> order
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
                                   module Unify :
                                   ((UNIFY)(* Splitting : Version 1.3 *)
                                   (* Author: Carsten Schuermann *)
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
                                   (*! sharing Print.IntSyn = IntSyn !*))
                                 end) : MTPSPLITTING =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing Unify.IntSyn = IntSyn !*)
      (*! structure CSManager : CS_MANAGER !*)(*! sharing CSManager.IntSyn = IntSyn  !*))
    exception Error of string 
    type 'a flag =
      | Active of
      (('a)(* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *))
      
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
      | ((S, k), L, Splits n, g, I, m, true__) ->
          Operator
            ((S, k), L,
              { sd = n; ind = I; c = (List.length L); m; r = 1; p = (g + 1) })
      | ((S, k), L, Splits n, g, I, m, false__) ->
          Operator
            ((S, k), L,
              { sd = n; ind = I; c = (List.length L); m; r = 0; p = (g + 1) })
    let rec aux =
      function
      | (I.Null, I.Null) -> I.Null
      | (Decl (g, D), Decl (B, Lemma _)) -> I.Decl ((aux (g, B)), (F.Prim D))
      | ((Decl (_, D) as g), (Decl (_, Parameter (SOME l)) as B)) ->
          let LabelDec (name, _, G2) = F.labelLookup l in
          let (Psi', g') = aux' (g, B, (List.length G2)) in
          I.Decl (Psi', (F.Block (F.CtxBlock ((SOME l), g'))))
    let rec aux' =
      function
      | (g, B, 0) -> ((aux (g, B)), I.Null)
      | (Decl (g, D), Decl (B, Parameter (SOME _)), n) ->
          let (Psi', g') = aux' (g, B, (n - 1)) in (Psi', (I.Decl (g', D)))
    let rec conv (Gs, Gs') =
      let exception Conv  in
        let conv =
          function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (g, Dec (_, V)), s), (Decl (g', Dec (_, V')), s')) ->
              let (s1, s1') = conv ((g, s), (g', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((V, s1), (V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (Gs, Gs'); true__ with | Conv -> false__
    let rec createEVarSpine (g, Vs) = createEVarSpineW (g, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (g, ((Uni (I.Type), s) as Vs)) -> (I.Nil, Vs)
      | (g, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (g, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = I.newEVar (g, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (g, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (g, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (g, k) =
      let Dec (_, V) = I.ctxDec (g, k) in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let rec someEVars =
      function
      | (g, nil, s) -> s
      | (g, (Dec (_, V))::L, s) ->
          someEVars
            (g, L, (I.Dot ((I.Exp (I.newEVar (g, (I.EClo (V, s))))), s)))
    let rec maxNumberParams a =
      let maxNumberParams' n =
        if n < 0
        then 0
        else
          (let LabelDec (name, G1, G2) = F.labelLookup n in
           let m' =
             foldr
               (function
                | (Dec (_, V), m) -> if (I.targetFam V) = a then m + 1 else m)
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
    let rec maxNumberCases (V, a) =
      (+) ((+) (maxNumberParams a) maxNumberLocalParams (V, a))
        maxNumberConstCases a
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((D)::g, s) -> (::) (I.decSub (D, s)) ctxSub (g, (I.dot1 s))
    let rec createTags =
      function
      | (0, l) -> I.Null
      | (n, l) -> I.Decl ((createTags ((n - 1), l)), (S.Parameter (SOME l)))
    let rec createLemmaTags =
      function
      | I.Null -> I.Null
      | Decl (g, D) ->
          I.Decl
            ((createLemmaTags g), (S.Lemma (S.Splits (!MTPGlobal.maxSplit))))
    let rec constCases =
      function
      | (g, Vs, nil, abstract, ops) -> ops
      | (g, Vs, (Const c)::Sgn, abstract, ops) ->
          let (U, Vs') = createAtomConst (g, (I.Const c)) in
          constCases
            (g, Vs, Sgn, abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (g, Vs, Vs')
                         then (Active (abstract U)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec paramCases =
      function
      | (g, Vs, 0, abstract, ops) -> ops
      | (g, Vs, k, abstract, ops) ->
          let (U, Vs') = createAtomBVar (g, k) in
          paramCases
            (g, Vs, (k - 1), abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (g, Vs, Vs')
                         then (Active (abstract U)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec constAndParamCases ops0 (c, g, k, (V, s'), abstract) =
      constCases
        (g, (V, s'), (Index.lookup c), abstract,
          (paramCases (g, (V, s'), k, abstract, ops0)))
    let rec metaCases (d, ops0) (c, g, k, Vs, abstract) =
      let g = I.ctxLength g in
      let select =
        function
        | (0, ops) -> ops
        | (d', ops) ->
            let n = (g - d') + 1 in
            let Dec (_, V) = I.ctxDec (g, n) in
            let ops' =
              if (I.targetFam V) = c
              then
                let (U, Vs') = createAtomBVar (g, n) in
                CSManager.trail
                  (function
                   | () ->
                       (try
                          if Unify.unifiable (g, Vs, Vs')
                          then (Active (abstract U)) :: ops
                          else ops
                        with | Error _ -> InActive :: ops))
              else ops in
            select ((d' - 1), ops') in
      select (d, ops0)
    let rec lowerSplitDest =
      function
      | (g, k, ((Root (Const c, _) as V), s'), abstract, cases) ->
          cases (c, g, (I.ctxLength g), (V, s'), abstract)
      | (g, k, (Pi ((D, P), V), s'), abstract, cases) ->
          let D' = I.decSub (D, s') in
          lowerSplitDest
            ((I.Decl (g, D')), (k + 1), (V, (I.dot1 s')),
              (function | U -> abstract (I.Lam (D', U))), cases)
    let rec abstractErrorLeft ((g, B), s) =
      raise (MTPAbstract.Error "Cannot split left of parameters")
    let rec abstractErrorRight ((g, B), s) =
      raise (MTPAbstract.Error "Cannot split right of parameters")
    let rec split (((Dec (_, V) as D), T), sc, abstract) =
      let split' (n, cases) =
        if n < 0
        then
          let ((g', B'), s', (G0, B0), _) = sc (I.Null, I.Null) in
          let abstract' (U') =
            let ((g'', B''), s'') =
              MTPAbstract.abstractSub'
                ((g', B'), (I.Dot ((I.Exp U'), s')), (I.Decl (B0, T))) in
            let _ =
              if !Global.doubleCheck
              then
                let Psi'' = aux (g'', B'') in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                let Psi = aux ((I.Decl (G0, D)), (I.Decl (B0, T))) in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                FunTypeCheck.checkSub (Psi'', s'', Psi)
              else () in
            abstract ((g'', B''), s'') in
          lowerSplitDest
            (g', 0, (V, s'), abstract', (constAndParamCases cases))
        else
          (let LabelDec (name, G1, G2) = F.labelLookup n in
           let t = someEVars (I.Null, G1, I.id) in
           let B1 = createLemmaTags (F.listToCtx G1) in
           let G2t = ctxSub (G2, t) in
           let length = List.length G2 in
           let B2 = createTags (length, n) in
           let ((g', B'), s', (G0, B0), p) =
             sc ((Names.ctxName (F.listToCtx G2t)), B2) in
           let abstract' (U') =
             if p
             then
               raise (MTPAbstract.Error "Cannot split right of parameters")
             else
               (let ((g'', B''), s'') =
                  MTPAbstract.abstractSub
                    (t, B1, (g', B'), (I.Dot ((I.Exp U'), s')),
                      (I.Decl (B0, T))) in
                let _ =
                  if !Global.doubleCheck
                  then
                    let Psi'' = aux (g'', B'') in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                    let Psi = aux ((I.Decl (G0, D)), (I.Decl (B0, T))) in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                    FunTypeCheck.checkSub (Psi'', s'', Psi)
                  else () in
                abstract ((g'', B''), s'')) in
           let cases' =
             lowerSplitDest
               (g', 0, (V, s'), abstract', (metaCases (length, cases))) in
           split' ((n - 1), cases')) in
      split' (((F.labelSize ()) - 1), nil)
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, V)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), V))
      | (k, Root (C, S)) -> (occursInCon (k, C)) || (occursInSpine (k, S))
      | (k, Lam (D, V)) -> (occursInDec (k, D)) || (occursInExp ((k + 1), V))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, B) -> B || (occursInExp (k, (Whnf.normalize (U, I.id)))))
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
      | (k, App (U, S)) -> (occursInExp (k, U)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec isIndexInit k = false__
    let rec isIndexSucc (D, isIndex) k =
      (occursInDec (k, D)) || (isIndex (k + 1))
    let rec isIndexFail (D, isIndex) k = isIndex (k + 1)
    let rec abstractInit (State (n, (g, B), (IH, OH), d, O, H, F) as S)
      ((g', B'), s') =
      if !Global.doubleCheck then TypeCheck.typeCheckCtx g' else ();
      if !Global.doubleCheck
      then FunTypeCheck.isFor (g', (F.forSub (F, s')))
      else ();
      S.State
        (n, (g', B'), (IH, OH), d, (S.orderSub (O, s')),
          (map (function | (i, F') -> (i, (F.forSub (F', s')))) H),
          (F.forSub (F, s')))
    let rec abstractCont ((D, T), abstract) ((g, B), s) =
      abstract
        (((I.Decl (g, (Whnf.normalizeDec (D, s)))),
           (I.Decl (B, (S.normalizeTag (T, s))))), (I.dot1 s))
    let rec makeAddressInit (S) k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec occursInOrder =
      function
      | (n, Arg (Us, Vt), k, sc) ->
          let U' = Whnf.normalize Us in
          if occursInExp (k, U') then SOME n else sc (n + 1)
      | (n, Lex (Os), k, sc) -> occursInOrders (n, Os, k, sc)
      | (n, Simul (Os), k, sc) -> occursInOrders (n, Os, k, sc)
    let rec occursInOrders =
      function
      | (n, nil, k, sc) -> sc n
      | (n, (O)::Os, k, sc) ->
          occursInOrder
            (n, O, k, (function | n' -> occursInOrders (n', Os, k, sc)))
    let rec inductionInit (O) k =
      occursInOrder (0, O, k, (function | n -> NONE))
    let rec inductionCont induction k = induction (k + 1)
    let rec expand' =
      function
      | (((I.Null, I.Null) as GB), isIndex, abstract, makeAddress, induction)
          ->
          (((function
             | (Gp, Bp) ->
                 ((Gp, Bp), (I.Shift (I.ctxLength Gp)), GB, false__))), nil)
      | (((Decl (g, D), Decl (B, (Lemma (Splits _ as K) as T))) as GB),
         isIndex, abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((g, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let sc' (Gp, Bp) =
            let ((g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (g', (I.EClo (V, s'))) in
            ((g', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          let ops' =
            if (not (isIndex 1)) && ((S.splitDepth K) > 0)
            then
              let a = I.targetFam V in
              (makeOperator
                 ((makeAddress 1), (split ((D, T), sc, abstract)), K,
                   (I.ctxLength g), (induction 1), (maxNumberCases (V, a)),
                   (Subordinate.below (a, a))))
                :: ops
            else ops in
          (sc', ops')
      | ((Decl (g, D), Decl (B, (Lemma (S.RL) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((g, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let sc' (Gp, Bp) =
            let ((g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (g', (I.EClo (V, s'))) in
            ((g', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (g, D), Decl (B, (Lemma (S.RLdone) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((g, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let sc' (Gp, Bp) =
            let ((g', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (g', (I.EClo (V, s'))) in
            ((g', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (g, D), Decl (B, (Parameter (SOME _) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((g, B), (isIndexSucc (D, isIndex)), abstractErrorLeft,
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let sc' (Gp, Bp) =
            let ((g', B'), s', (G0, B0), _) = sc (Gp, Bp) in
            (((I.Decl (g', (Names.decName (g', (I.decSub (D, s')))))),
               (I.Decl (B', T))), (I.dot1 s'),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), true__) in
          (sc', ops)
    let rec expand (State (n, (G0, B0), _, _, O, _, _) as s0) =
      let _ = if !Global.doubleCheck then FunTypeCheck.isState s0 else () in
      let (_, ops) =
        expand'
          ((G0, B0), isIndexInit, (abstractInit s0), (makeAddressInit s0),
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
      (Operator ((State (n, (g, B), (IH, OH), d, O, H, F), i), Sl, I) as Op)
      =
      let active =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> active (L, n)
        | ((Active _)::L, n) -> active (L, (n + 1)) in
      let inactive =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> inactive (L, (n + 1))
        | ((Active _)::L, n) -> inactive (L, n) in
      let casesToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let flagToString =
        function
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (g, (I.ctxDec (g, i)))) ^ " ")
          ^ (H.indexToString I))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ""
    let ((expand)(* recursive case *)(* non-recursive case *)
      (* aux (g, B) = L'

       Invariant:
       If   . |- g ctx
       and  g |- B tags
       then . |- L' = GxB lfctx
    *)
      (* conv ((g, s), (g', s')) = B

       Invariant:
       B iff g [s]  == g' [s']
       Might migrate in to conv module  --cs
    *)
      (* createEVarSpineW (g, (V, s)) = ((V', s') , S')

       Invariant:
       If   g |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then g |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  g |- W [1.2...n. s o ^n] = V' [s']
       and  g |- S : V [s] >  V' [s']
    *)
      (* s = id *)(* s = id *)(* createAtomConst (g, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* createAtomBVar (g, k) = (U', (V', s'))

       Invariant:
       If   g |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* someEVars (g, G1, s) = s'

       Invariant:
       If   |- g ctx
       and  g |- s : g'
       then g |- s' : g', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)
      (* ctxSub (g, s) = g'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- g ctx
       then G2 |- g' = g[s] ctx
    *)
      (* constCases (g, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   g |- s : g'  g' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
      (* paramCases (g, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   g |- s : g'  g' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in g
    *)
      (* abstract state *)(* lowerSplitDest (g, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, g |- s' : G1  G1 |- V: type
       and  k = |local parameters in g|
       and  g is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)
      (* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- g ctx
       and  g |- B tags
       and  g |- D : L
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (g', B'), s', (g, B), p'
                              (. |- g' = Gp, g'' ctx
                               g'' contains only parameter declarations from g
                               g' |- B' tags
                               g' |- s' : g
                               and p' holds iff (g', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : g)
            to S'            (|- S' state)

       then cases' = (s1, ... Sn) are cases of the split
    *)
      (* |- g' = parameter blocks of g  ctx*)(* g' |- B' tags *)
      (* g' |- s' : g *)(* g' |- U' : V[s'] *)(* g' |- U'.s' : g, V[s'] *)
      (* . |- t : G1 *)(* . |- G2 [t] ctx *)(* G2 [t] |- B2 tags *)
      (* . |- g' ctx *)(* g' |- B' tags *)
      (* g' |- s : g = G0 *)(* G0 |- B0 tags *)
      (* abstract' U = S'

                   Invariant:
                   If   g' |- U' : V[s']
                   then |- S' state *)
      (* g' |- U' : V[s'] *)(* g' |- U.s' : g, V *)
      (* . |- t : G1 *)(* . |- g'' ctx *)
      (* g'' |- B'' tags *)(* g'' = G1'', G2', G2'' *)
      (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
      (* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
      (* no case for Redex, EVar, EClo *)(* no case for FVar *)
      (* no case for SClo *)(* abstractInit S ((g', B'), s') = S'

       Invariant:
       If   |- S = (n, (g, B), (IH, OH), d, O, H, F) state
       and  |- g' ctx
       and  g' |- B' tags
       and  g' |- s' : g
       then |- S' = (n, (g', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
      (* abstractCont ((x:V, T), abstract) = abstract'

       Invariant:
       If   |- g ctx
       and  g |- V : type
       and  g |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : g, D)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : g)
                 to S'               (|- S' state)
    *)
      (* no other case should be possible by invariant *)
      (* expand' ((g, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- g ctx
       and  g |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : g)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (g', B'), s', (g, B), p'
                              (. |- g' = Gp, g'' ctx
                               g'' contains only parameter declarations from g
                               g' |- B' tags
                               g' |- s' : g
                               and p' holds iff (g', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (g, B) as the result of sc, just take (g, B)
    *)
      (* g' |- X : V[s'] *)(* g' |- X.s' : g, D *)
      (* no case of (I.Decl (g, D), I.Decl (g, S.Parameter NONE)) *)
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
    *))
      = expand
    let menu = menu
    let applicable = applicable
    let apply = apply
    let index = index
    let compare = compare
  end ;;
