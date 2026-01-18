
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
      | (Decl (G, D), Decl (B, Lemma _)) -> I.Decl ((aux (G, B)), (F.Prim D))
      | ((Decl (_, D) as G), (Decl (_, Parameter (SOME l)) as B)) ->
          let LabelDec (name, _, G2) = F.labelLookup l in
          let (Psi', G') = aux' (G, B, (List.length G2)) in
          I.Decl (Psi', (F.Block (F.CtxBlock ((SOME l), G'))))
    let rec aux' =
      function
      | (G, B, 0) -> ((aux (G, B)), I.Null)
      | (Decl (G, D), Decl (B, Parameter (SOME _)), n) ->
          let (Psi', G') = aux' (G, B, (n - 1)) in (Psi', (I.Decl (G', D)))
    let rec conv (Gs, Gs') =
      let exception Conv  in
        let rec conv =
          function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (G, Dec (_, V)), s), (Decl (G', Dec (_, V')), s')) ->
              let (s1, s1') = conv ((G, s), (G', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((V, s1), (V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (Gs, Gs'); true__ with | Conv -> false__
    let rec createEVarSpine (G, Vs) = createEVarSpineW (G, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (G, ((Uni (I.Type), s) as Vs)) -> (I.Nil, Vs)
      | (G, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (G, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = I.newEVar (G, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (G, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (G, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (G, k) =
      let Dec (_, V) = I.ctxDec (G, k) in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let rec someEVars =
      function
      | (G, nil, s) -> s
      | (G, (Dec (_, V))::L, s) ->
          someEVars
            (G, L, (I.Dot ((I.Exp (I.newEVar (G, (I.EClo (V, s))))), s)))
    let rec maxNumberParams a =
      let rec maxNumberParams' n =
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
      | ((D)::G, s) -> (::) (I.decSub (D, s)) ctxSub (G, (I.dot1 s))
    let rec createTags =
      function
      | (0, l) -> I.Null
      | (n, l) -> I.Decl ((createTags ((n - 1), l)), (S.Parameter (SOME l)))
    let rec createLemmaTags =
      function
      | I.Null -> I.Null
      | Decl (G, D) ->
          I.Decl
            ((createLemmaTags G), (S.Lemma (S.Splits (!MTPGlobal.maxSplit))))
    let rec constCases =
      function
      | (G, Vs, nil, abstract, ops) -> ops
      | (G, Vs, (Const c)::Sgn, abstract, ops) ->
          let (U, Vs') = createAtomConst (G, (I.Const c)) in
          constCases
            (G, Vs, Sgn, abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (G, Vs, Vs')
                         then (Active (abstract U)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec paramCases =
      function
      | (G, Vs, 0, abstract, ops) -> ops
      | (G, Vs, k, abstract, ops) ->
          let (U, Vs') = createAtomBVar (G, k) in
          paramCases
            (G, Vs, (k - 1), abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (G, Vs, Vs')
                         then (Active (abstract U)) :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec constAndParamCases ops0 (c, G, k, (V, s'), abstract) =
      constCases
        (G, (V, s'), (Index.lookup c), abstract,
          (paramCases (G, (V, s'), k, abstract, ops0)))
    let rec metaCases (d, ops0) (c, G, k, Vs, abstract) =
      let g = I.ctxLength G in
      let rec select =
        function
        | (0, ops) -> ops
        | (d', ops) ->
            let n = (g - d') + 1 in
            let Dec (_, V) = I.ctxDec (G, n) in
            let ops' =
              if (I.targetFam V) = c
              then
                let (U, Vs') = createAtomBVar (G, n) in
                CSManager.trail
                  (function
                   | () ->
                       (try
                          if Unify.unifiable (G, Vs, Vs')
                          then (Active (abstract U)) :: ops
                          else ops
                        with | Error _ -> InActive :: ops))
              else ops in
            select ((d' - 1), ops') in
      select (d, ops0)
    let rec lowerSplitDest =
      function
      | (G, k, ((Root (Const c, _) as V), s'), abstract, cases) ->
          cases (c, G, (I.ctxLength G), (V, s'), abstract)
      | (G, k, (Pi ((D, P), V), s'), abstract, cases) ->
          let D' = I.decSub (D, s') in
          lowerSplitDest
            ((I.Decl (G, D')), (k + 1), (V, (I.dot1 s')),
              (function | U -> abstract (I.Lam (D', U))), cases)
    let rec abstractErrorLeft ((G, B), s) =
      raise (MTPAbstract.Error "Cannot split left of parameters")
    let rec abstractErrorRight ((G, B), s) =
      raise (MTPAbstract.Error "Cannot split right of parameters")
    let rec split (((Dec (_, V) as D), T), sc, abstract) =
      let rec split' (n, cases) =
        if n < 0
        then
          let ((G', B'), s', (G0, B0), _) = sc (I.Null, I.Null) in
          let rec abstract' (U') =
            let ((G'', B''), s'') =
              MTPAbstract.abstractSub'
                ((G', B'), (I.Dot ((I.Exp U'), s')), (I.Decl (B0, T))) in
            let _ =
              if !Global.doubleCheck
              then
                let Psi'' = aux (G'', B'') in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                let Psi = aux ((I.Decl (G0, D)), (I.Decl (B0, T))) in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                FunTypeCheck.checkSub (Psi'', s'', Psi)
              else () in
            abstract ((G'', B''), s'') in
          lowerSplitDest
            (G', 0, (V, s'), abstract', (constAndParamCases cases))
        else
          (let LabelDec (name, G1, G2) = F.labelLookup n in
           let t = someEVars (I.Null, G1, I.id) in
           let B1 = createLemmaTags (F.listToCtx G1) in
           let G2t = ctxSub (G2, t) in
           let length = List.length G2 in
           let B2 = createTags (length, n) in
           let ((G', B'), s', (G0, B0), p) =
             sc ((Names.ctxName (F.listToCtx G2t)), B2) in
           let rec abstract' (U') =
             if p
             then
               raise (MTPAbstract.Error "Cannot split right of parameters")
             else
               (let ((G'', B''), s'') =
                  MTPAbstract.abstractSub
                    (t, B1, (G', B'), (I.Dot ((I.Exp U'), s')),
                      (I.Decl (B0, T))) in
                let _ =
                  if !Global.doubleCheck
                  then
                    let Psi'' = aux (G'', B'') in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                    let Psi = aux ((I.Decl (G0, D)), (I.Decl (B0, T))) in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                    FunTypeCheck.checkSub (Psi'', s'', Psi)
                  else () in
                abstract ((G'', B''), s'')) in
           let cases' =
             lowerSplitDest
               (G', 0, (V, s'), abstract', (metaCases (length, cases))) in
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
    let rec abstractInit (State (n, (G, B), (IH, OH), d, O, H, F) as S)
      ((G', B'), s') =
      if !Global.doubleCheck then TypeCheck.typeCheckCtx G' else ();
      if !Global.doubleCheck
      then FunTypeCheck.isFor (G', (F.forSub (F, s')))
      else ();
      S.State
        (n, (G', B'), (IH, OH), d, (S.orderSub (O, s')),
          (map (function | (i, F') -> (i, (F.forSub (F', s')))) H),
          (F.forSub (F, s')))
    let rec abstractCont ((D, T), abstract) ((G, B), s) =
      abstract
        (((I.Decl (G, (Whnf.normalizeDec (D, s)))),
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
      | (((Decl (G, D), Decl (B, (Lemma (Splits _ as K) as T))) as GB),
         isIndex, abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((G, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let rec sc' (Gp, Bp) =
            let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (G', (I.EClo (V, s'))) in
            ((G', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          let ops' =
            if (not (isIndex 1)) && ((S.splitDepth K) > 0)
            then
              let a = I.targetFam V in
              (makeOperator
                 ((makeAddress 1), (split ((D, T), sc, abstract)), K,
                   (I.ctxLength G), (induction 1), (maxNumberCases (V, a)),
                   (Subordinate.below (a, a))))
                :: ops
            else ops in
          (sc', ops')
      | ((Decl (G, D), Decl (B, (Lemma (S.RL) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((G, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let rec sc' (Gp, Bp) =
            let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (G', (I.EClo (V, s'))) in
            ((G', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (G, D), Decl (B, (Lemma (S.RLdone) as T))), isIndex, abstract,
         makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((G, B), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, T), abstract)),
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let rec sc' (Gp, Bp) =
            let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp) in
            let X = I.newEVar (G', (I.EClo (V, s'))) in
            ((G', B'), (I.Dot ((I.Exp X), s')),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), p') in
          (sc', ops)
      | ((Decl (G, D), Decl (B, (Parameter (SOME _) as T))), isIndex,
         abstract, makeAddress, induction) ->
          let (sc, ops) =
            expand'
              ((G, B), (isIndexSucc (D, isIndex)), abstractErrorLeft,
                (makeAddressCont makeAddress), (inductionCont induction)) in
          let Dec (xOpt, V) = D in
          let rec sc' (Gp, Bp) =
            let ((G', B'), s', (G0, B0), _) = sc (Gp, Bp) in
            (((I.Decl (G', (Names.decName (G', (I.decSub (D, s')))))),
               (I.Decl (B', T))), (I.dot1 s'),
              ((I.Decl (G0, D)), (I.Decl (B0, T))), true__) in
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
      (Operator ((State (n, (G, B), (IH, OH), d, O, H, F), i), Sl, I) as Op)
      =
      let rec active =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> active (L, n)
        | ((Active _)::L, n) -> active (L, (n + 1)) in
      let rec inactive =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> inactive (L, (n + 1))
        | ((Active _)::L, n) -> inactive (L, n) in
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
      (((((^) "Splitting : " Print.decToString (G, (I.ctxDec (G, i)))) ^ " ")
          ^ (H.indexToString I))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ""
    (* recursive case *)
    (* non-recursive case *)
    (* aux (G, B) = L'

       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)
    (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
    (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    (* s = id *)
    (* s = id *)
    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    (* someEVars (G, G1, s) = s'

       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)
    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
    (* constCases (G, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
    (* paramCases (G, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in G
    *)
    (* abstract state *)
    (* lowerSplitDest (G, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)
    (* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- G ctx
       and  G |- B tags
       and  G |- D : L
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)
    (* |- G' = parameter blocks of G  ctx*)
    (* G' |- B' tags *)
    (* G' |- s' : G *)
    (* G' |- U' : V[s'] *)
    (* G' |- U'.s' : G, V[s'] *)
    (* . |- t : G1 *)
    (* . |- G2 [t] ctx *)
    (* G2 [t] |- B2 tags *)
    (* . |- G' ctx *)
    (* G' |- B' tags *)
    (* G' |- s : G = G0 *)
    (* G0 |- B0 tags *)
    (* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *)
    (* G' |- U' : V[s'] *)
    (* G' |- U.s' : G, V *)
    (* . |- t : G1 *)
    (* . |- G'' ctx *)
    (* G'' |- B'' tags *)
    (* G'' = G1'', G2', G2'' *)
    (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
    (* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* abstractInit S ((G', B'), s') = S'

       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
    (* abstractCont ((x:V, T), abstract) = abstract'

       Invariant:
       If   |- G ctx
       and  G |- V : type
       and  G |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G, D)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : G)
                 to S'               (|- S' state)
    *)
    (* no other case should be possible by invariant *)
    (* expand' ((G, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (G, B) as the result of sc, just take (G, B)
    *)
    (* G' |- X : V[s'] *)
    (* G' |- X.s' : G, D *)
    (* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)
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
