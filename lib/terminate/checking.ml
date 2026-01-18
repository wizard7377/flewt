
(* Reasoning about orders *)
(* Author: Brigitte Pientka *)
module type CHECKING  =
  sig
    (*! structure IntSyn : INTSYN !*)
    module Order : ORDER
    (*! structure Paths : PATHS !*)
    (* If Q marks all parameters in a context G we write   G : Q  *)
    type __Quantifier =
      | All 
      | Exist 
      | And of Paths.occ 
    (*     | And                     *)
    type 'a __Predicate =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.__Dec * 'a __Predicate) 
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.__Order
    (* reduction predicate context (unordered) *)
    type nonrec rctx = order __Predicate list
    (* mixed-prefix context *)
    type nonrec qctx = __Quantifier IntSyn.__Ctx
    val shiftRCtx : rctx -> (IntSyn.__Sub -> IntSyn.__Sub) -> rctx
    val shiftPred :
      order __Predicate ->
        (IntSyn.__Sub -> IntSyn.__Sub) -> order __Predicate
    val deduce : (IntSyn.dctx * qctx * rctx * order __Predicate) -> bool
  end;;




(* Reasoning about structural orders *)
(* Author: Brigitte Pientka *)
(* for reasoning about orders see [Pientka IJCAR'01] *)
module Checking(Checking:sig
                           module Global : GLOBAL
                           module Whnf : WHNF
                           module Conv : CONV
                           module Unify : UNIFY
                           module Names : NAMES
                           module Index : INDEX
                           module Subordinate : SUBORDINATE
                           module Formatter : FORMATTER
                           module Print : PRINT
                           module Order : ORDER
                           (*! structure IntSyn' : INTSYN !*)
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Conv.IntSyn = IntSyn' !*)
                           (*! sharing Unify.IntSyn = IntSyn' !*)
                           (*! sharing Names.IntSyn = IntSyn' !*)
                           (*! sharing Index.IntSyn = IntSyn' !*)
                           (*! sharing Subordinate.IntSyn = IntSyn' !*)
                           (*! sharing Print.IntSyn = IntSyn' !*)
                           (*! sharing Order.IntSyn = IntSyn' !*)
                           (*! structure Paths  : PATHS !*)
                           module Origins : ORIGINS
                         end) : CHECKING =
  struct
    (*! sharing Origins.Paths = Paths !*)
    (*! sharing Origins.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module Order = Order
    (*! structure Paths = Paths !*)
    type __Quantifier =
      | All 
      | Exist 
      | And of Paths.occ 
    (*     | And                     *)
    (* If Q marks all parameters in a context G we write   G : Q               *)
    type 'a __Predicate =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.__Dec * 'a __Predicate) 
    (* Abbreviation *)
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.__Order
    (* reduction order assumptions (unordered) *)
    type nonrec rctx = order __Predicate list
    (* mixed prefix order contex *)
    type nonrec qctx = __Quantifier IntSyn.__Ctx
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    let rec atomicPredToString =
      function
      | (G, Less ((Us, _), (Us', _))) ->
          (^) ((Print.expToString (G, (I.EClo Us))) ^ " < ")
            Print.expToString (G, (I.EClo Us'))
      | (G, Leq ((Us, _), (Us', _))) ->
          (^) ((Print.expToString (G, (I.EClo Us))) ^ " <= ")
            Print.expToString (G, (I.EClo Us'))
      | (G, Eq ((Us, _), (Us', _))) ->
          (^) ((Print.expToString (G, (I.EClo Us))) ^ " = ")
            Print.expToString (G, (I.EClo Us'))
    let rec atomicRCtxToString =
      function
      | (G, nil) -> " "
      | (G, (O)::nil) -> atomicPredToString (G, O)
      | (G, (O)::D') ->
          (^) ((atomicRCtxToString (G, D')) ^ ", ") atomicPredToString (G, O)
    let rec shiftO arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Arg ((U, us), (V, vs)), f) -> R.Arg ((U, (f us)), (V, (f vs)))
      | (Lex (L), f) -> R.Lex (map (function | O -> shiftO O f) L)
      | (Simul (L), f) -> R.Simul (map (function | O -> shiftO O f) L)
    let rec shiftP arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Less (O1, O2), f) -> Less ((shiftO O1 f), (shiftO O2 f))
      | (Leq (O1, O2), f) -> Leq ((shiftO O1 f), (shiftO O2 f))
      | (Eq (O1, O2), f) -> Eq ((shiftO O1 f), (shiftO O2 f))
      | (Pi ((Dec (X, V) as D), P), f) -> Pi (D, (shiftP P f))
    let rec shiftRCtx (Rl) f = map (function | p -> shiftP p f) Rl
    let rec shiftArg arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Less (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f) ->
          Less (((U1, (f s1)), (V1, (f s1'))), ((U2, (f s2)), (V2, (f s2'))))
      | (Leq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f) ->
          Leq (((U1, (f s1)), (V1, (f s1'))), ((U2, (f s2)), (V2, (f s2'))))
      | (Eq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f) ->
          Eq (((U1, (f s1)), (V1, (f s1'))), ((U2, (f s2)), (V2, (f s2'))))
    let rec shiftACtx (Rl) f = map (function | p -> shiftArg p f) Rl
    let rec fmtOrder (G, O) =
      let rec fmtOrder' =
        function
        | Arg (((U, s) as Us), ((V, s') as Vs)) ->
            F.Hbox
              [F.String "("; Print.formatExp (G, (I.EClo Us)); F.String ")"]
        | Lex (L) ->
            F.Hbox
              [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders L); F.String "}"]
        | Simul (L) ->
            F.Hbox
              [F.String "["; F.HOVbox0 1 0 1 (fmtOrders L); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (O)::[] -> (fmtOrder' O) :: []
        | (O)::L -> (::) ((fmtOrder' O) :: F.Break) fmtOrders L in
      fmtOrder' O
    let rec fmtComparison (G, O, comp, O') =
      F.HOVbox0 1 0 1
        [fmtOrder (G, O); F.Break; F.String comp; F.Break; fmtOrder (G, O')]
    let rec fmtPredicate' =
      function
      | (G, Less (O, O')) -> fmtComparison (G, O, "<", O')
      | (G, Leq (O, O')) -> fmtComparison (G, O, "<=", O')
      | (G, Eq (O, O')) -> fmtComparison (G, O, "=", O')
      | (G, Pi (D, P)) ->
          F.Hbox [F.String "Pi "; fmtPredicate' ((I.Decl (G, D)), P)]
    let rec fmtPredicate (G, P) = fmtPredicate' ((Names.ctxName G), P)
    let rec fmtRGCtx' =
      function
      | (G, nil) -> ""
      | (G, (P)::[]) -> F.makestring_fmt (fmtPredicate' (G, P))
      | (G, (P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate' (G, P))) ^ " ,") fmtRGCtx'
            (G, Rl)
    let rec fmtRGCtx (G, Rl) = fmtRGCtx' ((Names.ctxName G), Rl)
    let rec init () = true__
    let rec eqCid (c, c') = c = c'
    let rec conv ((Us, Vs), (Us', Vs')) =
      (Conv.conv (Vs, Vs')) && (Conv.conv (Us, Us'))
    let rec isUniversal =
      function | All -> true__ | Exist -> false__ | Exist' -> false__
    let rec isExistential =
      function | All -> false__ | Exist -> true__ | Exist' -> true__
    let rec isParameter (Q, X) = isParameterW (Q, (Whnf.whnf (X, I.id)))
    let rec isParameterW (Q, Us) =
      try isUniversal (I.ctxLookup (Q, (Whnf.etaContract (I.EClo Us))))
      with | Whnf.Eta -> isFreeEVar Us
    let rec isFreeEVar =
      function
      | (EVar (_, _, _, ref []), _) -> true__
      | (Lam (D, U), s) -> isFreeEVar (Whnf.whnf (U, (I.dot1 s)))
      | _ -> false__
    let rec isAtomic (GQ, Us) = isAtomicW (GQ, (Whnf.whnf Us))
    let rec isAtomicW =
      function
      | (GQ, ((Root (Const c, S) as X), s)) -> isAtomicS (GQ, (S, s))
      | (GQ, ((Root (Def c, S) as X), s)) -> isAtomicS (GQ, (S, s))
      | (((G, Q) as GQ), ((Root (BVar n, S) as X), s)) ->
          (isExistential (I.ctxLookup (Q, n))) || (isAtomicS (GQ, (S, s)))
      | (GQ, _) -> false__
    let rec isAtomicS =
      function
      | (GQ, (I.Nil, _)) -> true__
      | (GQ, (SClo (S, s'), s'')) -> isAtomicS (GQ, (S, (I.comp (s', s''))))
      | (GQ, (App (U', S'), s1')) -> false__
    let rec eq (G, (Us, Vs), (Us', Vs')) =
      (Unify.unifiable (G, Vs, Vs')) && (Unify.unifiable (G, Us, Us'))
    let rec lookupEq =
      function
      | (GQ, nil, UsVs, UsVs', sc) -> false__
      | (GQ, (Less (_, _))::D, UsVs, UsVs', sc) ->
          lookupEq (GQ, D, UsVs, UsVs', sc)
      | (((G, Q) as GQ), (Eq (UsVs1, UsVs1'))::D, UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (G, UsVs1, UsVs)) &&
                    ((eq (G, UsVs1', UsVs')) && (sc ()))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (G, UsVs1, UsVs')) &&
                       ((eq (G, UsVs1', UsVs)) && (sc ()))))
               || (lookupEq (GQ, D, UsVs, UsVs', sc)))
    let rec lookupLt =
      function
      | (GQ, nil, UsVs, UsVs', sc) -> false__
      | (GQ, (Eq (_, _))::D, UsVs, UsVs', sc) ->
          lookupLt (GQ, D, UsVs, UsVs', sc)
      | (((G, Q) as GQ), (Less (UsVs1, UsVs1'))::D, UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (G, UsVs1, UsVs)) &&
                    ((eq (G, UsVs1', UsVs')) && (sc ()))))
            || (lookupLt (GQ, D, UsVs, UsVs', sc))
    let rec eqAtomic =
      function
      | (((G, Q) as GQ), nil, D', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function | () -> (eq (G, UsVs, UsVs')) && (sc ())))
            || (lookupEq (GQ, D', UsVs, UsVs', sc))
      | (((G, Q) as GQ), D, D', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function | () -> (eq (G, UsVs, UsVs')) && (sc ())))
            ||
            ((lookupEq (GQ, D, UsVs, UsVs', sc)) ||
               ((lookupEq (GQ, D', UsVs, UsVs', sc)) ||
                  (transEq (GQ, D, D', UsVs, UsVs', sc))))
    let rec transEq =
      function
      | (((G, Q) as GQ), nil, D, UsVs, UsVs', sc) -> false__
      | (((G, Q) as GQ), (Eq (UsVs1, UsVs1'))::D, D', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (G, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (eqAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (G, UsVs1, UsVs')) &&
                       ((sc ()) &&
                          (eqAtomicR (GQ, (D @ D'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transEq
                  (GQ, D, ((Eq (UsVs1, UsVs1')) :: D'), UsVs, UsVs', sc)))
      | (((G, Q) as GQ), (Less (UsVs1, UsVs1'))::D, D', UsVs, UsVs', sc) ->
          transEq (GQ, D, D', UsVs, UsVs', sc)
    let rec ltAtomic =
      function
      | (((G, Q) as GQ), nil, D', UsVs, UsVs', sc) ->
          lookupLt (GQ, D', UsVs, UsVs', sc)
      | (((G, Q) as GQ), D, D', UsVs, UsVs', sc) ->
          (lookupLt (GQ, D, UsVs, UsVs', sc)) ||
            ((lookupLt (GQ, D', UsVs, UsVs', sc)) ||
               (transLt (GQ, D, D', UsVs, UsVs', sc)))
    let rec transLt =
      function
      | (((G, Q) as GQ), nil, D, UsVs, UsVs', sc) -> false__
      | (((G, Q) as GQ), (Eq (UsVs1, UsVs1'))::D, D', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (G, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (ltAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (G, UsVs1, UsVs')) &&
                       ((sc ()) &&
                          (ltAtomicR (GQ, (D @ D'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transLt
                  (GQ, D, ((Eq (UsVs1, UsVs1')) :: D'), UsVs, UsVs', sc)))
      | (((G, Q) as GQ), (Less (UsVs1, UsVs1'))::D, D', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (G, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (eqAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (G, UsVs1', UsVs')) &&
                       ((sc ()) &&
                          (ltAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic)))))
               ||
               (transLt
                  (GQ, D, ((Less (UsVs1, UsVs1')) :: D'), UsVs, UsVs', sc)))
    let rec atomic =
      function
      | (GQ, D, D', Eq (UsVs, UsVs'), sc) ->
          eqAtomic (GQ, D, D', UsVs, UsVs', sc)
      | (GQ, D, D', Less (UsVs, UsVs'), sc) ->
          ltAtomic (GQ, D, D', UsVs, UsVs', sc)
    let rec leftInstantiate =
      function
      | (((G, Q) as GQ), nil, D', P, sc) ->
          if atomic (GQ, D', nil, P, sc)
          then
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) " Proved: " atomicRCtxToString (G, D')) ^
                          " ---> ")
                     atomicPredToString (G, P))
                    ^ "\n")
             else ();
             true__)
          else false__
      | (GQ, (Less (UsVs, UsVs'))::D, D', P, sc) ->
          ltInstL (GQ, D, D', UsVs, UsVs', P, sc)
      | (GQ, (Leq (UsVs, UsVs'))::D, D', P, sc) ->
          leInstL (GQ, D, D', UsVs, UsVs', P, sc)
      | (GQ, (Eq (UsVs, UsVs'))::D, D', P, sc) ->
          eqInstL (GQ, D, D', UsVs, UsVs', P, sc)
    let rec ltInstL (GQ, D, D', UsVs, UsVs', P', sc) =
      ltInstLW (GQ, D, D', (Whnf.whnfEta UsVs), UsVs', P', sc)
    let rec ltInstLW =
      function
      | (((G, Q) as GQ), D, D',
         ((Lam ((Dec (_, V1) as Dec), U), s1),
          (Pi ((Dec (_, V2), _), V), s2)),
         ((U', s1'), (V', s2')), P', sc) ->
          if Subordinate.equiv ((I.targetFam V'), (I.targetFam V1))
          then
            let X = I.newEVar (G, (I.EClo (V1, s1))) in
            let sc' = function | () -> (isParameter (Q, X)) && (sc ()) in
            ltInstL
              ((G, Q), D, D',
                ((U, (I.Dot ((I.Exp X), s1))), (V, (I.Dot ((I.Exp X), s2)))),
                ((U', s1'), (V', s2')), P', sc')
          else
            if Subordinate.below ((I.targetFam V1), (I.targetFam V'))
            then
              (let X = I.newEVar (G, (I.EClo (V1, s1))) in
               ltInstL
                 ((G, Q), D, D',
                   ((U, (I.Dot ((I.Exp X), s1))),
                     (V, (I.Dot ((I.Exp X), s2)))), ((U', s1'), (V', s2')),
                   P', sc))
            else false__
      | (GQ, D, D', UsVs, UsVs', P', sc) ->
          leftInstantiate (GQ, D, ((Less (UsVs, UsVs')) :: D'), P', sc)
    let rec leInstL (GQ, D, D', UsVs, UsVs', P', sc) =
      leInstLW (GQ, D, D', (Whnf.whnfEta UsVs), UsVs', P', sc)
    let rec leInstLW =
      function
      | (((G, Q) as GQ), D, D',
         ((Lam (Dec (_, V1), U), s1), (Pi ((Dec (_, V2), _), V), s2)),
         ((U', s1'), (V', s2')), P', sc) ->
          if Subordinate.equiv ((I.targetFam V'), (I.targetFam V1))
          then
            let X = I.newEVar (G, (I.EClo (V1, s1))) in
            let sc' = function | () -> (isParameter (Q, X)) && (sc ()) in
            leInstL
              ((G, Q), D, D',
                ((U, (I.Dot ((I.Exp X), s1))), (V, (I.Dot ((I.Exp X), s2)))),
                ((U', s1'), (V', s2')), P', sc')
          else
            if Subordinate.below ((I.targetFam V1), (I.targetFam V'))
            then
              (let X = I.newEVar (G, (I.EClo (V1, s1))) in
               leInstL
                 ((G, Q), D, D',
                   ((U, (I.Dot ((I.Exp X), s1))),
                     (V, (I.Dot ((I.Exp X), s2)))), ((U', s1'), (V', s2')),
                   P', sc))
            else false__
      | (GQ, D, D', UsVs, UsVs', P, sc) ->
          leftInstantiate (GQ, D, ((Less (UsVs, UsVs')) :: D'), P, sc)
    let rec eqInstL (GQ, D, D', UsVs, UsVs', P', sc) =
      eqInstLW (GQ, D, D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), P', sc)
    let rec eqInstLW =
      function
      | (((G, Q) as GQ), D, D',
         ((Lam (Dec (_, V1'), U'), s1'), (Pi ((Dec (_, V2'), _), V'), s2')),
         ((Lam (Dec (_, V1''), U''), s1''),
          (Pi ((Dec (_, V2''), _), V''), s2'')),
         P', sc) ->
          let X = I.newEVar (G, (I.EClo (V1'', s1''))) in
          eqInstL
            (GQ, D, D',
              ((U', (I.Dot ((I.Exp X), s1'))),
                (V', (I.Dot ((I.Exp X), s2')))),
              ((U'', (I.Dot ((I.Exp X), s1''))),
                (V'', (I.Dot ((I.Exp X), s2'')))), P',
              (function | () -> (isParameter (Q, X); sc ())))
      | (GQ, D, D', UsVs, UsVs', P', sc) ->
          eqIL (GQ, D, D', UsVs, UsVs', P', sc)
    let rec eqIL =
      function
      | (((G, Q) as GQ), D, D', (((Root (Const c, S), s), Vs) as UsVs),
         (((Root (Const c', S'), s'), Vs') as UsVs'), P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, D, D', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq (UsVs, UsVs')) :: D)))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (Def c, S), s), Vs) as UsVs),
         (((Root (Def c', S'), s'), Vs') as UsVs'), P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, D, D', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq (UsVs, UsVs')) :: D)))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (Const c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), P', sc) ->
          if isAtomic (GQ, Us')
          then
            leftInstantiate
              (GQ, D, ((Eq ((Us', Vs'), (Us, Vs))) :: D'), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq ((Us, Vs), (Us', Vs'))) :: D)))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (Def c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), P', sc) ->
          if isAtomic (GQ, Us')
          then
            leftInstantiate
              (GQ, D, ((Eq ((Us', Vs'), (Us, Vs))) :: D'), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq ((Us, Vs), (Us', Vs'))) :: D)))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Def c, S'), s') as Us'), Vs'), P', sc) ->
          if isAtomic (GQ, Us)
          then
            leftInstantiate
              (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq ((Us, Vs), (Us', Vs'))) :: D')))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Const c, S'), s') as Us'), Vs'), P', sc) ->
          if isAtomic (GQ, Us)
          then
            leftInstantiate
              (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (G, ((Eq ((Us, Vs), (Us', Vs'))) :: D')))
                           atomicRCtxToString (G, D'))
                          ^ " ---> ")
                     atomicPredToString (G, P'))
                    ^ "\n")
             else ();
             true__)
      | (((G, Q) as GQ), D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (BVar n', S'), s') as Us'), Vs'), P', sc) ->
          if n = n'
          then
            let Dec (_, V') = I.ctxDec (G, n) in
            eqSpineIL
              (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P',
                sc)
          else
            leftInstantiate
              (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P', sc)
      | (((G, Q) as GQ), D, D', UsVs, UsVs', P', sc) ->
          (if (!Global.chatter) > 4
           then
             print
               (((^) (((^) ((^) " Proved: " atomicRCtxToString
                              (G, ((Eq (UsVs, UsVs')) :: D)))
                         atomicRCtxToString (G, D'))
                        ^ " ---> ")
                   atomicPredToString (G, P'))
                  ^ "\n")
           else ();
           true__)
    let rec eqSpineIL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P', sc) =
      eqSpineILW
        (GQ, D, D', (Ss, (Whnf.whnf Vs)), (Ss', (Whnf.whnf Vs')), P', sc)
    let rec eqSpineILW =
      function
      | (GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P', sc) ->
          leftInstantiate (GQ, D, D', P', sc)
      | (GQ, D, D', ((SClo (S, s'), s''), Vs), SsVs', P', sc) ->
          eqSpineIL (GQ, D, D', ((S, (I.comp (s', s''))), Vs), SsVs', P', sc)
      | (GQ, D, D', SsVs, ((SClo (S', s'), s''), Vs'), P', sc) ->
          eqSpineIL
            (GQ, D, D', SsVs, ((S', (I.comp (s', s''))), Vs'), P', sc)
      | (GQ, D, D', ((App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), P', sc)
          ->
          let D1 = (Eq (((U, s1), (V1, s2)), ((U', s1'), (V1', s2')))) :: D in
          eqSpineIL
            (GQ, D1, D',
              ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (U, s1))), s2)))),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))),
              P', sc)
    let rec rightDecompose =
      function
      | (GQ, D', Less (O, O')) -> ordLtR (GQ, D', O, O')
      | (GQ, D', Leq (O, O')) -> ordLeR (GQ, D', O, O')
      | (GQ, D', Eq (O, O')) -> ordEqR (GQ, D', O, O')
    let rec ordLtR =
      function
      | (GQ, D', Arg (UsVs), Arg (UsVs')) ->
          ltAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
      | (GQ, D', Lex (O), Lex (O')) -> ltLexR (GQ, D', O, O')
      | (GQ, D', Simul (O), Simul (O')) -> ltSimulR (GQ, D', O, O')
    let rec ordLeR =
      function
      | (GQ, D', Arg (UsVs), Arg (UsVs')) ->
          leAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
      | (GQ, D', Lex (O), Lex (O')) ->
          (ltLexR (GQ, D', O, O')) || (ordEqsR (GQ, D', O, O'))
      | (GQ, D', Simul (O), Simul (O')) -> leSimulR (GQ, D', O, O')
    let rec ordEqR =
      function
      | (GQ, D', Arg (UsVs), Arg (UsVs')) ->
          (conv (UsVs, UsVs')) ||
            (eqAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate))
      | (GQ, D', Lex (O), Lex (O')) -> ordEqsR (GQ, D', O, O')
      | (GQ, D', Simul (O), Simul (O')) -> ordEqsR (GQ, D', O, O')
    let rec ordEqsR =
      function
      | (GQ, D', nil, nil) -> true__
      | (GQ, D', (O)::L, (O')::L') ->
          (ordEqR (GQ, D', O, O')) && (ordEqsR (GQ, D', L, L'))
    let rec ltLexR =
      function
      | (GQ, D', nil, nil) -> false__
      | (GQ, D', (O)::L, (O')::L') ->
          (ordLtR (GQ, D', O, O')) ||
            ((ordEqR (GQ, D', O, O')) && (ltLexR (GQ, D', L, L')))
    let rec leLexR (GQ, D', L, L') =
      (ltLexR (GQ, D', L, L')) || (ordEqsR (GQ, D', L, L'))
    let rec ltSimulR =
      function
      | (GQ, D, nil, nil) -> false__
      | (GQ, D, (O)::L, (O')::L') ->
          ((ordLtR (GQ, D, O, O')) && (leSimulR (GQ, D, L, L'))) ||
            ((ordEqR (GQ, D, O, O')) && (ltSimulR (GQ, D, L, L')))
    let rec leSimulR =
      function
      | (GQ, D, nil, nil) -> true__
      | (GQ, D, (O)::L, (O')::L') ->
          (ordLeR (GQ, D, O, O')) && (leSimulR (GQ, D, L, L'))
    let rec ltAtomicR (GQ, D, UsVs, UsVs', sc, k) =
      ltAtomicRW (GQ, D, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec ltAtomicRW =
      function
      | (GQ, D, ((Us, ((Root _, s') as Vs)) as UsVs), UsVs', sc, k) ->
          ltR (GQ, D, UsVs, UsVs', sc, k)
      | (((G, Q) as GQ), D, ((Lam (_, U), s1), (Pi ((Dec, _), V), s2)),
         ((U', s1'), (V', s2')), sc, k) ->
          let UsVs' =
            ((U', (I.comp (s1', I.shift))), (V', (I.comp (s2', I.shift)))) in
          let UsVs = ((U, (I.dot1 s1)), (V, (I.dot1 s2))) in
          let D' = shiftACtx D (function | s -> I.comp (s, I.shift)) in
          ltAtomicR
            (((I.Decl (G, (N.decLUName (G, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))), D', UsVs, UsVs', sc, k)
    let rec leAtomicR (GQ, D, UsVs, UsVs', sc, k) =
      leAtomicRW (GQ, D, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec leAtomicRW =
      function
      | (GQ, D, ((Us, ((Root _, s') as Vs)) as UsVs), UsVs', sc, k) ->
          leR (GQ, D, UsVs, UsVs', sc, k)
      | (((G, Q) as GQ), D, ((Lam (_, U), s1), (Pi ((Dec, _), V), s2)),
         ((U', s1'), (V', s2')), sc, k) ->
          let D' = shiftACtx D (function | s -> I.comp (s, I.shift)) in
          let UsVs' =
            ((U', (I.comp (s1', I.shift))), (V', (I.comp (s2', I.shift)))) in
          let UsVs = ((U, (I.dot1 s1)), (V, (I.dot1 s2))) in
          leAtomicR
            (((I.Decl (G, (N.decLUName (G, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))), D', UsVs, UsVs', sc, k)
    let rec eqAtomicR (((G, Q) as GQ), D, UsVs, UsVs', sc, k) =
      eqAtomicRW (GQ, D, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), sc, k)
    let rec eqAtomicRW =
      function
      | (((G, Q) as GQ), D, ((Lam (_, U), s1), (Pi ((Dec, _), V), s2)),
         ((Lam (_, U'), s1'), (Pi ((Dec', _), V'), s2')), sc, k) ->
          eqAtomicR
            (((I.Decl (G, (N.decLUName (G, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))),
              (shiftACtx D (function | s -> I.comp (s, I.shift))),
              ((U, (I.dot1 s1')), (V, (I.dot1 s2'))),
              ((U', (I.dot1 s1')), (V', (I.dot1 s2'))), sc, k)
      | (GQ, D, (Us, ((Root _, s2) as Vs)), (Us', ((Root _, s2') as Vs')),
         sc, k) -> eqR (GQ, D, (Us, Vs), (Us', Vs'), sc, k)
      | (GQ, D, (Us, Vs), (Us', Vs'), sc, k) -> false__
    let rec ltR (((G, Q) as GQ), D, UsVs, UsVs', sc, k) =
      ltRW (GQ, D, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec ltRW =
      function
      | (GQ, D, (Us, Vs), (((Root (Const c, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us')
          then k (GQ, D, nil, (Less ((Us, Vs), (Us', Vs'))), sc)
          else
            ltSpineR
              (GQ, D, (Us, Vs), ((S', s'), ((I.constType c), I.id)), sc, k)
      | (GQ, D, (Us, Vs), (((Root (Def c, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us')
          then k (GQ, D, nil, (Less ((Us, Vs), (Us', Vs'))), sc)
          else
            ltSpineR
              (GQ, D, (Us, Vs), ((S', s'), ((I.constType c), I.id)), sc, k)
      | (((G, Q) as GQ), D, (Us, Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us')
          then k (GQ, D, nil, (Less ((Us, Vs), (Us', Vs'))), sc)
          else
            (let Dec (_, V') = I.ctxDec (G, n) in
             ltSpineR (GQ, D, (Us, Vs), ((S', s'), (V', I.id)), sc, k))
      | (GQ, D, _, ((EVar _, _), _), _, _) -> false__
      | (((G, Q) as GQ), D, ((U, s1), (V, s2)),
         ((Lam (Dec (_, V1'), U'), s1'), (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, k) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' = function | () -> (isParameter (Q, X); sc ()) in
            ltR
              (GQ, D, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', k)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               ltR
                 (GQ, D, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, k))
            else false__
    let rec ltSpineR (GQ, D, (Us, Vs), (Ss', Vs'), sc, k) =
      ltSpineRW (GQ, D, (Us, Vs), (Ss', (Whnf.whnf Vs')), sc, k)
    let rec ltSpineRW =
      function
      | (GQ, D, (Us, Vs), ((I.Nil, _), _), _, _) -> false__
      | (GQ, D, (Us, Vs), ((SClo (S, s'), s''), Vs'), sc, k) ->
          ltSpineR (GQ, D, (Us, Vs), ((S, (I.comp (s', s''))), Vs'), sc, k)
      | (GQ, D, (Us, Vs),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
          (leAtomicR (GQ, D, (Us, Vs), ((U', s1'), (V1', s2')), sc, k)) ||
            (ltSpineR
               (GQ, D, (Us, Vs),
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))), sc, k))
    let rec leR (GQ, D, UsVs, UsVs', sc, k) =
      leRW (GQ, D, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec leRW =
      function
      | (((G, Q) as GQ), D, ((U, s1), (V, s2)),
         ((Lam (Dec (_, V1'), U'), s1'), (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, k) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' = function | () -> (isParameter (Q, X)) && (sc ()) in
            leR
              (GQ, D, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', k)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               leR
                 (GQ, D, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, k))
            else false__
      | (GQ, D, UsVs, UsVs', sc, k) ->
          (ltR (GQ, D, UsVs, UsVs', sc, k)) ||
            (eqR (GQ, D, UsVs, UsVs', sc, k))
    let rec eqR (((G, Q) as GQ), D, UsVs, UsVs', sc, k) =
      (CSManager.trail (function | () -> (eq (G, UsVs, UsVs')) && (sc ())))
        || (eqR' (GQ, D, UsVs, UsVs', sc, k))
    let rec eqR' =
      function
      | (GQ, D, (Us, ((Pi ((Dec (_, V2'), _), V'), s2') as Vs)),
         (Us', ((Root _, s2'') as Vs')), sc, k) -> false__
      | (GQ, D, (Us, ((Root _, s2') as Vs)),
         (Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), sc, k) ->
          false__
      | (GQ, D, (((Root (Const c, S), s), Vs) as UsVs),
         (((Root (Const c', S'), s'), Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, D, ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), sc, k)
          else false__
      | (GQ, D, (((Root (Const c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us')
          then k (GQ, D, nil, (Eq ((Us', Vs'), (Us, Vs))), sc)
          else false__
      | (GQ, D, (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Const c, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us)
          then k (GQ, D, nil, (Eq ((Us, Vs), (Us', Vs'))), sc)
          else false__
      | (GQ, D, (((Root (Def c, S), s), Vs) as UsVs),
         (((Root (Def c', S'), s'), Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, D, ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), sc, k)
          else false__
      | (GQ, D, (((Root (Def c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us')
          then k (GQ, D, nil, (Eq ((Us', Vs'), (Us, Vs))), sc)
          else false__
      | (GQ, D, (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Def c, S'), s') as Us'), Vs'), sc, k) ->
          if isAtomic (GQ, Us)
          then k (GQ, D, nil, (Eq ((Us, Vs), (Us', Vs'))), sc)
          else false__
      | (((G, Q) as GQ), D, (((Root (BVar n, S), s) as Us), Vs),
         (((Root (BVar n', S'), s') as Us'), Vs'), sc, k) ->
          if n = n'
          then
            let Dec (_, V') = I.ctxDec (G, n) in
            eqSpineR
              (GQ, D, ((S, s), (V', I.id)), ((S', s'), (V', I.id)), sc, k)
          else k (GQ, D, nil, (Eq ((Us, Vs), (Us', Vs'))), sc)
      | (GQ, D, UsVs, UsVs', sc, k) -> k (GQ, D, nil, (Eq (UsVs, UsVs')), sc)
    let rec eqSpineR (GQ, D, (Ss, Vs), (Ss', Vs'), sc, k) =
      eqSpineRW (GQ, D, (Ss, (Whnf.whnf Vs)), (Ss', (Whnf.whnf Vs')), sc, k)
    let rec eqSpineRW =
      function
      | (GQ, D, ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), sc, k) -> true__
      | (GQ, D, ((SClo (S, s'), s''), Vs), SsVs', sc, k) ->
          eqSpineR (GQ, D, ((S, (I.comp (s', s''))), Vs), SsVs', sc, k)
      | (GQ, D, SsVs, ((SClo (S', s'), s''), Vs'), sc, k) ->
          eqSpineR (GQ, D, SsVs, ((S', (I.comp (s', s''))), Vs'), sc, k)
      | (GQ, D, ((App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
          (eqAtomicR
             (GQ, D, ((U, s1), (V1, s2)), ((U', s1'), (V1', s2')), sc, k))
            &&
            (eqSpineR
               (GQ, D,
                 ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (U, s1))), s2)))),
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))), sc, k))
      | (GQ, D, SsVs, SsVs', sc, k) -> false__
    let rec leftDecompose =
      function
      | (((G, Q) as GQ), nil, D', P) -> rightDecompose (GQ, D', P)
      | (GQ, (Less (Arg (UsVs), Arg (UsVs')))::D, D', P) ->
          ltAtomicL (GQ, D, D', UsVs, UsVs', P)
      | (GQ, (Less (Lex (O), Lex (O')))::D, D', P) ->
          ltLexL (GQ, D, D', O, O', P)
      | (GQ, (Less (Simul (O), Simul (O')))::D, D', P) ->
          ltSimulL (GQ, D, D', O, O', P)
      | (GQ, (Leq (Arg (UsVs), Arg (UsVs')))::D, D', P) ->
          leAtomicL (GQ, D, D', UsVs, UsVs', P)
      | (GQ, (Leq (Lex (O), Lex (O')))::D, D', P) ->
          (leftDecompose (GQ, ((Less ((R.Lex O), (R.Lex O'))) :: D), D', P))
            &&
            (leftDecompose (GQ, ((Eq ((R.Lex O), (R.Lex O'))) :: D), D', P))
      | (GQ, (Leq (Simul (O), Simul (O')))::D, D', P) ->
          leSimulL (GQ, D, D', O, O', P)
      | (GQ, (Eq (Arg (UsVs), Arg (UsVs')))::D, D', P) ->
          eqAtomicL (GQ, D, D', UsVs, UsVs', P)
      | (GQ, (Eq (Lex (O), Lex (O')))::D, D', P) ->
          eqsL (GQ, D, D', O, O', P)
      | (GQ, (Eq (Simul (O), Simul (O')))::D, D', P) ->
          eqsL (GQ, D, D', O, O', P)
      | (((G, Q) as GQ), (Pi (Dec, O))::D, D', P) ->
          (if (!Global.chatter) > 3
           then
             (print " Ignoring quantified order ";
              print (F.makestring_fmt (fmtPredicate (G, (Pi (Dec, O))))))
           else ();
           leftDecompose (GQ, D, D', P))
    let rec ltLexL =
      function
      | (GQ, D, D', nil, nil, P) -> true__
      | (GQ, D, D', (O)::L, (O')::L', P) ->
          (leftDecompose (GQ, ((Less (O, O')) :: D), D', P)) &&
            (ltLexL (GQ, ((Eq (O, O')) :: D), D', L, L', P))
    let rec eqsL =
      function
      | (GQ, D, D', nil, nil, P) -> true__
      | (GQ, D, D', (O)::L, (O')::L', P) ->
          (leftDecompose (GQ, ((Eq (O, O')) :: D), D', P)) &&
            (eqsL (GQ, D, D', L, L', P))
    let rec ltSimulL =
      function
      | (GQ, D, D', nil, nil, P) -> leftDecompose (GQ, D, D', P)
      | (GQ, D, D', (O)::L, (O')::L', P) ->
          (leSimulL (GQ, ((Less (O, O')) :: D), D', L, L', P)) ||
            (ltSimulL (GQ, ((Eq (O, O')) :: D), D', L, L', P))
    let rec leSimulL =
      function
      | (GQ, D, D', nil, nil, P) -> leftDecompose (GQ, D, D', P)
      | (GQ, D, D', (O)::L, (O')::L', P) ->
          leSimulL (GQ, ((Leq (O, O')) :: D), D', L, L', P)
    let rec ltAtomicL (GQ, D, D', UsVs, UsVs', P) =
      ltAtomicLW (GQ, D, D', UsVs, (Whnf.whnfEta UsVs'), P)
    let rec ltAtomicLW =
      function
      | (((G, Q) as GQ), D, D', UsVs, (Us', ((Root _, s') as Vs')), P) ->
          ltL (GQ, D, D', UsVs, (Us', Vs'), P)
      | (((G, Q) as GQ), D, D', ((U, s1), (V, s2)),
         ((Lam (_, U'), s1'), (Pi ((Dec', _), V'), s2')), P) ->
          let D1 = shiftRCtx D (function | s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx D' (function | s -> I.comp (s, I.shift)) in
          let UsVs =
            ((U, (I.comp (s1, I.shift))), (V, (I.comp (s2, I.shift)))) in
          let UsVs' = ((U', (I.dot1 s1')), (V', (I.dot1 s2'))) in
          let P' = shiftP P (function | s -> I.comp (s, I.shift)) in
          ltAtomicL
            (((I.Decl (G, (N.decLUName (G, (I.decSub (Dec', s2')))))),
               (I.Decl (Q, All))), D1, D1', UsVs, UsVs', P')
    let rec leAtomicL (GQ, D, D', UsVs, UsVs', P) =
      leAtomicLW (GQ, D, D', UsVs, (Whnf.whnfEta UsVs'), P)
    let rec leAtomicLW =
      function
      | (GQ, D, D', UsVs, (Us', ((Root (H, S), s') as Vs')), P) ->
          leL (GQ, D, D', UsVs, (Us', Vs'), P)
      | (((G, Q) as GQ), D, D', ((U, s1), (V, s2)),
         ((Lam (_, U'), s1'), (Pi ((Dec', _), V'), s2')), P) ->
          let D1 = shiftRCtx D (function | s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx D' (function | s -> I.comp (s, I.shift)) in
          let UsVs =
            ((U, (I.comp (s1, I.shift))), (V, (I.comp (s2, I.shift)))) in
          let UsVs' = ((U', (I.dot1 s1')), (V', (I.dot1 s2'))) in
          let P' = shiftP P (function | s -> I.comp (s, I.shift)) in
          leAtomicL
            (((I.Decl (G, (N.decLUName (G, (I.decSub (Dec', s2')))))),
               (I.Decl (Q, All))), D1, D1', UsVs, UsVs', P')
    let rec eqAtomicL (GQ, D, D', UsVs, UsVs', P) =
      eqAtomicLW (GQ, D, D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), P)
    let rec eqAtomicLW =
      function
      | (GQ, D, D', (Us, ((Root _, s) as Vs)), (Us', ((Root _, s') as Vs')),
         P) -> eqL (GQ, D, D', (Us, Vs), (Us', Vs'), P)
      | (GQ, D, D', (Us, ((Root _, s) as Vs)), (Us', ((Pi _, s') as Vs')), P)
          -> true__
      | (GQ, D, D', (Us, ((Pi _, s) as Vs)), (Us', ((Root _, s') as Vs')), P)
          -> true__
      | (GQ, D, D', (Us, ((Pi _, s) as Vs)), (Us', ((Pi _, s') as Vs')), P)
          -> leftDecompose (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P)
    let rec leL (GQ, D, D', UsVs, UsVs', P) =
      (ltAtomicL (GQ, D, D', UsVs, UsVs', P)) &&
        (eqAtomicL (GQ, D, D', UsVs, UsVs', P))
    let rec ltL (GQ, D, D', UsVs, (Us', Vs'), P) =
      ltLW (GQ, D, D', UsVs, ((Whnf.whnf Us'), Vs'), P)
    let rec ltLW =
      function
      | (((G, Q) as GQ), D, D', UsVs,
         (((Root (BVar n, S'), s') as Us'), Vs'), P) ->
          if isAtomic (GQ, Us')
          then leftDecompose (GQ, D, ((Less (UsVs, (Us', Vs'))) :: D'), P)
          else
            (let Dec (_, V') = I.ctxDec (G, n) in
             ltSpineL (GQ, D, D', UsVs, ((S', s'), (V', I.id)), P))
      | (GQ, D, D', UsVs, ((Root (Const c, S'), s'), Vs'), P) ->
          ltSpineL (GQ, D, D', UsVs, ((S', s'), ((I.constType c), I.id)), P)
      | (GQ, D, D', UsVs, ((Root (Def c, S'), s'), Vs'), P) ->
          ltSpineL (GQ, D, D', UsVs, ((S', s'), ((I.constType c), I.id)), P)
    let rec ltSpineL (GQ, D, D', UsVs, (Ss', Vs'), P) =
      ltSpineLW (GQ, D, D', UsVs, (Ss', (Whnf.whnf Vs')), P)
    let rec ltSpineLW =
      function
      | (GQ, D, D', UsVs, ((I.Nil, _), _), _) -> true__
      | (GQ, D, D', UsVs, ((SClo (S, s'), s''), Vs'), P) ->
          ltSpineL (GQ, D, D', UsVs, ((S, (I.comp (s', s''))), Vs'), P)
      | (GQ, D, D', UsVs,
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), P) ->
          (leAtomicL (GQ, D, D', UsVs, ((U', s1'), (V1', s2')), P)) &&
            (ltSpineL
               (GQ, D, D', UsVs,
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))), P))
    let rec eqL (GQ, D, D', UsVs, UsVs', P) =
      eqLW (GQ, D, D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), P)
    let rec eqLW =
      function
      | (GQ, D, D', (Us, ((Pi ((Dec (_, V2'), _), V'), s2') as Vs)),
         (Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), P) ->
          leftDecompose (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P)
      | (GQ, D, D', (Us, ((Pi ((Dec (_, V2'), _), V'), s2') as Vs)),
         (Us', ((Root _, s2'') as Vs')), P) -> true__
      | (GQ, D, D', (Us, ((Root _, s2') as Vs)),
         (Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), P) -> true__
      | (GQ, D, D', (((Root (Const c, S), s), Vs) as UsVs),
         (((Root (Const c', S'), s'), Vs') as UsVs'), P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, D, D', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P)
          else true__
      | (GQ, D, D', (((Root (Const c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), P) ->
          if isAtomic (GQ, Us')
          then leftDecompose (GQ, D, ((Eq ((Us', Vs'), (Us, Vs))) :: D'), P)
          else true__
      | (GQ, D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Const c, S'), s') as Us'), Vs'), P) ->
          if isAtomic (GQ, Us)
          then leftDecompose (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P)
          else true__
      | (GQ, D, D', (((Root (Def c, S), s), Vs) as UsVs),
         (((Root (Def c', S'), s'), Vs') as UsVs'), P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, D, D', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P)
          else true__
      | (GQ, D, D', (((Root (Def c, S), s) as Us), Vs),
         (((Root (BVar n, S'), s') as Us'), Vs'), P) ->
          if isAtomic (GQ, Us')
          then leftDecompose (GQ, D, ((Eq ((Us', Vs'), (Us, Vs))) :: D'), P)
          else true__
      | (GQ, D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (Def c, S'), s') as Us'), Vs'), P) ->
          if isAtomic (GQ, Us)
          then leftDecompose (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P)
          else true__
      | (((G, Q) as GQ), D, D', (((Root (BVar n, S), s) as Us), Vs),
         (((Root (BVar n', S'), s') as Us'), Vs'), P) ->
          if n = n'
          then
            let Dec (_, V') = I.ctxDec (G, n) in
            eqSpineL
              (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P)
          else leftDecompose (GQ, D, ((Eq ((Us, Vs), (Us', Vs'))) :: D'), P)
      | (GQ, D, D', UsVs, UsVs', P) ->
          leftDecompose (GQ, D, ((Eq (UsVs, UsVs')) :: D'), P)
    let rec eqSpineL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P) =
      eqSpineLW (GQ, D, D', (Ss, (Whnf.whnf Vs)), (Ss', (Whnf.whnf Vs')), P)
    let rec eqSpineLW =
      function
      | (GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P) ->
          leftDecompose (GQ, D, D', P)
      | (GQ, D, D', ((SClo (S, s'), s''), Vs), SsVs', P) ->
          eqSpineL (GQ, D, D', ((S, (I.comp (s', s''))), Vs), SsVs', P)
      | (GQ, D, D', SsVs, ((SClo (S', s'), s''), Vs'), P) ->
          eqSpineL (GQ, D, D', SsVs, ((S', (I.comp (s', s''))), Vs'), P)
      | (GQ, D, D', ((App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), P) ->
          let D1 =
            (Eq
               ((R.Arg ((U, s1), (V1, s2))), (R.Arg ((U', s1'), (V1', s2')))))
              :: D in
          eqSpineL
            (GQ, D1, D',
              ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (U, s1))), s2)))),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))),
              P)
    let rec deduce (G, Q, D, P) = leftDecompose ((G, Q), D, nil, P)
    (* Reasoning about order relations *)
    (*
    Typing context        G
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] =  U'[s1'] : V'[s2']

    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- P as an abbreviation

    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2]
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]

  *)
    (*--------------------------------------------------------------------*)
    (* Printing atomic orders *)
    (*--------------------------------------------------------------------*)
    (* shifting substitutions *)
    (* shiftO O f = O'

      if O is an order
         then we shift the substitutions which are associated
         with its terms by applying f to it
    *)
    (*--------------------------------------------------------------------*)
    (* Printing *)
    (* F.String "Pi predicate"  *)
    (*--------------------------------------------------------------------*)
    (* init () = true

       Invariant:
       The inital constraint continuation
    *)
    (* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
    (* isFreeEVar (Us) = true
       iff Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
    (* constraints must be empty *)
    (* isAtomic (G, X) = true
       Invariant:
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter
     *)
    (* should disallow orelse ? *)
    (*      | isAtomicW (GQ, (X as (I.EClo _))) = true    existential var *)
    (*-----------------------------------------------------------*)
    (* eq (G, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B

       Invariant:
       B holds  iff
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)
    (* lookupEq (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)
    (* lookupLt (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Less(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)
    (*  eqAtomic (GQ, D, D', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  D, UsVs = UsVs', D' ---> UsVs = UsVs'  (ctx lookup)
        or  D, UsVs' = UsVs, D' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  D, D' ---> UsVs = UsVs' by transitivity

     *)
    (* transEq (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
    (* ltAtomic (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs <UsVs' ; D' ---> UsVs < UsVs'   (identity)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
    (* transLt (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
    (* atomic (GQ, D, P) = B

     An atomic order context D' is maximally decomposed iff

          T := Root(c, Nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   all atomic order relations in D' are
          either T' < T or T1' = T1'

   An atomic order P' is maximally decomposed iff
          T := Root(c, nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   T' < T or T1 = T1

    Invariant:

    B iff
          D and P are maximally decomposed,
      and they may contain EVars
      and G : Q
      and G |- P
      and G |- D
      and D --> P

      *)
    (*-----------------------------------------------------------*)
    (* leftInstantiate ((G,Q), D, D', P, sc) = B

     B iff
           G : Q
       and G |- D
       and G |- D'
       and G |- P

       and  D is an atomic order relation ctx, which does not
              contain any EVars
       and  D' is an atomic order relation ctx, which may
              contain EVars
       and  P' is a atomic order relation

       and  D --> P

    D' accumulates all orders
    *)
    (* should never happen by invariant *)
    (* ltInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] < U'[s'] ---> P
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that X can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* leInstL ((G, Q), D, D', UsVs, UsVs', P', sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] <= U'[s'] ---> P'
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that X can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* eqInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
    *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eqIL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
       and U, U' will be maximally unfolded
    *)
    (* (Us, Vs as (I.Pi _ , _)) and (Us', Vs' as (I.Root _, _))
           or the other way
         *)
    (*--------------------------------------------------------------*)
    (* rightDecompose (GQ, D', P) = B

    B iff
        G : Q
    and D is maximally unfolded, but does not contain any EVars
    and P is a order relation
    and G |- P
    and D --> P

    *)
    (* ordLtR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 < O2
    *)
    (* ordLeR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 <= O2
    *)
    (* ordEqR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 = O2
    *)
    (* ordEqsR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D' --> L1 = L2
    *)
    (* ltLexR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D' --> L1 is lexically smaller than L2
    *)
    (* ltSimulR (GQ, D, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D implies that L1 is simultaneously smaller than L2
    *)
    (* leSimulR (G, Q, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D implies that L1 is simultaneously less than or equal to L2
    *)
    (*--------------------------------------------------------------*)
    (* Atomic Orders (Right) *)
    (* ltAtomicR (GQ, (D, D'), UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' implies U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* leAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* eqAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is structurally equivalent to U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* Dec = Dec' *)
    (* mismatch: not equal *)
    (* Fri Feb 25 21:26:39 2005 -fp !!! *)
    (* ltR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded

    *)
    (* either leftInstantiate D or  atomic reasoning *)
    (* either leftInstantiate D or  atomic reasoning *)
    (* either leftInstantiate D or  atomic reasoning *)
    (* == I.targetFam V2' *)
    (* enforce that X is only instantiated to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* possibly redundant if lhs always subordinate to rhs *)
    (* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
    (* leR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that X can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* eqR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] = U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
    (* either leftInstantiate D or atomic reasoning *)
    (* either leftInstantiate D or atomic reasoning *)
    (* either leftInstantiate D or atomic reasoning *)
    (* either leftInstantiate D or atomic reasoning *)
    (* either leftInstantiate D or atomic reasoning *)
    (* UsVs = Lam *)
    (* either leftInstantiate D or atomic reasoning *)
    (*--------------------------------------------------------------*)
    (* leftDecompose (G, Q, D, D', P) = B

      if G : Q and
         D --> P  where D might contain orders (lex and simul)

      then D' --> P
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < L

      L := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = L
      R := Root(n, Nil) | Lam(x:A, R)
      L := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)
    (* less *)
    (* le *)
    (* eq *)
    (* drop assumption Pi D. P *)
    (*--------------------------------------------------------------*)
    (* Lexicographic and Simultanous Orders (left)*)
    (* If D, D', Lex O1, ....On < Lex O'1, ....O'n --> P
      then
            D, D', O1 < O1' --> P
        and D, D', O1 = O1', O2 < O2 --> P

        ...
        and D, D', O1 = O1', .., O_n-1 = O'_n-1, O_n < O'_n --> P
    *)
    (* If D, D', Lex O1, ....On = Lex O'1, ....O'n --> P
      If D, D', Simul O1, ....On = Simul O'1, ....O'n --> P
      then
            D, D', O1 = O1' --> P
        and D, D', O2 = O2' --> P

        ...
        and D, D', On = On' --> P
    *)
    (*--------------------------------------------------------------*)
    (* Atomic Orders (left) *)
    (* U := Root(c, S) | Root(n, S) | Lam(x:A, U) *)
    (* ltAtomicL (GQ as (G, Q), D, D', ((U, s1), (V, s2)), ((U', s1'), (V', s2')), P) = B

     B holds iff

            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and  G |- D, D', (U[s1]:V[s2]) < U'[s1']:V'[s2']) --> P


       if G |- D, D', (Us:Vs) < (\x1:A1....\xn:An. U'[s1']: V'[s2']) --> P and
               (n >= 0)
       then
          G, a1:A1, .... an:An |-
             D^n, D'^n, (Us^n:Vs^n) < U'[a1... an . s1'^n]:V'[a1. ... . an . s2'^n] --> P^n

       where D^n, (Us^n, P^n) means all substitutions in D (U, P etc)
             are shifted by n
    *)
    (* see invariant for ltAtomic *)
    (*  *)
    (*--------------------------------------------------------------*)
    (* U' := Root(c, S) | Root(n, S) *)
    (* add definitions! *)
    (*  If D, D', U < Root(c, S) --> P
      then D, D', U <= S' --> P
   *)
    (*  eqL (GQ, D, D', UsVs, UsVs', P) = B

       B holds iff

            G : Q

       and  D is an Order relation ctx
       and  D' is an atomic order relation ctx
       and  P is a order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and D, D', U[s1] = U'[s1'] --> P

       note: D, D', UsVs, UsVs' and P do not
             contain any EVars
   *)
    (*
     | eqLW (GQ, D, D', UsVs as ((I.Root (I.BVar n, I.Nil), s), Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, D, D', P)
         else
           leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

*)
    (* UsVs = Lam *)
    (*--------------------------------------------------------------*)
    (* Infer: D --> P *)
    (* deduce (G, Q, D, P) = B

      B iff
         G :  Q
     and G |- D
     and G |- P
     and D implies P
    *)
    let deduce = deduce
    let shiftRCtx = shiftRCtx
    let shiftPred = shiftP
  end ;;
