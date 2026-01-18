
(* Reasoning about orders *)
(* Author: Brigitte Pientka *)
module type CHECKING  =
  sig
    (*! structure IntSyn : INTSYN !*)
    module Order : ORDER
    (*! structure Paths : PATHS !*)
    (* If Q marks all parameters in a context __g we write   __g : Q  *)
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
    (* If Q marks all parameters in a context __g we write   __g : Q               *)
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
      | (__g, Less ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__g, (I.EClo __Us))) ^ " < ")
            Print.expToString (__g, (I.EClo __Us'))
      | (__g, Leq ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__g, (I.EClo __Us))) ^ " <= ")
            Print.expToString (__g, (I.EClo __Us'))
      | (__g, Eq ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__g, (I.EClo __Us))) ^ " = ")
            Print.expToString (__g, (I.EClo __Us'))
    let rec atomicRCtxToString =
      function
      | (__g, nil) -> " "
      | (__g, (O)::nil) -> atomicPredToString (__g, O)
      | (__g, (O)::__d') ->
          (^) ((atomicRCtxToString (__g, __d')) ^ ", ") atomicPredToString (__g, O)
    let rec shiftO arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Arg ((__u, us), (__v, vs)), f) -> R.Arg ((__u, (f us)), (__v, (f vs)))
      | (Lex (__l), f) -> R.Lex (map (function | O -> shiftO O f) __l)
      | (Simul (__l), f) -> R.Simul (map (function | O -> shiftO O f) __l)
    let rec shiftP arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Less (O1, O2), f) -> Less ((shiftO O1 f), (shiftO O2 f))
      | (Leq (O1, O2), f) -> Leq ((shiftO O1 f), (shiftO O2 f))
      | (Eq (O1, O2), f) -> Eq ((shiftO O1 f), (shiftO O2 f))
      | (Pi ((Dec (x, __v) as __d), P), f) -> Pi (__d, (shiftP P f))
    let rec shiftRCtx (Rl) f = map (function | p -> shiftP p f) Rl
    let rec shiftArg arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Less (((__U1, s1), (V1, s1')), ((__U2, s2), (V2, s2'))), f) ->
          Less (((__U1, (f s1)), (V1, (f s1'))), ((__U2, (f s2)), (V2, (f s2'))))
      | (Leq (((__U1, s1), (V1, s1')), ((__U2, s2), (V2, s2'))), f) ->
          Leq (((__U1, (f s1)), (V1, (f s1'))), ((__U2, (f s2)), (V2, (f s2'))))
      | (Eq (((__U1, s1), (V1, s1')), ((__U2, s2), (V2, s2'))), f) ->
          Eq (((__U1, (f s1)), (V1, (f s1'))), ((__U2, (f s2)), (V2, (f s2'))))
    let rec shiftACtx (Rl) f = map (function | p -> shiftArg p f) Rl
    let rec fmtOrder (__g, O) =
      let rec fmtOrder' =
        function
        | Arg (((__u, s) as __Us), ((__v, s') as __Vs)) ->
            F.hbox
              [F.String "("; Print.formatExp (__g, (I.EClo __Us)); F.String ")"]
        | Lex (__l) ->
            F.hbox
              [F.String "{"; F.hOVbox0 1 0 1 (fmtOrders __l); F.String "}"]
        | Simul (__l) ->
            F.hbox
              [F.String "["; F.hOVbox0 1 0 1 (fmtOrders __l); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (O)::[] -> (fmtOrder' O) :: []
        | (O)::__l -> (::) ((fmtOrder' O) :: F.Break) fmtOrders __l in
      fmtOrder' O
    let rec fmtComparison (__g, O, comp, O') =
      F.hOVbox0 1 0 1
        [fmtOrder (__g, O); F.Break; F.String comp; F.Break; fmtOrder (__g, O')]
    let rec fmtPredicate' =
      function
      | (__g, Less (O, O')) -> fmtComparison (__g, O, "<", O')
      | (__g, Leq (O, O')) -> fmtComparison (__g, O, "<=", O')
      | (__g, Eq (O, O')) -> fmtComparison (__g, O, "=", O')
      | (__g, Pi (__d, P)) ->
          F.hbox [F.String "Pi "; fmtPredicate' ((I.Decl (__g, __d)), P)]
    let rec fmtPredicate (__g, P) = fmtPredicate' ((Names.ctxName __g), P)
    let rec fmtRGCtx' =
      function
      | (__g, nil) -> ""
      | (__g, (P)::[]) -> F.makestring_fmt (fmtPredicate' (__g, P))
      | (__g, (P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate' (__g, P))) ^ " ,") fmtRGCtx'
            (__g, Rl)
    let rec fmtRGCtx (__g, Rl) = fmtRGCtx' ((Names.ctxName __g), Rl)
    let rec init () = true__
    let rec eqCid (c, c') = c = c'
    let rec conv ((__Us, __Vs), (__Us', __Vs')) =
      (Conv.conv (__Vs, __Vs')) && (Conv.conv (__Us, __Us'))
    let rec isUniversal =
      function | All -> true__ | Exist -> false__ | Exist' -> false__
    let rec isExistential =
      function | All -> false__ | Exist -> true__ | Exist' -> true__
    let rec isParameter (Q, x) = isParameterW (Q, (Whnf.whnf (x, I.id)))
    let rec isParameterW (Q, __Us) =
      try isUniversal (I.ctxLookup (Q, (Whnf.etaContract (I.EClo __Us))))
      with | Whnf.Eta -> isFreeEVar __Us
    let rec isFreeEVar =
      function
      | (EVar (_, _, _, ref []), _) -> true__
      | (Lam (__d, __u), s) -> isFreeEVar (Whnf.whnf (__u, (I.dot1 s)))
      | _ -> false__
    let rec isAtomic (GQ, __Us) = isAtomicW (GQ, (Whnf.whnf __Us))
    let rec isAtomicW =
      function
      | (GQ, ((Root (Const c, S) as x), s)) -> isAtomicS (GQ, (S, s))
      | (GQ, ((Root (Def c, S) as x), s)) -> isAtomicS (GQ, (S, s))
      | (((__g, Q) as GQ), ((Root (BVar n, S) as x), s)) ->
          (isExistential (I.ctxLookup (Q, n))) || (isAtomicS (GQ, (S, s)))
      | (GQ, _) -> false__
    let rec isAtomicS =
      function
      | (GQ, (I.Nil, _)) -> true__
      | (GQ, (SClo (S, s'), s'')) -> isAtomicS (GQ, (S, (I.comp (s', s''))))
      | (GQ, (App (__u', S'), s1')) -> false__
    let rec eq (__g, (__Us, __Vs), (__Us', __Vs')) =
      (Unify.unifiable (__g, __Vs, __Vs')) && (Unify.unifiable (__g, __Us, __Us'))
    let rec lookupEq =
      function
      | (GQ, nil, UsVs, UsVs', sc) -> false__
      | (GQ, (Less (_, _))::__d, UsVs, UsVs', sc) ->
          lookupEq (GQ, __d, UsVs, UsVs', sc)
      | (((__g, Q) as GQ), (Eq (UsVs1, UsVs1'))::__d, UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (__g, UsVs1, UsVs)) &&
                    ((eq (__g, UsVs1', UsVs')) && (sc ()))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (__g, UsVs1, UsVs')) &&
                       ((eq (__g, UsVs1', UsVs)) && (sc ()))))
               || (lookupEq (GQ, __d, UsVs, UsVs', sc)))
    let rec lookupLt =
      function
      | (GQ, nil, UsVs, UsVs', sc) -> false__
      | (GQ, (Eq (_, _))::__d, UsVs, UsVs', sc) ->
          lookupLt (GQ, __d, UsVs, UsVs', sc)
      | (((__g, Q) as GQ), (Less (UsVs1, UsVs1'))::__d, UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (__g, UsVs1, UsVs)) &&
                    ((eq (__g, UsVs1', UsVs')) && (sc ()))))
            || (lookupLt (GQ, __d, UsVs, UsVs', sc))
    let rec eqAtomic =
      function
      | (((__g, Q) as GQ), nil, __d', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function | () -> (eq (__g, UsVs, UsVs')) && (sc ())))
            || (lookupEq (GQ, __d', UsVs, UsVs', sc))
      | (((__g, Q) as GQ), __d, __d', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function | () -> (eq (__g, UsVs, UsVs')) && (sc ())))
            ||
            ((lookupEq (GQ, __d, UsVs, UsVs', sc)) ||
               ((lookupEq (GQ, __d', UsVs, UsVs', sc)) ||
                  (transEq (GQ, __d, __d', UsVs, UsVs', sc))))
    let rec transEq =
      function
      | (((__g, Q) as GQ), nil, __d, UsVs, UsVs', sc) -> false__
      | (((__g, Q) as GQ), (Eq (UsVs1, UsVs1'))::__d, __d', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (__g, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (eqAtomicR (GQ, (__d @ __d'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (__g, UsVs1, UsVs')) &&
                       ((sc ()) &&
                          (eqAtomicR (GQ, (__d @ __d'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transEq
                  (GQ, __d, ((Eq (UsVs1, UsVs1')) :: __d'), UsVs, UsVs', sc)))
      | (((__g, Q) as GQ), (Less (UsVs1, UsVs1'))::__d, __d', UsVs, UsVs', sc) ->
          transEq (GQ, __d, __d', UsVs, UsVs', sc)
    let rec ltAtomic =
      function
      | (((__g, Q) as GQ), nil, __d', UsVs, UsVs', sc) ->
          lookupLt (GQ, __d', UsVs, UsVs', sc)
      | (((__g, Q) as GQ), __d, __d', UsVs, UsVs', sc) ->
          (lookupLt (GQ, __d, UsVs, UsVs', sc)) ||
            ((lookupLt (GQ, __d', UsVs, UsVs', sc)) ||
               (transLt (GQ, __d, __d', UsVs, UsVs', sc)))
    let rec transLt =
      function
      | (((__g, Q) as GQ), nil, __d, UsVs, UsVs', sc) -> false__
      | (((__g, Q) as GQ), (Eq (UsVs1, UsVs1'))::__d, __d', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (__g, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (ltAtomicR (GQ, (__d @ __d'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (__g, UsVs1, UsVs')) &&
                       ((sc ()) &&
                          (ltAtomicR (GQ, (__d @ __d'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transLt
                  (GQ, __d, ((Eq (UsVs1, UsVs1')) :: __d'), UsVs, UsVs', sc)))
      | (((__g, Q) as GQ), (Less (UsVs1, UsVs1'))::__d, __d', UsVs, UsVs', sc) ->
          (CSManager.trail
             (function
              | () ->
                  (eq (__g, UsVs1', UsVs')) &&
                    ((sc ()) &&
                       (eqAtomicR (GQ, (__d @ __d'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (function
                 | () ->
                     (eq (__g, UsVs1', UsVs')) &&
                       ((sc ()) &&
                          (ltAtomicR (GQ, (__d @ __d'), UsVs, UsVs1, sc, atomic)))))
               ||
               (transLt
                  (GQ, __d, ((Less (UsVs1, UsVs1')) :: __d'), UsVs, UsVs', sc)))
    let rec atomic =
      function
      | (GQ, __d, __d', Eq (UsVs, UsVs'), sc) ->
          eqAtomic (GQ, __d, __d', UsVs, UsVs', sc)
      | (GQ, __d, __d', Less (UsVs, UsVs'), sc) ->
          ltAtomic (GQ, __d, __d', UsVs, UsVs', sc)
    let rec leftInstantiate =
      function
      | (((__g, Q) as GQ), nil, __d', P, sc) ->
          if atomic (GQ, __d', nil, P, sc)
          then
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) " Proved: " atomicRCtxToString (__g, __d')) ^
                          " ---> ")
                     atomicPredToString (__g, P))
                    ^ "\n")
             else ();
             true__)
          else false__
      | (GQ, (Less (UsVs, UsVs'))::__d, __d', P, sc) ->
          ltInstL (GQ, __d, __d', UsVs, UsVs', P, sc)
      | (GQ, (Leq (UsVs, UsVs'))::__d, __d', P, sc) ->
          leInstL (GQ, __d, __d', UsVs, UsVs', P, sc)
      | (GQ, (Eq (UsVs, UsVs'))::__d, __d', P, sc) ->
          eqInstL (GQ, __d, __d', UsVs, UsVs', P, sc)
    let rec ltInstL (GQ, __d, __d', UsVs, UsVs', __P', sc) =
      ltInstLW (GQ, __d, __d', (Whnf.whnfEta UsVs), UsVs', __P', sc)
    let rec ltInstLW =
      function
      | (((__g, Q) as GQ), __d, __d',
         ((Lam ((Dec (_, V1) as Dec), __u), s1),
          (Pi ((Dec (_, V2), _), __v), s2)),
         ((__u', s1'), (__v', s2')), __P', sc) ->
          if Subordinate.equiv ((I.targetFam __v'), (I.targetFam V1))
          then
            let x = I.newEVar (__g, (I.EClo (V1, s1))) in
            let sc' = function | () -> (isParameter (Q, x)) && (sc ()) in
            ltInstL
              ((__g, Q), __d, __d',
                ((__u, (I.Dot ((I.Exp x), s1))), (__v, (I.Dot ((I.Exp x), s2)))),
                ((__u', s1'), (__v', s2')), __P', sc')
          else
            if Subordinate.below ((I.targetFam V1), (I.targetFam __v'))
            then
              (let x = I.newEVar (__g, (I.EClo (V1, s1))) in
               ltInstL
                 ((__g, Q), __d, __d',
                   ((__u, (I.Dot ((I.Exp x), s1))),
                     (__v, (I.Dot ((I.Exp x), s2)))), ((__u', s1'), (__v', s2')),
                   __P', sc))
            else false__
      | (GQ, __d, __d', UsVs, UsVs', __P', sc) ->
          leftInstantiate (GQ, __d, ((Less (UsVs, UsVs')) :: __d'), __P', sc)
    let rec leInstL (GQ, __d, __d', UsVs, UsVs', __P', sc) =
      leInstLW (GQ, __d, __d', (Whnf.whnfEta UsVs), UsVs', __P', sc)
    let rec leInstLW =
      function
      | (((__g, Q) as GQ), __d, __d',
         ((Lam (Dec (_, V1), __u), s1), (Pi ((Dec (_, V2), _), __v), s2)),
         ((__u', s1'), (__v', s2')), __P', sc) ->
          if Subordinate.equiv ((I.targetFam __v'), (I.targetFam V1))
          then
            let x = I.newEVar (__g, (I.EClo (V1, s1))) in
            let sc' = function | () -> (isParameter (Q, x)) && (sc ()) in
            leInstL
              ((__g, Q), __d, __d',
                ((__u, (I.Dot ((I.Exp x), s1))), (__v, (I.Dot ((I.Exp x), s2)))),
                ((__u', s1'), (__v', s2')), __P', sc')
          else
            if Subordinate.below ((I.targetFam V1), (I.targetFam __v'))
            then
              (let x = I.newEVar (__g, (I.EClo (V1, s1))) in
               leInstL
                 ((__g, Q), __d, __d',
                   ((__u, (I.Dot ((I.Exp x), s1))),
                     (__v, (I.Dot ((I.Exp x), s2)))), ((__u', s1'), (__v', s2')),
                   __P', sc))
            else false__
      | (GQ, __d, __d', UsVs, UsVs', P, sc) ->
          leftInstantiate (GQ, __d, ((Less (UsVs, UsVs')) :: __d'), P, sc)
    let rec eqInstL (GQ, __d, __d', UsVs, UsVs', __P', sc) =
      eqInstLW (GQ, __d, __d', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), __P', sc)
    let rec eqInstLW =
      function
      | (((__g, Q) as GQ), __d, __d',
         ((Lam (Dec (_, V1'), __u'), s1'), (Pi ((Dec (_, V2'), _), __v'), s2')),
         ((Lam (Dec (_, V1''), __u''), s1''),
          (Pi ((Dec (_, V2''), _), __v''), s2'')),
         __P', sc) ->
          let x = I.newEVar (__g, (I.EClo (V1'', s1''))) in
          eqInstL
            (GQ, __d, __d',
              ((__u', (I.Dot ((I.Exp x), s1'))),
                (__v', (I.Dot ((I.Exp x), s2')))),
              ((__u'', (I.Dot ((I.Exp x), s1''))),
                (__v'', (I.Dot ((I.Exp x), s2'')))), __P',
              (function | () -> (isParameter (Q, x); sc ())))
      | (GQ, __d, __d', UsVs, UsVs', __P', sc) ->
          eqIL (GQ, __d, __d', UsVs, UsVs', __P', sc)
    let rec eqIL =
      function
      | (((__g, Q) as GQ), __d, __d', (((Root (Const c, S), s), __Vs) as UsVs),
         (((Root (Const c', S'), s'), __Vs') as UsVs'), __P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, __d, __d', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq (UsVs, UsVs')) :: __d)))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (Def c, S), s), __Vs) as UsVs),
         (((Root (Def c', S'), s'), __Vs') as UsVs'), __P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, __d, __d', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq (UsVs, UsVs')) :: __d)))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (Const c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us')
          then
            leftInstantiate
              (GQ, __d, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __d'), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d)))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (Def c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us')
          then
            leftInstantiate
              (GQ, __d, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __d'), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d)))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Def c, S'), s') as __Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us)
          then
            leftInstantiate
              (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d')))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Const c, S'), s') as __Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us)
          then
            leftInstantiate
              (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__g, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d')))
                           atomicRCtxToString (__g, __d'))
                          ^ " ---> ")
                     atomicPredToString (__g, __P'))
                    ^ "\n")
             else ();
             true__)
      | (((__g, Q) as GQ), __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (BVar n', S'), s') as __Us'), __Vs'), __P', sc) ->
          if n = n'
          then
            let Dec (_, __v') = I.ctxDec (__g, n) in
            eqSpineIL
              (GQ, __d, __d', ((S, s), (__v', I.id)), ((S', s'), (__v', I.id)), __P',
                sc)
          else
            leftInstantiate
              (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), __P', sc)
      | (((__g, Q) as GQ), __d, __d', UsVs, UsVs', __P', sc) ->
          (if (!Global.chatter) > 4
           then
             print
               (((^) (((^) ((^) " Proved: " atomicRCtxToString
                              (__g, ((Eq (UsVs, UsVs')) :: __d)))
                         atomicRCtxToString (__g, __d'))
                        ^ " ---> ")
                   atomicPredToString (__g, __P'))
                  ^ "\n")
           else ();
           true__)
    let rec eqSpineIL (GQ, __d, __d', (__Ss, __Vs), (__Ss', __Vs'), __P', sc) =
      eqSpineILW
        (GQ, __d, __d', (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')), __P', sc)
    let rec eqSpineILW =
      function
      | (GQ, __d, __d', ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), __P', sc) ->
          leftInstantiate (GQ, __d, __d', __P', sc)
      | (GQ, __d, __d', ((SClo (S, s'), s''), __Vs), SsVs', __P', sc) ->
          eqSpineIL (GQ, __d, __d', ((S, (I.comp (s', s''))), __Vs), SsVs', __P', sc)
      | (GQ, __d, __d', SsVs, ((SClo (S', s'), s''), __Vs'), __P', sc) ->
          eqSpineIL
            (GQ, __d, __d', SsVs, ((S', (I.comp (s', s''))), __Vs'), __P', sc)
      | (GQ, __d, __d', ((App (__u, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), __P', sc)
          ->
          let D1 = (Eq (((__u, s1), (V1, s2)), ((__u', s1'), (V1', s2')))) :: __d in
          eqSpineIL
            (GQ, D1, __d',
              ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (__u, s1))), s2)))),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))),
              __P', sc)
    let rec rightDecompose =
      function
      | (GQ, __d', Less (O, O')) -> ordLtR (GQ, __d', O, O')
      | (GQ, __d', Leq (O, O')) -> ordLeR (GQ, __d', O, O')
      | (GQ, __d', Eq (O, O')) -> ordEqR (GQ, __d', O, O')
    let rec ordLtR =
      function
      | (GQ, __d', Arg (UsVs), Arg (UsVs')) ->
          ltAtomicR (GQ, __d', UsVs, UsVs', init, leftInstantiate)
      | (GQ, __d', Lex (O), Lex (O')) -> ltLexR (GQ, __d', O, O')
      | (GQ, __d', Simul (O), Simul (O')) -> ltSimulR (GQ, __d', O, O')
    let rec ordLeR =
      function
      | (GQ, __d', Arg (UsVs), Arg (UsVs')) ->
          leAtomicR (GQ, __d', UsVs, UsVs', init, leftInstantiate)
      | (GQ, __d', Lex (O), Lex (O')) ->
          (ltLexR (GQ, __d', O, O')) || (ordEqsR (GQ, __d', O, O'))
      | (GQ, __d', Simul (O), Simul (O')) -> leSimulR (GQ, __d', O, O')
    let rec ordEqR =
      function
      | (GQ, __d', Arg (UsVs), Arg (UsVs')) ->
          (conv (UsVs, UsVs')) ||
            (eqAtomicR (GQ, __d', UsVs, UsVs', init, leftInstantiate))
      | (GQ, __d', Lex (O), Lex (O')) -> ordEqsR (GQ, __d', O, O')
      | (GQ, __d', Simul (O), Simul (O')) -> ordEqsR (GQ, __d', O, O')
    let rec ordEqsR =
      function
      | (GQ, __d', nil, nil) -> true__
      | (GQ, __d', (O)::__l, (O')::__l') ->
          (ordEqR (GQ, __d', O, O')) && (ordEqsR (GQ, __d', __l, __l'))
    let rec ltLexR =
      function
      | (GQ, __d', nil, nil) -> false__
      | (GQ, __d', (O)::__l, (O')::__l') ->
          (ordLtR (GQ, __d', O, O')) ||
            ((ordEqR (GQ, __d', O, O')) && (ltLexR (GQ, __d', __l, __l')))
    let rec leLexR (GQ, __d', __l, __l') =
      (ltLexR (GQ, __d', __l, __l')) || (ordEqsR (GQ, __d', __l, __l'))
    let rec ltSimulR =
      function
      | (GQ, __d, nil, nil) -> false__
      | (GQ, __d, (O)::__l, (O')::__l') ->
          ((ordLtR (GQ, __d, O, O')) && (leSimulR (GQ, __d, __l, __l'))) ||
            ((ordEqR (GQ, __d, O, O')) && (ltSimulR (GQ, __d, __l, __l')))
    let rec leSimulR =
      function
      | (GQ, __d, nil, nil) -> true__
      | (GQ, __d, (O)::__l, (O')::__l') ->
          (ordLeR (GQ, __d, O, O')) && (leSimulR (GQ, __d, __l, __l'))
    let rec ltAtomicR (GQ, __d, UsVs, UsVs', sc, k) =
      ltAtomicRW (GQ, __d, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec ltAtomicRW =
      function
      | (GQ, __d, ((__Us, ((Root _, s') as __Vs)) as UsVs), UsVs', sc, k) ->
          ltR (GQ, __d, UsVs, UsVs', sc, k)
      | (((__g, Q) as GQ), __d, ((Lam (_, __u), s1), (Pi ((Dec, _), __v), s2)),
         ((__u', s1'), (__v', s2')), sc, k) ->
          let UsVs' =
            ((__u', (I.comp (s1', I.shift))), (__v', (I.comp (s2', I.shift)))) in
          let UsVs = ((__u, (I.dot1 s1)), (__v, (I.dot1 s2))) in
          let __d' = shiftACtx __d (function | s -> I.comp (s, I.shift)) in
          ltAtomicR
            (((I.Decl (__g, (N.decLUName (__g, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))), __d', UsVs, UsVs', sc, k)
    let rec leAtomicR (GQ, __d, UsVs, UsVs', sc, k) =
      leAtomicRW (GQ, __d, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec leAtomicRW =
      function
      | (GQ, __d, ((__Us, ((Root _, s') as __Vs)) as UsVs), UsVs', sc, k) ->
          leR (GQ, __d, UsVs, UsVs', sc, k)
      | (((__g, Q) as GQ), __d, ((Lam (_, __u), s1), (Pi ((Dec, _), __v), s2)),
         ((__u', s1'), (__v', s2')), sc, k) ->
          let __d' = shiftACtx __d (function | s -> I.comp (s, I.shift)) in
          let UsVs' =
            ((__u', (I.comp (s1', I.shift))), (__v', (I.comp (s2', I.shift)))) in
          let UsVs = ((__u, (I.dot1 s1)), (__v, (I.dot1 s2))) in
          leAtomicR
            (((I.Decl (__g, (N.decLUName (__g, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))), __d', UsVs, UsVs', sc, k)
    let rec eqAtomicR (((__g, Q) as GQ), __d, UsVs, UsVs', sc, k) =
      eqAtomicRW (GQ, __d, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), sc, k)
    let rec eqAtomicRW =
      function
      | (((__g, Q) as GQ), __d, ((Lam (_, __u), s1), (Pi ((Dec, _), __v), s2)),
         ((Lam (_, __u'), s1'), (Pi ((Dec', _), __v'), s2')), sc, k) ->
          eqAtomicR
            (((I.Decl (__g, (N.decLUName (__g, (I.decSub (Dec, s2)))))),
               (I.Decl (Q, All))),
              (shiftACtx __d (function | s -> I.comp (s, I.shift))),
              ((__u, (I.dot1 s1')), (__v, (I.dot1 s2'))),
              ((__u', (I.dot1 s1')), (__v', (I.dot1 s2'))), sc, k)
      | (GQ, __d, (__Us, ((Root _, s2) as __Vs)), (__Us', ((Root _, s2') as __Vs')),
         sc, k) -> eqR (GQ, __d, (__Us, __Vs), (__Us', __Vs'), sc, k)
      | (GQ, __d, (__Us, __Vs), (__Us', __Vs'), sc, k) -> false__
    let rec ltR (((__g, Q) as GQ), __d, UsVs, UsVs', sc, k) =
      ltRW (GQ, __d, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec ltRW =
      function
      | (GQ, __d, (__Us, __Vs), (((Root (Const c, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us')
          then k (GQ, __d, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
          else
            ltSpineR
              (GQ, __d, (__Us, __Vs), ((S', s'), ((I.constType c), I.id)), sc, k)
      | (GQ, __d, (__Us, __Vs), (((Root (Def c, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us')
          then k (GQ, __d, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
          else
            ltSpineR
              (GQ, __d, (__Us, __Vs), ((S', s'), ((I.constType c), I.id)), sc, k)
      | (((__g, Q) as GQ), __d, (__Us, __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us')
          then k (GQ, __d, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
          else
            (let Dec (_, __v') = I.ctxDec (__g, n) in
             ltSpineR (GQ, __d, (__Us, __Vs), ((S', s'), (__v', I.id)), sc, k))
      | (GQ, __d, _, ((EVar _, _), _), _, _) -> false__
      | (((__g, Q) as GQ), __d, ((__u, s1), (__v, s2)),
         ((Lam (Dec (_, V1'), __u'), s1'), (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, k) ->
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' = function | () -> (isParameter (Q, x); sc ()) in
            ltR
              (GQ, __d, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', k)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               ltR
                 (GQ, __d, ((__u, s1), (__v, s2)),
                   ((__u', (I.Dot ((I.Exp x), s1'))),
                     (__v', (I.Dot ((I.Exp x), s2')))), sc, k))
            else false__
    let rec ltSpineR (GQ, __d, (__Us, __Vs), (__Ss', __Vs'), sc, k) =
      ltSpineRW (GQ, __d, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, k)
    let rec ltSpineRW =
      function
      | (GQ, __d, (__Us, __Vs), ((I.Nil, _), _), _, _) -> false__
      | (GQ, __d, (__Us, __Vs), ((SClo (S, s'), s''), __Vs'), sc, k) ->
          ltSpineR (GQ, __d, (__Us, __Vs), ((S, (I.comp (s', s''))), __Vs'), sc, k)
      | (GQ, __d, (__Us, __Vs),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
          (leAtomicR (GQ, __d, (__Us, __Vs), ((__u', s1'), (V1', s2')), sc, k)) ||
            (ltSpineR
               (GQ, __d, (__Us, __Vs),
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))), sc, k))
    let rec leR (GQ, __d, UsVs, UsVs', sc, k) =
      leRW (GQ, __d, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec leRW =
      function
      | (((__g, Q) as GQ), __d, ((__u, s1), (__v, s2)),
         ((Lam (Dec (_, V1'), __u'), s1'), (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, k) ->
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' = function | () -> (isParameter (Q, x)) && (sc ()) in
            leR
              (GQ, __d, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', k)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               leR
                 (GQ, __d, ((__u, s1), (__v, s2)),
                   ((__u', (I.Dot ((I.Exp x), s1'))),
                     (__v', (I.Dot ((I.Exp x), s2')))), sc, k))
            else false__
      | (GQ, __d, UsVs, UsVs', sc, k) ->
          (ltR (GQ, __d, UsVs, UsVs', sc, k)) ||
            (eqR (GQ, __d, UsVs, UsVs', sc, k))
    let rec eqR (((__g, Q) as GQ), __d, UsVs, UsVs', sc, k) =
      (CSManager.trail (function | () -> (eq (__g, UsVs, UsVs')) && (sc ())))
        || (eqR' (GQ, __d, UsVs, UsVs', sc, k))
    let rec eqR' =
      function
      | (GQ, __d, (__Us, ((Pi ((Dec (_, V2'), _), __v'), s2') as __Vs)),
         (__Us', ((Root _, s2'') as __Vs')), sc, k) -> false__
      | (GQ, __d, (__Us, ((Root _, s2') as __Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), __v''), s2'') as __Vs')), sc, k) ->
          false__
      | (GQ, __d, (((Root (Const c, S), s), __Vs) as UsVs),
         (((Root (Const c', S'), s'), __Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, __d, ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), sc, k)
          else false__
      | (GQ, __d, (((Root (Const c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us')
          then k (GQ, __d, nil, (Eq ((__Us', __Vs'), (__Us, __Vs))), sc)
          else false__
      | (GQ, __d, (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Const c, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us)
          then k (GQ, __d, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
          else false__
      | (GQ, __d, (((Root (Def c, S), s), __Vs) as UsVs),
         (((Root (Def c', S'), s'), __Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, __d, ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), sc, k)
          else false__
      | (GQ, __d, (((Root (Def c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us')
          then k (GQ, __d, nil, (Eq ((__Us', __Vs'), (__Us, __Vs))), sc)
          else false__
      | (GQ, __d, (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Def c, S'), s') as __Us'), __Vs'), sc, k) ->
          if isAtomic (GQ, __Us)
          then k (GQ, __d, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
          else false__
      | (((__g, Q) as GQ), __d, (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (BVar n', S'), s') as __Us'), __Vs'), sc, k) ->
          if n = n'
          then
            let Dec (_, __v') = I.ctxDec (__g, n) in
            eqSpineR
              (GQ, __d, ((S, s), (__v', I.id)), ((S', s'), (__v', I.id)), sc, k)
          else k (GQ, __d, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
      | (GQ, __d, UsVs, UsVs', sc, k) -> k (GQ, __d, nil, (Eq (UsVs, UsVs')), sc)
    let rec eqSpineR (GQ, __d, (__Ss, __Vs), (__Ss', __Vs'), sc, k) =
      eqSpineRW (GQ, __d, (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')), sc, k)
    let rec eqSpineRW =
      function
      | (GQ, __d, ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), sc, k) -> true__
      | (GQ, __d, ((SClo (S, s'), s''), __Vs), SsVs', sc, k) ->
          eqSpineR (GQ, __d, ((S, (I.comp (s', s''))), __Vs), SsVs', sc, k)
      | (GQ, __d, SsVs, ((SClo (S', s'), s''), __Vs'), sc, k) ->
          eqSpineR (GQ, __d, SsVs, ((S', (I.comp (s', s''))), __Vs'), sc, k)
      | (GQ, __d, ((App (__u, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
          (eqAtomicR
             (GQ, __d, ((__u, s1), (V1, s2)), ((__u', s1'), (V1', s2')), sc, k))
            &&
            (eqSpineR
               (GQ, __d,
                 ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (__u, s1))), s2)))),
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))), sc, k))
      | (GQ, __d, SsVs, SsVs', sc, k) -> false__
    let rec leftDecompose =
      function
      | (((__g, Q) as GQ), nil, __d', P) -> rightDecompose (GQ, __d', P)
      | (GQ, (Less (Arg (UsVs), Arg (UsVs')))::__d, __d', P) ->
          ltAtomicL (GQ, __d, __d', UsVs, UsVs', P)
      | (GQ, (Less (Lex (O), Lex (O')))::__d, __d', P) ->
          ltLexL (GQ, __d, __d', O, O', P)
      | (GQ, (Less (Simul (O), Simul (O')))::__d, __d', P) ->
          ltSimulL (GQ, __d, __d', O, O', P)
      | (GQ, (Leq (Arg (UsVs), Arg (UsVs')))::__d, __d', P) ->
          leAtomicL (GQ, __d, __d', UsVs, UsVs', P)
      | (GQ, (Leq (Lex (O), Lex (O')))::__d, __d', P) ->
          (leftDecompose (GQ, ((Less ((R.Lex O), (R.Lex O'))) :: __d), __d', P))
            &&
            (leftDecompose (GQ, ((Eq ((R.Lex O), (R.Lex O'))) :: __d), __d', P))
      | (GQ, (Leq (Simul (O), Simul (O')))::__d, __d', P) ->
          leSimulL (GQ, __d, __d', O, O', P)
      | (GQ, (Eq (Arg (UsVs), Arg (UsVs')))::__d, __d', P) ->
          eqAtomicL (GQ, __d, __d', UsVs, UsVs', P)
      | (GQ, (Eq (Lex (O), Lex (O')))::__d, __d', P) ->
          eqsL (GQ, __d, __d', O, O', P)
      | (GQ, (Eq (Simul (O), Simul (O')))::__d, __d', P) ->
          eqsL (GQ, __d, __d', O, O', P)
      | (((__g, Q) as GQ), (Pi (Dec, O))::__d, __d', P) ->
          (if (!Global.chatter) > 3
           then
             (print " Ignoring quantified order ";
              print (F.makestring_fmt (fmtPredicate (__g, (Pi (Dec, O))))))
           else ();
           leftDecompose (GQ, __d, __d', P))
    let rec ltLexL =
      function
      | (GQ, __d, __d', nil, nil, P) -> true__
      | (GQ, __d, __d', (O)::__l, (O')::__l', P) ->
          (leftDecompose (GQ, ((Less (O, O')) :: __d), __d', P)) &&
            (ltLexL (GQ, ((Eq (O, O')) :: __d), __d', __l, __l', P))
    let rec eqsL =
      function
      | (GQ, __d, __d', nil, nil, P) -> true__
      | (GQ, __d, __d', (O)::__l, (O')::__l', P) ->
          (leftDecompose (GQ, ((Eq (O, O')) :: __d), __d', P)) &&
            (eqsL (GQ, __d, __d', __l, __l', P))
    let rec ltSimulL =
      function
      | (GQ, __d, __d', nil, nil, P) -> leftDecompose (GQ, __d, __d', P)
      | (GQ, __d, __d', (O)::__l, (O')::__l', P) ->
          (leSimulL (GQ, ((Less (O, O')) :: __d), __d', __l, __l', P)) ||
            (ltSimulL (GQ, ((Eq (O, O')) :: __d), __d', __l, __l', P))
    let rec leSimulL =
      function
      | (GQ, __d, __d', nil, nil, P) -> leftDecompose (GQ, __d, __d', P)
      | (GQ, __d, __d', (O)::__l, (O')::__l', P) ->
          leSimulL (GQ, ((Leq (O, O')) :: __d), __d', __l, __l', P)
    let rec ltAtomicL (GQ, __d, __d', UsVs, UsVs', P) =
      ltAtomicLW (GQ, __d, __d', UsVs, (Whnf.whnfEta UsVs'), P)
    let rec ltAtomicLW =
      function
      | (((__g, Q) as GQ), __d, __d', UsVs, (__Us', ((Root _, s') as __Vs')), P) ->
          ltL (GQ, __d, __d', UsVs, (__Us', __Vs'), P)
      | (((__g, Q) as GQ), __d, __d', ((__u, s1), (__v, s2)),
         ((Lam (_, __u'), s1'), (Pi ((Dec', _), __v'), s2')), P) ->
          let D1 = shiftRCtx __d (function | s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx __d' (function | s -> I.comp (s, I.shift)) in
          let UsVs =
            ((__u, (I.comp (s1, I.shift))), (__v, (I.comp (s2, I.shift)))) in
          let UsVs' = ((__u', (I.dot1 s1')), (__v', (I.dot1 s2'))) in
          let __P' = shiftP P (function | s -> I.comp (s, I.shift)) in
          ltAtomicL
            (((I.Decl (__g, (N.decLUName (__g, (I.decSub (Dec', s2')))))),
               (I.Decl (Q, All))), D1, D1', UsVs, UsVs', __P')
    let rec leAtomicL (GQ, __d, __d', UsVs, UsVs', P) =
      leAtomicLW (GQ, __d, __d', UsVs, (Whnf.whnfEta UsVs'), P)
    let rec leAtomicLW =
      function
      | (GQ, __d, __d', UsVs, (__Us', ((Root (H, S), s') as __Vs')), P) ->
          leL (GQ, __d, __d', UsVs, (__Us', __Vs'), P)
      | (((__g, Q) as GQ), __d, __d', ((__u, s1), (__v, s2)),
         ((Lam (_, __u'), s1'), (Pi ((Dec', _), __v'), s2')), P) ->
          let D1 = shiftRCtx __d (function | s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx __d' (function | s -> I.comp (s, I.shift)) in
          let UsVs =
            ((__u, (I.comp (s1, I.shift))), (__v, (I.comp (s2, I.shift)))) in
          let UsVs' = ((__u', (I.dot1 s1')), (__v', (I.dot1 s2'))) in
          let __P' = shiftP P (function | s -> I.comp (s, I.shift)) in
          leAtomicL
            (((I.Decl (__g, (N.decLUName (__g, (I.decSub (Dec', s2')))))),
               (I.Decl (Q, All))), D1, D1', UsVs, UsVs', __P')
    let rec eqAtomicL (GQ, __d, __d', UsVs, UsVs', P) =
      eqAtomicLW (GQ, __d, __d', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), P)
    let rec eqAtomicLW =
      function
      | (GQ, __d, __d', (__Us, ((Root _, s) as __Vs)), (__Us', ((Root _, s') as __Vs')),
         P) -> eqL (GQ, __d, __d', (__Us, __Vs), (__Us', __Vs'), P)
      | (GQ, __d, __d', (__Us, ((Root _, s) as __Vs)), (__Us', ((Pi _, s') as __Vs')), P)
          -> true__
      | (GQ, __d, __d', (__Us, ((Pi _, s) as __Vs)), (__Us', ((Root _, s') as __Vs')), P)
          -> true__
      | (GQ, __d, __d', (__Us, ((Pi _, s) as __Vs)), (__Us', ((Pi _, s') as __Vs')), P)
          -> leftDecompose (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), P)
    let rec leL (GQ, __d, __d', UsVs, UsVs', P) =
      (ltAtomicL (GQ, __d, __d', UsVs, UsVs', P)) &&
        (eqAtomicL (GQ, __d, __d', UsVs, UsVs', P))
    let rec ltL (GQ, __d, __d', UsVs, (__Us', __Vs'), P) =
      ltLW (GQ, __d, __d', UsVs, ((Whnf.whnf __Us'), __Vs'), P)
    let rec ltLW =
      function
      | (((__g, Q) as GQ), __d, __d', UsVs,
         (((Root (BVar n, S'), s') as __Us'), __Vs'), P) ->
          if isAtomic (GQ, __Us')
          then leftDecompose (GQ, __d, ((Less (UsVs, (__Us', __Vs'))) :: __d'), P)
          else
            (let Dec (_, __v') = I.ctxDec (__g, n) in
             ltSpineL (GQ, __d, __d', UsVs, ((S', s'), (__v', I.id)), P))
      | (GQ, __d, __d', UsVs, ((Root (Const c, S'), s'), __Vs'), P) ->
          ltSpineL (GQ, __d, __d', UsVs, ((S', s'), ((I.constType c), I.id)), P)
      | (GQ, __d, __d', UsVs, ((Root (Def c, S'), s'), __Vs'), P) ->
          ltSpineL (GQ, __d, __d', UsVs, ((S', s'), ((I.constType c), I.id)), P)
    let rec ltSpineL (GQ, __d, __d', UsVs, (__Ss', __Vs'), P) =
      ltSpineLW (GQ, __d, __d', UsVs, (__Ss', (Whnf.whnf __Vs')), P)
    let rec ltSpineLW =
      function
      | (GQ, __d, __d', UsVs, ((I.Nil, _), _), _) -> true__
      | (GQ, __d, __d', UsVs, ((SClo (S, s'), s''), __Vs'), P) ->
          ltSpineL (GQ, __d, __d', UsVs, ((S, (I.comp (s', s''))), __Vs'), P)
      | (GQ, __d, __d', UsVs,
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), P) ->
          (leAtomicL (GQ, __d, __d', UsVs, ((__u', s1'), (V1', s2')), P)) &&
            (ltSpineL
               (GQ, __d, __d', UsVs,
                 ((S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))), P))
    let rec eqL (GQ, __d, __d', UsVs, UsVs', P) =
      eqLW (GQ, __d, __d', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), P)
    let rec eqLW =
      function
      | (GQ, __d, __d', (__Us, ((Pi ((Dec (_, V2'), _), __v'), s2') as __Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), __v''), s2'') as __Vs')), P) ->
          leftDecompose (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), P)
      | (GQ, __d, __d', (__Us, ((Pi ((Dec (_, V2'), _), __v'), s2') as __Vs)),
         (__Us', ((Root _, s2'') as __Vs')), P) -> true__
      | (GQ, __d, __d', (__Us, ((Root _, s2') as __Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), __v''), s2'') as __Vs')), P) -> true__
      | (GQ, __d, __d', (((Root (Const c, S), s), __Vs) as UsVs),
         (((Root (Const c', S'), s'), __Vs') as UsVs'), P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, __d, __d', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P)
          else true__
      | (GQ, __d, __d', (((Root (Const c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), P) ->
          if isAtomic (GQ, __Us')
          then leftDecompose (GQ, __d, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __d'), P)
          else true__
      | (GQ, __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Const c, S'), s') as __Us'), __Vs'), P) ->
          if isAtomic (GQ, __Us)
          then leftDecompose (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), P)
          else true__
      | (GQ, __d, __d', (((Root (Def c, S), s), __Vs) as UsVs),
         (((Root (Def c', S'), s'), __Vs') as UsVs'), P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, __d, __d', ((S, s), ((I.constType c), I.id)),
                ((S', s'), ((I.constType c'), I.id)), P)
          else true__
      | (GQ, __d, __d', (((Root (Def c, S), s) as __Us), __Vs),
         (((Root (BVar n, S'), s') as __Us'), __Vs'), P) ->
          if isAtomic (GQ, __Us')
          then leftDecompose (GQ, __d, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __d'), P)
          else true__
      | (GQ, __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (Def c, S'), s') as __Us'), __Vs'), P) ->
          if isAtomic (GQ, __Us)
          then leftDecompose (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), P)
          else true__
      | (((__g, Q) as GQ), __d, __d', (((Root (BVar n, S), s) as __Us), __Vs),
         (((Root (BVar n', S'), s') as __Us'), __Vs'), P) ->
          if n = n'
          then
            let Dec (_, __v') = I.ctxDec (__g, n) in
            eqSpineL
              (GQ, __d, __d', ((S, s), (__v', I.id)), ((S', s'), (__v', I.id)), P)
          else leftDecompose (GQ, __d, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __d'), P)
      | (GQ, __d, __d', UsVs, UsVs', P) ->
          leftDecompose (GQ, __d, ((Eq (UsVs, UsVs')) :: __d'), P)
    let rec eqSpineL (GQ, __d, __d', (__Ss, __Vs), (__Ss', __Vs'), P) =
      eqSpineLW (GQ, __d, __d', (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')), P)
    let rec eqSpineLW =
      function
      | (GQ, __d, __d', ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), P) ->
          leftDecompose (GQ, __d, __d', P)
      | (GQ, __d, __d', ((SClo (S, s'), s''), __Vs), SsVs', P) ->
          eqSpineL (GQ, __d, __d', ((S, (I.comp (s', s''))), __Vs), SsVs', P)
      | (GQ, __d, __d', SsVs, ((SClo (S', s'), s''), __Vs'), P) ->
          eqSpineL (GQ, __d, __d', SsVs, ((S', (I.comp (s', s''))), __Vs'), P)
      | (GQ, __d, __d', ((App (__u, S), s1), (Pi ((Dec (_, V1), _), V2), s2)),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), P) ->
          let D1 =
            (Eq
               ((R.Arg ((__u, s1), (V1, s2))), (R.Arg ((__u', s1'), (V1', s2')))))
              :: __d in
          eqSpineL
            (GQ, D1, __d',
              ((S, s1), (V2, (I.Dot ((I.Exp (I.EClo (__u, s1))), s2)))),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))),
              P)
    let rec deduce (__g, Q, __d, P) = leftDecompose ((__g, Q), __d, nil, P)
    (* Reasoning about order relations *)
    (*
    Typing context        __g
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := __u[s1] : __v[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation __P' := __u[s1] : __v[s2] <  __u'[s1'] : __v'[s2'] |
                                __u[s1] : __v[s2] <= __u'[s1'] : __v'[s2'] |
                                __u[s1] : __v[s2] =  __u'[s1'] : __v'[s2']

    Order Relation Ctx    __d  := . | R , __d
    Atomic Order Rel. Ctx __d' := . | R',  __d'

    Invariant:

    sometimes we write __g |- P as an abbreviation

    if P = (O < O')    then __g |- O and __g |- O'
    if P = (O <= O')    then __g |- O and __g |- O'
    if P = (O = O')    then __g |- O and __g |- O'

    if O = Lex O1 .. On  then __g |- O1 and ....G |- On
    if O = Simul O1 .. On  then __g |- O1 and ....G |- On

    if O = __u[s1] : __v[s2]
      then     __g : Q
           and __g |- s1 : G1, G1 |- __u : V1
           and __g |- s2 : G2   G2 |- __v : __l
           and __g |- __u[s1] : __v[s2]

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
    (* isParameter (Q, x) = B

       Invariant:
       If   __g |- x : __v
       and  __g : Q
       then B holds iff x is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
    (* isFreeEVar (__Us) = true
       iff __Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
    (* constraints must be empty *)
    (* isAtomic (__g, x) = true
       Invariant:
       If __g |- x : __v
       and __g : Q
       then B holds iff x is an atomic term which is not a parameter
     *)
    (* should disallow orelse ? *)
    (*      | isAtomicW (GQ, (x as (I.EClo _))) = true    existential var *)
    (*-----------------------------------------------------------*)
    (* eq (__g, ((__u, s1), (__v, s2)), ((__u', s1'), (__v', s2')), sc) = B

       Invariant:
       B holds  iff
            __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s' : G3  G3 |- __u' : __v'
       and  __u[s1] is unifiable with to __u'[s']
       and  all restrictions in sc are satisfied
       and __v[s2] is atomic
       and only __u'[s'] contains EVars
    *)
    (* lookupEq (GQ, __d, UsVs, UsVs', sc) = B

     B holds iff

     and  __d is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          __g : Q
     and  __g |- s1 : G1   G1 |- __u : V1
     and  __g |- s2 : G2   G2 |- __v : __l
     and  __g |- __u[s1] : __v [s2]
     and  __g |- s' : G3  G3 |- __u' : __v'

     if there exists Eq(UsVs1, UsVs1') in __d
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in __d
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)
    (* lookupLt (GQ, __d, UsVs, UsVs', sc) = B

     B holds iff

     and  __d is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          __g : Q
     and  __g |- s1 : G1   G1 |- __u : V1
     and  __g |- s2 : G2   G2 |- __v : __l
     and  __g |- __u[s1] : __v [s2]
     and  __g |- s' : G3  G3 |- __u' : __v'

     if there exists Less(UsVs1, UsVs1') in __d
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)
    (*  eqAtomic (GQ, __d, __d', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  __d, UsVs = UsVs', __d' ---> UsVs = UsVs'  (ctx lookup)
        or  __d, UsVs' = UsVs, __d' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  __d, __d' ---> UsVs = UsVs' by transitivity

     *)
    (* transEq (GQ, __d, __d', UsVs, UsVs', sc) = B

     B iff
        if __d, UsVs' = UsVs1 ; __d' ---> UsVs = UsVs'
          then  __d, __d' ---> UsVs = UsVs1            (transEq1)

        or

        if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'  (transEq2)
          then  __d, __d' ---> UsVs = UsVs1

       or

       if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'
         then __d; UsVs1 = UsVs' __d' ---> UsVs = UsVs'
   *)
    (* ltAtomic (GQ, __d, __d', UsVs, UsVs', sc) = B

     B iff
        if __d, UsVs <UsVs' ; __d' ---> UsVs < UsVs'   (identity)

        or

        if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'  (transEq2)
          then  __d, __d' ---> UsVs = UsVs1

       or

       if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'
         then __d; UsVs1 = UsVs' __d' ---> UsVs = UsVs'
   *)
    (* transLt (GQ, __d, __d', UsVs, UsVs', sc) = B

     B iff
        if __d, UsVs' = UsVs1 ; __d' ---> UsVs = UsVs'
          then  __d, __d' ---> UsVs = UsVs1            (transEq1)

        or

        if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'  (transEq2)
          then  __d, __d' ---> UsVs = UsVs1

       or

       if __d, UsVs1 = UsVs'; __d' ---> UsVs = UsVs'
         then __d; UsVs1 = UsVs' __d' ---> UsVs = UsVs'
   *)
    (* atomic (GQ, __d, P) = B

     An atomic order context __d' is maximally decomposed iff

          T := Root(c, Nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   all atomic order relations in __d' are
          either T' < T or T1' = T1'

   An atomic order __P' is maximally decomposed iff
          T := Root(c, nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   T' < T or T1 = T1

    Invariant:

    B iff
          __d and P are maximally decomposed,
      and they may contain EVars
      and __g : Q
      and __g |- P
      and __g |- __d
      and __d --> P

      *)
    (*-----------------------------------------------------------*)
    (* leftInstantiate ((__g,Q), __d, __d', P, sc) = B

     B iff
           __g : Q
       and __g |- __d
       and __g |- __d'
       and __g |- P

       and  __d is an atomic order relation ctx, which does not
              contain any EVars
       and  __d' is an atomic order relation ctx, which may
              contain EVars
       and  __P' is a atomic order relation

       and  __d --> P

    __d' accumulates all orders
    *)
    (* should never happen by invariant *)
    (* ltInstL ((__g, Q), __d, __d', UsVs, UsVs', P, sc) = B
     Invariant:
       B holds  iff
            __g : Q
       and  __d is an atomic order relation ctx
       and  __d' is an atomic order relation ctx
       and  __P' is a atomic order relation

       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v [s2]
       and  __g |- s' : G3  G3 |- __u' : __v'
       and  sc is a constraint continuation representing restrictions on EVars
       and  __v[s2] atomic
       and  only __u[s1] contains EVars
       and  __d, __d', __u[s1] < __u'[s'] ---> P
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that x can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* leInstL ((__g, Q), __d, __d', UsVs, UsVs', __P', sc) = B
     Invariant:
       B holds  iff
            __g : Q
       and  __d is an atomic order relation ctx
       and  __d' is an atomic order relation ctx
       and  __P' is a atomic order relation

       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v [s2]
       and  __g |- s' : G3  G3 |- __u' : __v'
       and  sc is a constraint continuation representing restrictions on EVars
       and  __v[s2] atomic
       and  only __u[s1] contains EVars
       and  __d, __d', __u[s1] <= __u'[s'] ---> __P'
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that x can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* eqInstL ((__g, Q), __d, __d', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            __g : Q
       and  __d is an atomic order relation ctx
       and  __d' is an atomic order relation ctx
       and  __P' is a atomic order relation
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v [s2]
       and  __g |- s' : G3  G3 |- __u' : __v'
       and  sc is a constraint continuation representing restrictions on EVars
       and  __v[s2] atomic
       and  only __u[s1] and __u'[s'] contain EVars
       and  __d, __d', __u[s1] = __u'[s'] ---> __P'
    *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eqIL ((__g, Q), __d, __d', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            __g : Q
       and  __d is an atomic order relation ctx
       and  __d' is an atomic order relation ctx
       and  __P' is a atomic order relation
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v [s2]
       and  __g |- s' : G3  G3 |- __u' : __v'
       and  sc is a constraint continuation representing restrictions on EVars
       and  __v[s2] atomic
       and  only __u[s1] and __u'[s'] contain EVars
       and  __d, __d', __u[s1] = __u'[s'] ---> __P'
       and __u, __u' will be maximally unfolded
    *)
    (* (__Us, __Vs as (I.Pi _ , _)) and (__Us', __Vs' as (I.Root _, _))
           or the other way
         *)
    (*--------------------------------------------------------------*)
    (* rightDecompose (GQ, __d', P) = B

    B iff
        __g : Q
    and __d is maximally unfolded, but does not contain any EVars
    and P is a order relation
    and __g |- P
    and __d --> P

    *)
    (* ordLtR (GQ, __d, O1, O2) = B'

       Invariant:
       If   __g : Q
       and  __g |- O1 augmented subterm
       and  __g |- O2 augmented subterm not containing any EVars
       then B' holds iff __d --> O1 < O2
    *)
    (* ordLeR (GQ, __d, O1, O2) = B'

       Invariant:
       If   __g : Q
       and  __g |- O1 augmented subterm
       and  __g |- O2 augmented subterm not containing any EVars
       then B' holds iff __d --> O1 <= O2
    *)
    (* ordEqR (GQ, __d, O1, O2) = B'

       Invariant:
       If   __g : Q
       and  __g |- O1 augmented subterm
       and  __g |- O2 augmented subterm not containing any EVars
       then B' holds iff __d --> O1 = O2
    *)
    (* ordEqsR (GQ, __d', L1, L2) = B'

       Invariant:
       If   __g : Q
       and  __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms not containing any EVars
       then B' holds iff __d' --> L1 = L2
    *)
    (* ltLexR (GQ, __d', L1, L2) = B'

       Invariant:
       If   __g : Q
       and  __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff __d' --> L1 is lexically smaller than L2
    *)
    (* ltSimulR (GQ, __d, L1, L2) = B'

       Invariant:
       If   __g : Q
       and  __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff __d implies that L1 is simultaneously smaller than L2
    *)
    (* leSimulR (__g, Q, L1, L2) = B'

       Invariant:
       If   __g : Q
       and  __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms not containing any EVars
       then B' holds iff __d implies that L1 is simultaneously less than or equal to L2
    *)
    (*--------------------------------------------------------------*)
    (* Atomic Orders (Right) *)
    (* ltAtomicR (GQ, (__d, __d'), UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d' implies __u[s1] is a strict subterm of __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* leAtomicR (GQ, __d, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d implies __u[s1] is a subterm of __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* eqAtomicR (GQ, __d, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d implies __u[s1] is structurally equivalent to __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
    (* Dec = Dec' *)
    (* mismatch: not equal *)
    (* Fri Feb 25 21:26:39 2005 -fp !!! *)
    (* ltR (GQ, __d, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d' --> __u[s1] is a strict subterm of __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and __u'[s'] will be maximally unfolded
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded

    *)
    (* either leftInstantiate __d or  atomic reasoning *)
    (* either leftInstantiate __d or  atomic reasoning *)
    (* either leftInstantiate __d or  atomic reasoning *)
    (* == I.targetFam V2' *)
    (* enforce that x is only instantiated to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* possibly redundant if lhs always subordinate to rhs *)
    (* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
    (* leR (GQ, __d, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d' --> __u[s1] is a subterm of __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and __u'[s'] will be maximally unfolded
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that x can only bound to parameter or remain uninstantiated *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* impossible, if additional invariant assumed (see ltW) *)
    (* eqR (GQ, __d, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']
       and  __d' --> __u[s1] = __u'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only __u'[s'] contains EVars
       and __u'[s'] will be maximally unfolded
    *)
    (* either leftInstantiate __d or atomic reasoning *)
    (* either leftInstantiate __d or atomic reasoning *)
    (* either leftInstantiate __d or atomic reasoning *)
    (* either leftInstantiate __d or atomic reasoning *)
    (* either leftInstantiate __d or atomic reasoning *)
    (* UsVs = Lam *)
    (* either leftInstantiate __d or atomic reasoning *)
    (*--------------------------------------------------------------*)
    (* leftDecompose (__g, Q, __d, __d', P) = B

      if __g : Q and
         __d --> P  where __d might contain orders (lex and simul)

      then __d' --> P
           where all orders in __d' are atomic

      __d' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < __l

      __l := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = __l
      R := Root(n, Nil) | Lam(x:A, R)
      __l := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)
    (* less *)
    (* le *)
    (* eq *)
    (* drop assumption Pi D. P *)
    (*--------------------------------------------------------------*)
    (* Lexicographic and Simultanous Orders (left)*)
    (* If __d, __d', Lex O1, ....On < Lex O'1, ....O'n --> P
      then
            __d, __d', O1 < O1' --> P
        and __d, __d', O1 = O1', O2 < O2 --> P

        ...
        and __d, __d', O1 = O1', .., O_n-1 = O'n-1, O_n < O'n --> P
    *)
    (* If __d, __d', Lex O1, ....On = Lex O'1, ....O'n --> P
      If __d, __d', Simul O1, ....On = Simul O'1, ....O'n --> P
      then
            __d, __d', O1 = O1' --> P
        and __d, __d', O2 = O2' --> P

        ...
        and __d, __d', On = On' --> P
    *)
    (*--------------------------------------------------------------*)
    (* Atomic Orders (left) *)
    (* __u := Root(c, S) | Root(n, S) | Lam(x:A, __u) *)
    (* ltAtomicL (GQ as (__g, Q), __d, __d', ((__u, s1), (__v, s2)), ((__u', s1'), (__v', s2')), P) = B

     B holds iff

            __g : Q
       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']

       and  __g |- __d, __d', (__u[s1]:__v[s2]) < __u'[s1']:__v'[s2']) --> P


       if __g |- __d, __d', (__Us:__Vs) < (\x1:A1....\xn:An. __u'[s1']: __v'[s2']) --> P and
               (n >= 0)
       then
          __g, a1:A1, .... an:An |-
             __d^n, __d'^n, (__Us^n:__Vs^n) < __u'[a1... an . s1'^n]:__v'[a1. ... . an . s2'^n] --> P^n

       where __d^n, (__Us^n, P^n) means all substitutions in __d (__u, P etc)
             are shifted by n
    *)
    (* see invariant for ltAtomic *)
    (*  *)
    (*--------------------------------------------------------------*)
    (* __u' := Root(c, S) | Root(n, S) *)
    (* add definitions! *)
    (*  If __d, __d', __u < Root(c, S) --> P
      then __d, __d', __u <= S' --> P
   *)
    (*  eqL (GQ, __d, __d', UsVs, UsVs', P) = B

       B holds iff

            __g : Q

       and  __d is an Order relation ctx
       and  __d' is an atomic order relation ctx
       and  P is a order relation

       and  __g |- s1 : G1   G1 |- __u : V1
       and  __g |- s2 : G2   G2 |- __v : __l
       and  __g |- __u[s1] : __v[s2]
       and  __g |- s1' : G3   G3 |- __u' : V1'
       and  __g |- s2' : G4   G4 |- __v' : __l
       and  __g |- __u'[s1'] : __v'[s2']

       and __d, __d', __u[s1] = __u'[s1'] --> P

       note: __d, __d', UsVs, UsVs' and P do not
             contain any EVars
   *)
    (*
     | eqLW (GQ, __d, __d', UsVs as ((I.Root (I.BVar n, I.Nil), s), __Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), __Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, __d, __d', P)
         else
           leftDecompose (GQ, __d, (Eq(UsVs, UsVs') :: __d'), P)

*)
    (* UsVs = Lam *)
    (*--------------------------------------------------------------*)
    (* Infer: __d --> P *)
    (* deduce (__g, Q, __d, P) = B

      B iff
         __g :  Q
     and __g |- __d
     and __g |- P
     and __d implies P
    *)
    let deduce = deduce
    let shiftRCtx = shiftRCtx
    let shiftPred = shiftP
  end ;;
