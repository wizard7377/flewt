
module type CHECKING  =
  sig
    module Order : ORDER
    type __Quantifier =
      | All 
      | Exist 
      | And of Paths.occ 
    type 'a __Predicate =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.__Dec * 'a __Predicate) 
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.__Order
    type nonrec rctx = order __Predicate list
    type nonrec qctx = __Quantifier IntSyn.__Ctx
    val shiftRCtx : rctx -> (IntSyn.__Sub -> IntSyn.__Sub) -> rctx
    val shiftPred :
      order __Predicate ->
        (IntSyn.__Sub -> IntSyn.__Sub) -> order __Predicate
    val deduce : IntSyn.dctx -> qctx -> rctx -> order __Predicate -> bool
  end;;




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
                           module Origins : ORIGINS
                         end) : CHECKING =
  struct
    module Order = Order
    type __Quantifier =
      | All 
      | Exist 
      | And of Paths.occ 
    type 'a __Predicate =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.__Dec * 'a __Predicate) 
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.__Order
    type nonrec rctx = order __Predicate list
    type nonrec qctx = __Quantifier IntSyn.__Ctx
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    let rec atomicPredToString __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Less ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__G, (I.EClo __Us))) ^ " < ")
            Print.expToString (__G, (I.EClo __Us'))
      | (__G, Leq ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__G, (I.EClo __Us))) ^ " <= ")
            Print.expToString (__G, (I.EClo __Us'))
      | (__G, Eq ((__Us, _), (__Us', _))) ->
          (^) ((Print.expToString (__G, (I.EClo __Us))) ^ " = ")
            Print.expToString (__G, (I.EClo __Us'))
    let rec atomicRCtxToString __2__ __3__ =
      match (__2__, __3__) with
      | (__G, nil) -> " "
      | (__G, (__O)::nil) -> atomicPredToString (__G, __O)
      | (__G, (__O)::__D') ->
          (^) ((atomicRCtxToString (__G, __D')) ^ ", ") atomicPredToString
            (__G, __O)
    let rec shiftO __4__ __5__ =
      match (__4__, __5__) with
      | (Arg ((__U, us), (__V, vs)), f) ->
          R.Arg ((__U, (f us)), (__V, (f vs)))
      | (Lex (__L), f) -> R.Lex (map (fun (__O) -> shiftO __O f) __L)
      | (Simul (__L), f) -> R.Simul (map (fun (__O) -> shiftO __O f) __L)
    let rec shiftP __6__ __7__ =
      match (__6__, __7__) with
      | (Less (__O1, __O2), f) -> Less ((shiftO __O1 f), (shiftO __O2 f))
      | (Leq (__O1, __O2), f) -> Leq ((shiftO __O1 f), (shiftO __O2 f))
      | (Eq (__O1, __O2), f) -> Eq ((shiftO __O1 f), (shiftO __O2 f))
      | (Pi ((Dec (__X, __V) as D), __P), f) -> Pi (__D, (shiftP __P f))
    let rec shiftRCtx (Rl) f = map (fun p -> shiftP p f) Rl
    let rec shiftArg __8__ __9__ =
      match (__8__, __9__) with
      | (Less (((__U1, s1), (__V1, s1')), ((__U2, s2), (__V2, s2'))), f) ->
          Less
            (((__U1, (f s1)), (__V1, (f s1'))),
              ((__U2, (f s2)), (__V2, (f s2'))))
      | (Leq (((__U1, s1), (__V1, s1')), ((__U2, s2), (__V2, s2'))), f) ->
          Leq
            (((__U1, (f s1)), (__V1, (f s1'))),
              ((__U2, (f s2)), (__V2, (f s2'))))
      | (Eq (((__U1, s1), (__V1, s1')), ((__U2, s2), (__V2, s2'))), f) ->
          Eq
            (((__U1, (f s1)), (__V1, (f s1'))),
              ((__U2, (f s2)), (__V2, (f s2'))))
    let rec shiftACtx (Rl) f = map (fun p -> shiftArg p f) Rl
    let rec fmtOrder (__G) (__O) =
      let rec fmtOrder' =
        function
        | Arg (((__U, s) as Us), ((__V, s') as Vs)) ->
            F.Hbox
              [F.String "(";
              Print.formatExp (__G, (I.EClo __Us));
              F.String ")"]
        | Lex (__L) ->
            F.Hbox
              [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders __L); F.String "}"]
        | Simul (__L) ->
            F.Hbox
              [F.String "["; F.HOVbox0 1 0 1 (fmtOrders __L); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (__O)::[] -> (fmtOrder' __O) :: []
        | (__O)::__L -> (::) ((fmtOrder' __O) :: F.Break) fmtOrders __L in
      fmtOrder' __O
    let rec fmtComparison (__G) (__O) comp (__O') =
      F.HOVbox0 1 0 1
        [fmtOrder (__G, __O);
        F.Break;
        F.String comp;
        F.Break;
        fmtOrder (__G, __O')]
    let rec fmtPredicate' __10__ __11__ =
      match (__10__, __11__) with
      | (__G, Less (__O, __O')) -> fmtComparison (__G, __O, "<", __O')
      | (__G, Leq (__O, __O')) -> fmtComparison (__G, __O, "<=", __O')
      | (__G, Eq (__O, __O')) -> fmtComparison (__G, __O, "=", __O')
      | (__G, Pi (__D, __P)) ->
          F.Hbox [F.String "Pi "; fmtPredicate' ((I.Decl (__G, __D)), __P)]
      (* F.String "Pi predicate"  *)
    let rec fmtPredicate (__G) (__P) =
      fmtPredicate' ((Names.ctxName __G), __P)
    let rec fmtRGCtx' __12__ __13__ =
      match (__12__, __13__) with
      | (__G, nil) -> ""
      | (__G, (__P)::[]) -> F.makestring_fmt (fmtPredicate' (__G, __P))
      | (__G, (__P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate' (__G, __P))) ^ " ,")
            fmtRGCtx' (__G, Rl)
    let rec fmtRGCtx (__G) (Rl) = fmtRGCtx' ((Names.ctxName __G), Rl)
    let rec init () = true
    let rec eqCid c c' = c = c'
    let rec conv (__Us, __Vs) (__Us', __Vs') =
      (Conv.conv (__Vs, __Vs')) && (Conv.conv (__Us, __Us'))
    let rec isUniversal =
      function | All -> true | Exist -> false | Exist' -> false
    let rec isExistential =
      function | All -> false | Exist -> true | Exist' -> true
    let rec isParameter (__Q) (__X) =
      isParameterW (__Q, (Whnf.whnf (__X, I.id)))
    let rec isParameterW (__Q) (__Us) =
      try isUniversal (I.ctxLookup (__Q, (Whnf.etaContract (I.EClo __Us))))
      with | Whnf.Eta -> isFreeEVar __Us
    let rec isFreeEVar __14__ __15__ =
      match (__14__, __15__) with
      | (EVar (_, _, _, { contents = [] }), _) -> true
      | (Lam (__D, __U), s) -> isFreeEVar (Whnf.whnf (__U, (I.dot1 s)))
      | _ -> false(* constraints must be empty *)
    let rec isAtomic (GQ) (__Us) = isAtomicW (GQ, (Whnf.whnf __Us))
    let rec isAtomicW __16__ __17__ =
      match (__16__, __17__) with
      | (GQ, ((Root (Const c, __S) as X), s)) -> isAtomicS (GQ, (__S, s))
      | (GQ, ((Root (Def c, __S) as X), s)) -> isAtomicS (GQ, (__S, s))
      | (((__G, __Q) as GQ), ((Root (BVar n, __S) as X), s)) ->
          (isExistential (I.ctxLookup (__Q, n))) ||
            (isAtomicS (GQ, (__S, s)))
      | (GQ, _) -> false(*      | isAtomicW (GQ, (X as (I.EClo _))) = true    existential var *)
      (* should disallow orelse ? *)
    let rec isAtomicS __18__ __19__ =
      match (__18__, __19__) with
      | (GQ, (I.Nil, _)) -> true
      | (GQ, (SClo (__S, s'), s'')) ->
          isAtomicS (GQ, (__S, (I.comp (s', s''))))
      | (GQ, (App (__U', __S'), s1')) -> false
    let rec eq (__G) (__Us, __Vs) (__Us', __Vs') =
      (Unify.unifiable (__G, __Vs, __Vs')) &&
        (Unify.unifiable (__G, __Us, __Us'))
    let rec lookupEq __20__ __21__ __22__ __23__ __24__ =
      match (__20__, __21__, __22__, __23__, __24__) with
      | (GQ, nil, UsVs, UsVs', sc) -> false
      | (GQ, (Less (_, _))::__D, UsVs, UsVs', sc) ->
          lookupEq (GQ, __D, UsVs, UsVs', sc)
      | (((__G, __Q) as GQ), (Eq (UsVs1, UsVs1'))::__D, UsVs, UsVs', sc) ->
          (CSManager.trail
             (fun () ->
                (eq (__G, UsVs1, UsVs)) &&
                  ((eq (__G, UsVs1', UsVs')) && (sc ()))))
            ||
            ((CSManager.trail
                (fun () ->
                   (eq (__G, UsVs1, UsVs')) &&
                     ((eq (__G, UsVs1', UsVs)) && (sc ()))))
               || (lookupEq (GQ, __D, UsVs, UsVs', sc)))
    let rec lookupLt __25__ __26__ __27__ __28__ __29__ =
      match (__25__, __26__, __27__, __28__, __29__) with
      | (GQ, nil, UsVs, UsVs', sc) -> false
      | (GQ, (Eq (_, _))::__D, UsVs, UsVs', sc) ->
          lookupLt (GQ, __D, UsVs, UsVs', sc)
      | (((__G, __Q) as GQ), (Less (UsVs1, UsVs1'))::__D, UsVs, UsVs', sc) ->
          (CSManager.trail
             (fun () ->
                (eq (__G, UsVs1, UsVs)) &&
                  ((eq (__G, UsVs1', UsVs')) && (sc ()))))
            || (lookupLt (GQ, __D, UsVs, UsVs', sc))
    let rec eqAtomic __30__ __31__ __32__ __33__ __34__ __35__ =
      match (__30__, __31__, __32__, __33__, __34__, __35__) with
      | (((__G, __Q) as GQ), nil, __D', UsVs, UsVs', sc) ->
          (CSManager.trail (fun () -> (eq (__G, UsVs, UsVs')) && (sc ()))) ||
            (lookupEq (GQ, __D', UsVs, UsVs', sc))
      | (((__G, __Q) as GQ), __D, __D', UsVs, UsVs', sc) ->
          (CSManager.trail (fun () -> (eq (__G, UsVs, UsVs')) && (sc ()))) ||
            ((lookupEq (GQ, __D, UsVs, UsVs', sc)) ||
               ((lookupEq (GQ, __D', UsVs, UsVs', sc)) ||
                  (transEq (GQ, __D, __D', UsVs, UsVs', sc))))
    let rec transEq __36__ __37__ __38__ __39__ __40__ __41__ =
      match (__36__, __37__, __38__, __39__, __40__, __41__) with
      | (((__G, __Q) as GQ), nil, __D, UsVs, UsVs', sc) -> false
      | (((__G, __Q) as GQ), (Eq (UsVs1, UsVs1'))::__D, __D', UsVs, UsVs',
         sc) ->
          (CSManager.trail
             (fun () ->
                (eq (__G, UsVs1', UsVs')) &&
                  ((sc ()) &&
                     (eqAtomicR (GQ, (__D @ __D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (fun () ->
                   (eq (__G, UsVs1, UsVs')) &&
                     ((sc ()) &&
                        (eqAtomicR
                           (GQ, (__D @ __D'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transEq
                  (GQ, __D, ((Eq (UsVs1, UsVs1')) :: __D'), UsVs, UsVs', sc)))
      | (((__G, __Q) as GQ), (Less (UsVs1, UsVs1'))::__D, __D', UsVs, UsVs',
         sc) -> transEq (GQ, __D, __D', UsVs, UsVs', sc)
    let rec ltAtomic __42__ __43__ __44__ __45__ __46__ __47__ =
      match (__42__, __43__, __44__, __45__, __46__, __47__) with
      | (((__G, __Q) as GQ), nil, __D', UsVs, UsVs', sc) ->
          lookupLt (GQ, __D', UsVs, UsVs', sc)
      | (((__G, __Q) as GQ), __D, __D', UsVs, UsVs', sc) ->
          (lookupLt (GQ, __D, UsVs, UsVs', sc)) ||
            ((lookupLt (GQ, __D', UsVs, UsVs', sc)) ||
               (transLt (GQ, __D, __D', UsVs, UsVs', sc)))
    let rec transLt __48__ __49__ __50__ __51__ __52__ __53__ =
      match (__48__, __49__, __50__, __51__, __52__, __53__) with
      | (((__G, __Q) as GQ), nil, __D, UsVs, UsVs', sc) -> false
      | (((__G, __Q) as GQ), (Eq (UsVs1, UsVs1'))::__D, __D', UsVs, UsVs',
         sc) ->
          (CSManager.trail
             (fun () ->
                (eq (__G, UsVs1', UsVs')) &&
                  ((sc ()) &&
                     (ltAtomicR (GQ, (__D @ __D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (fun () ->
                   (eq (__G, UsVs1, UsVs')) &&
                     ((sc ()) &&
                        (ltAtomicR
                           (GQ, (__D @ __D'), UsVs, UsVs1', sc, atomic)))))
               ||
               (transLt
                  (GQ, __D, ((Eq (UsVs1, UsVs1')) :: __D'), UsVs, UsVs', sc)))
      | (((__G, __Q) as GQ), (Less (UsVs1, UsVs1'))::__D, __D', UsVs, UsVs',
         sc) ->
          (CSManager.trail
             (fun () ->
                (eq (__G, UsVs1', UsVs')) &&
                  ((sc ()) &&
                     (eqAtomicR (GQ, (__D @ __D'), UsVs, UsVs1, sc, atomic)))))
            ||
            ((CSManager.trail
                (fun () ->
                   (eq (__G, UsVs1', UsVs')) &&
                     ((sc ()) &&
                        (ltAtomicR
                           (GQ, (__D @ __D'), UsVs, UsVs1, sc, atomic)))))
               ||
               (transLt
                  (GQ, __D, ((Less (UsVs1, UsVs1')) :: __D'), UsVs, UsVs',
                    sc)))
    let rec atomic __54__ __55__ __56__ __57__ __58__ =
      match (__54__, __55__, __56__, __57__, __58__) with
      | (GQ, __D, __D', Eq (UsVs, UsVs'), sc) ->
          eqAtomic (GQ, __D, __D', UsVs, UsVs', sc)
      | (GQ, __D, __D', Less (UsVs, UsVs'), sc) ->
          ltAtomic (GQ, __D, __D', UsVs, UsVs', sc)
    let rec leftInstantiate __59__ __60__ __61__ __62__ __63__ =
      match (__59__, __60__, __61__, __62__, __63__) with
      | (((__G, __Q) as GQ), nil, __D', __P, sc) ->
          ((if atomic (GQ, __D', nil, __P, sc)
            then
              (if (!Global.chatter) > 4
               then
                 print
                   (((^) (((^) " Proved: " atomicRCtxToString (__G, __D')) ^
                            " ---> ")
                       atomicPredToString (__G, __P))
                      ^ "\n")
               else ();
               true)
            else false)
          (* should never happen by invariant *))
      | (GQ, (Less (UsVs, UsVs'))::__D, __D', __P, sc) ->
          ltInstL (GQ, __D, __D', UsVs, UsVs', __P, sc)
      | (GQ, (Leq (UsVs, UsVs'))::__D, __D', __P, sc) ->
          leInstL (GQ, __D, __D', UsVs, UsVs', __P, sc)
      | (GQ, (Eq (UsVs, UsVs'))::__D, __D', __P, sc) ->
          eqInstL (GQ, __D, __D', UsVs, UsVs', __P, sc)
    let rec ltInstL (GQ) (__D) (__D') (UsVs) (UsVs') (__P') sc =
      ltInstLW (GQ, __D, __D', (Whnf.whnfEta UsVs), UsVs', __P', sc)
    let rec ltInstLW __64__ __65__ __66__ __67__ __68__ __69__ __70__ =
      match (__64__, __65__, __66__, __67__, __68__, __69__, __70__) with
      | (((__G, __Q) as GQ), __D, __D',
         ((Lam ((Dec (_, __V1) as Dec), __U), s1),
          (Pi ((Dec (_, __V2), _), __V), s2)),
         ((__U', s1'), (__V', s2')), __P', sc) ->
          ((if Subordinate.equiv ((I.targetFam __V'), (I.targetFam __V1))
            then
              let __X = I.newEVar (__G, (I.EClo (__V1, s1))) in
              let sc' () = (isParameter (__Q, __X)) && (sc ()) in
              ((ltInstL
                  ((__G, __Q), __D, __D',
                    ((__U, (I.Dot ((I.Exp __X), s1))),
                      (__V, (I.Dot ((I.Exp __X), s2)))),
                    ((__U', s1'), (__V', s2')), __P', sc'))
                (* = I.newEVar (I.EClo (V2', s2')) *)
                (* enforces that X can only bound to parameter or remain uninstantiated *))
            else
              if Subordinate.below ((I.targetFam __V1), (I.targetFam __V'))
              then
                (let __X = I.newEVar (__G, (I.EClo (__V1, s1))) in
                 ((ltInstL
                     ((__G, __Q), __D, __D',
                       ((__U, (I.Dot ((I.Exp __X), s1))),
                         (__V, (I.Dot ((I.Exp __X), s2)))),
                       ((__U', s1'), (__V', s2')), __P', sc))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else false)
          (* == I.targetFam V2' *))
      | (GQ, __D, __D', UsVs, UsVs', __P', sc) ->
          leftInstantiate (GQ, __D, ((Less (UsVs, UsVs')) :: __D'), __P', sc)
      (* impossible, if additional invariant assumed (see ltW) *)
    let rec leInstL (GQ) (__D) (__D') (UsVs) (UsVs') (__P') sc =
      leInstLW (GQ, __D, __D', (Whnf.whnfEta UsVs), UsVs', __P', sc)
    let rec leInstLW __71__ __72__ __73__ __74__ __75__ __76__ __77__ =
      match (__71__, __72__, __73__, __74__, __75__, __76__, __77__) with
      | (((__G, __Q) as GQ), __D, __D',
         ((Lam (Dec (_, __V1), __U), s1), (Pi ((Dec (_, __V2), _), __V), s2)),
         ((__U', s1'), (__V', s2')), __P', sc) ->
          ((if Subordinate.equiv ((I.targetFam __V'), (I.targetFam __V1))
            then
              let __X = I.newEVar (__G, (I.EClo (__V1, s1))) in
              let sc' () = (isParameter (__Q, __X)) && (sc ()) in
              ((leInstL
                  ((__G, __Q), __D, __D',
                    ((__U, (I.Dot ((I.Exp __X), s1))),
                      (__V, (I.Dot ((I.Exp __X), s2)))),
                    ((__U', s1'), (__V', s2')), __P', sc'))
                (* = I.newEVar (I.EClo (V2', s2')) *)
                (* enforces that X can only bound to parameter or remain uninstantiated *))
            else
              if Subordinate.below ((I.targetFam __V1), (I.targetFam __V'))
              then
                (let __X = I.newEVar (__G, (I.EClo (__V1, s1))) in
                 ((leInstL
                     ((__G, __Q), __D, __D',
                       ((__U, (I.Dot ((I.Exp __X), s1))),
                         (__V, (I.Dot ((I.Exp __X), s2)))),
                       ((__U', s1'), (__V', s2')), __P', sc))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else false)
          (* == I.targetFam V2' *))
      | (GQ, __D, __D', UsVs, UsVs', __P, sc) ->
          leftInstantiate (GQ, __D, ((Less (UsVs, UsVs')) :: __D'), __P, sc)
      (* impossible, if additional invariant assumed (see ltW) *)
    let rec eqInstL (GQ) (__D) (__D') (UsVs) (UsVs') (__P') sc =
      eqInstLW
        (GQ, __D, __D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), __P', sc)
    let rec eqInstLW __78__ __79__ __80__ __81__ __82__ __83__ __84__ =
      match (__78__, __79__, __80__, __81__, __82__, __83__, __84__) with
      | (((__G, __Q) as GQ), __D, __D',
         ((Lam (Dec (_, V1'), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         ((Lam (Dec (_, V1''), U''), s1''),
          (Pi ((Dec (_, V2''), _), V''), s2'')),
         __P', sc) ->
          let __X = I.newEVar (__G, (I.EClo (V1'', s1''))) in
          ((eqInstL
              (GQ, __D, __D',
                ((__U', (I.Dot ((I.Exp __X), s1'))),
                  (__V', (I.Dot ((I.Exp __X), s2')))),
                ((U'', (I.Dot ((I.Exp __X), s1''))),
                  (V'', (I.Dot ((I.Exp __X), s2'')))), __P',
                (fun () -> isParameter (__Q, __X); sc ())))
            (* = I.newEVar (I.EClo (V2', s2')) *))
      | (GQ, __D, __D', UsVs, UsVs', __P', sc) ->
          eqIL (GQ, __D, __D', UsVs, UsVs', __P', sc)
    let rec eqIL __85__ __86__ __87__ __88__ __89__ __90__ __91__ =
      match (__85__, __86__, __87__, __88__, __89__, __90__, __91__) with
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (Const c, __S), s), __Vs) as UsVs),
         (((Root (Const c', __S'), s'), __Vs') as UsVs'), __P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, __D, __D', ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G, ((Eq (UsVs, UsVs')) :: __D)))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (Def c, __S), s), __Vs) as UsVs),
         (((Root (Def c', __S'), s'), __Vs') as UsVs'), __P', sc) ->
          if eqCid (c, c')
          then
            eqSpineIL
              (GQ, __D, __D', ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), __P', sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G, ((Eq (UsVs, UsVs')) :: __D)))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (Const c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us')
          then
            leftInstantiate
              (GQ, __D, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __D'), __P',
                sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G,
                                  ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D)))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (Def c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us')
          then
            leftInstantiate
              (GQ, __D, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __D'), __P',
                sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G,
                                  ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D)))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Def c, __S'), s') as Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us)
          then
            leftInstantiate
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P',
                sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G,
                                  ((Eq ((__Us, __Vs), (__Us', __Vs'))) ::
                                     __D')))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Const c, __S'), s') as Us'), __Vs'), __P', sc) ->
          if isAtomic (GQ, __Us)
          then
            leftInstantiate
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P',
                sc)
          else
            (if (!Global.chatter) > 4
             then
               print
                 (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                (__G,
                                  ((Eq ((__Us, __Vs), (__Us', __Vs'))) ::
                                     __D')))
                           atomicRCtxToString (__G, __D'))
                          ^ " ---> ")
                     atomicPredToString (__G, __P'))
                    ^ "\n")
             else ();
             true)
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (BVar n', __S'), s') as Us'), __Vs'), __P', sc) ->
          if n = n'
          then
            let Dec (_, __V') = I.ctxDec (__G, n) in
            eqSpineIL
              (GQ, __D, __D', ((__S, s), (__V', I.id)),
                ((__S', s'), (__V', I.id)), __P', sc)
          else
            leftInstantiate
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P',
                sc)
      | (((__G, __Q) as GQ), __D, __D', UsVs, UsVs', __P', sc) ->
          (if (!Global.chatter) > 4
           then
             print
               (((^) (((^) ((^) " Proved: " atomicRCtxToString
                              (__G, ((Eq (UsVs, UsVs')) :: __D)))
                         atomicRCtxToString (__G, __D'))
                        ^ " ---> ")
                   atomicPredToString (__G, __P'))
                  ^ "\n")
           else ();
           true)(* (Us, Vs as (I.Pi _ , _)) and (Us', Vs' as (I.Root _, _))
           or the other way
         *)
    let rec eqSpineIL (GQ) (__D) (__D') (__Ss, __Vs) (__Ss', __Vs') (__P') sc
      =
      eqSpineILW
        (GQ, __D, __D', (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')),
          __P', sc)
    let rec eqSpineILW __92__ __93__ __94__ __95__ __96__ __97__ __98__ =
      match (__92__, __93__, __94__, __95__, __96__, __97__, __98__) with
      | (GQ, __D, __D', ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), __P', sc)
          -> leftInstantiate (GQ, __D, __D', __P', sc)
      | (GQ, __D, __D', ((SClo (__S, s'), s''), __Vs), SsVs', __P', sc) ->
          eqSpineIL
            (GQ, __D, __D', ((__S, (I.comp (s', s''))), __Vs), SsVs', __P',
              sc)
      | (GQ, __D, __D', SsVs, ((SClo (__S', s'), s''), __Vs'), __P', sc) ->
          eqSpineIL
            (GQ, __D, __D', SsVs, ((__S', (I.comp (s', s''))), __Vs'), __P',
              sc)
      | (GQ, __D, __D',
         ((App (__U, __S), s1), (Pi ((Dec (_, __V1), _), __V2), s2)),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), __P',
         sc) ->
          let __D1 =
            (Eq (((__U, s1), (__V1, s2)), ((__U', s1'), (V1', s2')))) :: __D in
          eqSpineIL
            (GQ, __D1, __D',
              ((__S, s1), (__V2, (I.Dot ((I.Exp (I.EClo (__U, s1))), s2)))),
              ((__S', s1'),
                (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), __P',
              sc)
    let rec rightDecompose __99__ __100__ __101__ =
      match (__99__, __100__, __101__) with
      | (GQ, __D', Less (__O, __O')) -> ordLtR (GQ, __D', __O, __O')
      | (GQ, __D', Leq (__O, __O')) -> ordLeR (GQ, __D', __O, __O')
      | (GQ, __D', Eq (__O, __O')) -> ordEqR (GQ, __D', __O, __O')
    let rec ordLtR __102__ __103__ __104__ __105__ =
      match (__102__, __103__, __104__, __105__) with
      | (GQ, __D', Arg (UsVs), Arg (UsVs')) ->
          ltAtomicR (GQ, __D', UsVs, UsVs', init, leftInstantiate)
      | (GQ, __D', Lex (__O), Lex (__O')) -> ltLexR (GQ, __D', __O, __O')
      | (GQ, __D', Simul (__O), Simul (__O')) ->
          ltSimulR (GQ, __D', __O, __O')
    let rec ordLeR __106__ __107__ __108__ __109__ =
      match (__106__, __107__, __108__, __109__) with
      | (GQ, __D', Arg (UsVs), Arg (UsVs')) ->
          leAtomicR (GQ, __D', UsVs, UsVs', init, leftInstantiate)
      | (GQ, __D', Lex (__O), Lex (__O')) ->
          (ltLexR (GQ, __D', __O, __O')) || (ordEqsR (GQ, __D', __O, __O'))
      | (GQ, __D', Simul (__O), Simul (__O')) ->
          leSimulR (GQ, __D', __O, __O')
    let rec ordEqR __110__ __111__ __112__ __113__ =
      match (__110__, __111__, __112__, __113__) with
      | (GQ, __D', Arg (UsVs), Arg (UsVs')) ->
          (conv (UsVs, UsVs')) ||
            (eqAtomicR (GQ, __D', UsVs, UsVs', init, leftInstantiate))
      | (GQ, __D', Lex (__O), Lex (__O')) -> ordEqsR (GQ, __D', __O, __O')
      | (GQ, __D', Simul (__O), Simul (__O')) ->
          ordEqsR (GQ, __D', __O, __O')
    let rec ordEqsR __114__ __115__ __116__ __117__ =
      match (__114__, __115__, __116__, __117__) with
      | (GQ, __D', nil, nil) -> true
      | (GQ, __D', (__O)::__L, (__O')::__L') ->
          (ordEqR (GQ, __D', __O, __O')) && (ordEqsR (GQ, __D', __L, __L'))
    let rec ltLexR __118__ __119__ __120__ __121__ =
      match (__118__, __119__, __120__, __121__) with
      | (GQ, __D', nil, nil) -> false
      | (GQ, __D', (__O)::__L, (__O')::__L') ->
          (ordLtR (GQ, __D', __O, __O')) ||
            ((ordEqR (GQ, __D', __O, __O')) && (ltLexR (GQ, __D', __L, __L')))
    let rec leLexR (GQ) (__D') (__L) (__L') =
      (ltLexR (GQ, __D', __L, __L')) || (ordEqsR (GQ, __D', __L, __L'))
    let rec ltSimulR __122__ __123__ __124__ __125__ =
      match (__122__, __123__, __124__, __125__) with
      | (GQ, __D, nil, nil) -> false
      | (GQ, __D, (__O)::__L, (__O')::__L') ->
          ((ordLtR (GQ, __D, __O, __O')) && (leSimulR (GQ, __D, __L, __L')))
            ||
            ((ordEqR (GQ, __D, __O, __O')) && (ltSimulR (GQ, __D, __L, __L')))
    let rec leSimulR __126__ __127__ __128__ __129__ =
      match (__126__, __127__, __128__, __129__) with
      | (GQ, __D, nil, nil) -> true
      | (GQ, __D, (__O)::__L, (__O')::__L') ->
          (ordLeR (GQ, __D, __O, __O')) && (leSimulR (GQ, __D, __L, __L'))
    let rec ltAtomicR (GQ) (__D) (UsVs) (UsVs') sc k =
      ltAtomicRW (GQ, __D, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec ltAtomicRW __130__ __131__ __132__ __133__ __134__ __135__ =
      match (__130__, __131__, __132__, __133__, __134__, __135__) with
      | (GQ, __D, ((__Us, ((Root _, s') as Vs)) as UsVs), UsVs', sc, k) ->
          ltR (GQ, __D, UsVs, UsVs', sc, k)
      | (((__G, __Q) as GQ), __D,
         ((Lam (_, __U), s1), (Pi ((Dec, _), __V), s2)),
         ((__U', s1'), (__V', s2')), sc, k) ->
          let UsVs' =
            ((__U', (I.comp (s1', I.shift))),
              (__V', (I.comp (s2', I.shift)))) in
          let UsVs = ((__U, (I.dot1 s1)), (__V, (I.dot1 s2))) in
          let __D' = shiftACtx __D (fun s -> I.comp (s, I.shift)) in
          ltAtomicR
            (((I.Decl (__G, (N.decLUName (__G, (I.decSub (Dec, s2)))))),
               (I.Decl (__Q, All))), __D', UsVs, UsVs', sc, k)
    let rec leAtomicR (GQ) (__D) (UsVs) (UsVs') sc k =
      leAtomicRW (GQ, __D, (Whnf.whnfEta UsVs), UsVs', sc, k)
    let rec leAtomicRW __136__ __137__ __138__ __139__ __140__ __141__ =
      match (__136__, __137__, __138__, __139__, __140__, __141__) with
      | (GQ, __D, ((__Us, ((Root _, s') as Vs)) as UsVs), UsVs', sc, k) ->
          leR (GQ, __D, UsVs, UsVs', sc, k)
      | (((__G, __Q) as GQ), __D,
         ((Lam (_, __U), s1), (Pi ((Dec, _), __V), s2)),
         ((__U', s1'), (__V', s2')), sc, k) ->
          let __D' = shiftACtx __D (fun s -> I.comp (s, I.shift)) in
          let UsVs' =
            ((__U', (I.comp (s1', I.shift))),
              (__V', (I.comp (s2', I.shift)))) in
          let UsVs = ((__U, (I.dot1 s1)), (__V, (I.dot1 s2))) in
          leAtomicR
            (((I.Decl (__G, (N.decLUName (__G, (I.decSub (Dec, s2)))))),
               (I.Decl (__Q, All))), __D', UsVs, UsVs', sc, k)
    let rec eqAtomicR ((__G, __Q) as GQ) (__D) (UsVs) (UsVs') sc k =
      eqAtomicRW (GQ, __D, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), sc, k)
    let rec eqAtomicRW __142__ __143__ __144__ __145__ __146__ __147__ =
      match (__142__, __143__, __144__, __145__, __146__, __147__) with
      | (((__G, __Q) as GQ), __D,
         ((Lam (_, __U), s1), (Pi ((Dec, _), __V), s2)),
         ((Lam (_, __U'), s1'), (Pi ((Dec', _), __V'), s2')), sc, k) ->
          eqAtomicR
            (((I.Decl (__G, (N.decLUName (__G, (I.decSub (Dec, s2)))))),
               (I.Decl (__Q, All))),
              (shiftACtx __D (fun s -> I.comp (s, I.shift))),
              ((__U, (I.dot1 s1')), (__V, (I.dot1 s2'))),
              ((__U', (I.dot1 s1')), (__V', (I.dot1 s2'))), sc, k)
      | (GQ, __D, (__Us, ((Root _, s2) as Vs)),
         (__Us', ((Root _, s2') as Vs')), sc, k) ->
          eqR (GQ, __D, (__Us, __Vs), (__Us', __Vs'), sc, k)
      | (GQ, __D, (__Us, __Vs), (__Us', __Vs'), sc, k) -> false(* Fri Feb 25 21:26:39 2005 -fp !!! *)
      (* mismatch: not equal *)(* Dec = Dec' *)
    let rec ltR ((__G, __Q) as GQ) (__D) (UsVs) (UsVs') sc k =
      ltRW (GQ, __D, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec ltRW __148__ __149__ __150__ __151__ __152__ __153__ =
      match (__148__, __149__, __150__, __151__, __152__, __153__) with
      | (GQ, __D, (__Us, __Vs), (((Root (Const c, __S'), s') as Us'), __Vs'),
         sc, k) ->
          ((if isAtomic (GQ, __Us')
            then k (GQ, __D, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
            else
              ltSpineR
                (GQ, __D, (__Us, __Vs),
                  ((__S', s'), ((I.constType c), I.id)), sc, k))
          (* either leftInstantiate D or  atomic reasoning *))
      | (GQ, __D, (__Us, __Vs), (((Root (Def c, __S'), s') as Us'), __Vs'),
         sc, k) ->
          ((if isAtomic (GQ, __Us')
            then k (GQ, __D, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
            else
              ltSpineR
                (GQ, __D, (__Us, __Vs),
                  ((__S', s'), ((I.constType c), I.id)), sc, k))
          (* either leftInstantiate D or  atomic reasoning *))
      | (((__G, __Q) as GQ), __D, (__Us, __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), sc, k) ->
          ((if isAtomic (GQ, __Us')
            then k (GQ, __D, nil, (Less ((__Us, __Vs), (__Us', __Vs'))), sc)
            else
              (let Dec (_, __V') = I.ctxDec (__G, n) in
               ltSpineR
                 (GQ, __D, (__Us, __Vs), ((__S', s'), (__V', I.id)), sc, k)))
          (* either leftInstantiate D or  atomic reasoning *))
      | (GQ, __D, _, ((EVar _, _), _), _, _) -> false
      | (((__G, __Q) as GQ), __D, ((__U, s1), (__V, s2)),
         ((Lam (Dec (_, V1'), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, k) ->
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' () = isParameter (__Q, __X); sc () in
              ((ltR
                  (GQ, __D, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', k))
                (* enforce that X is only instantiated to parameters *)
                (* = I.newEVar (I.EClo (V2', s2')) *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 ((ltR
                     (GQ, __D, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc, k))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else false)
          (* == I.targetFam V2' *))
    let rec ltSpineR (GQ) (__D) (__Us, __Vs) (__Ss', __Vs') sc k =
      ltSpineRW (GQ, __D, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, k)
    let rec ltSpineRW __154__ __155__ __156__ __157__ __158__ __159__ =
      match (__154__, __155__, __156__, __157__, __158__, __159__) with
      | (GQ, __D, (__Us, __Vs), ((I.Nil, _), _), _, _) -> false
      | (GQ, __D, (__Us, __Vs), ((SClo (__S, s'), s''), __Vs'), sc, k) ->
          ltSpineR
            (GQ, __D, (__Us, __Vs), ((__S, (I.comp (s', s''))), __Vs'), sc,
              k)
      | (GQ, __D, (__Us, __Vs),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc,
         k) ->
          (leAtomicR
             (GQ, __D, (__Us, __Vs), ((__U', s1'), (V1', s2')), sc, k))
            ||
            (ltSpineR
               (GQ, __D, (__Us, __Vs),
                 ((__S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), sc,
                 k))(* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
    let rec leR (GQ) (__D) (UsVs) (UsVs') sc k =
      leRW (GQ, __D, UsVs, (Whnf.whnfEta UsVs'), sc, k)
    let rec leRW __160__ __161__ __162__ __163__ __164__ __165__ =
      match (__160__, __161__, __162__, __163__, __164__, __165__) with
      | (((__G, __Q) as GQ), __D, ((__U, s1), (__V, s2)),
         ((Lam (Dec (_, V1'), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, k) ->
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' () = (isParameter (__Q, __X)) && (sc ()) in
              ((leR
                  (GQ, __D, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', k))
                (* = I.newEVar (I.EClo (V2', s2')) *)
                (* enforces that X can only bound to parameter or remain uninstantiated *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 ((leR
                     (GQ, __D, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc, k))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else false)
          (* == I.targetFam V2' *))
      | (GQ, __D, UsVs, UsVs', sc, k) ->
          (ltR (GQ, __D, UsVs, UsVs', sc, k)) ||
            (eqR (GQ, __D, UsVs, UsVs', sc, k))(* impossible, if additional invariant assumed (see ltW) *)
    let rec eqR ((__G, __Q) as GQ) (__D) (UsVs) (UsVs') sc k =
      (CSManager.trail (fun () -> (eq (__G, UsVs, UsVs')) && (sc ()))) ||
        (eqR' (GQ, __D, UsVs, UsVs', sc, k))
    let rec eqR' __166__ __167__ __168__ __169__ __170__ __171__ =
      match (__166__, __167__, __168__, __169__, __170__, __171__) with
      | (GQ, __D, (__Us, ((Pi ((Dec (_, V2'), _), __V'), s2') as Vs)),
         (__Us', ((Root _, s2'') as Vs')), sc, k) -> false
      | (GQ, __D, (__Us, ((Root _, s2') as Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), sc, k) ->
          false
      | (GQ, __D, (((Root (Const c, __S), s), __Vs) as UsVs),
         (((Root (Const c', __S'), s'), __Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, __D, ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), sc, k)
          else false
      | (GQ, __D, (((Root (Const c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), sc, k) ->
          ((if isAtomic (GQ, __Us')
            then k (GQ, __D, nil, (Eq ((__Us', __Vs'), (__Us, __Vs))), sc)
            else false)
          (* either leftInstantiate D or atomic reasoning *))
      | (GQ, __D, (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Const c, __S'), s') as Us'), __Vs'), sc, k) ->
          ((if isAtomic (GQ, __Us)
            then k (GQ, __D, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
            else false)
          (* either leftInstantiate D or atomic reasoning *))
      | (GQ, __D, (((Root (Def c, __S), s), __Vs) as UsVs),
         (((Root (Def c', __S'), s'), __Vs') as UsVs'), sc, k) ->
          if eqCid (c, c')
          then
            eqSpineR
              (GQ, __D, ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), sc, k)
          else false
      | (GQ, __D, (((Root (Def c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), sc, k) ->
          ((if isAtomic (GQ, __Us')
            then k (GQ, __D, nil, (Eq ((__Us', __Vs'), (__Us, __Vs))), sc)
            else false)
          (* either leftInstantiate D or atomic reasoning *))
      | (GQ, __D, (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Def c, __S'), s') as Us'), __Vs'), sc, k) ->
          ((if isAtomic (GQ, __Us)
            then k (GQ, __D, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
            else false)
          (* either leftInstantiate D or atomic reasoning *))
      | (((__G, __Q) as GQ), __D, (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (BVar n', __S'), s') as Us'), __Vs'), sc, k) ->
          if n = n'
          then
            let Dec (_, __V') = I.ctxDec (__G, n) in
            eqSpineR
              (GQ, __D, ((__S, s), (__V', I.id)), ((__S', s'), (__V', I.id)),
                sc, k)
          else k (GQ, __D, nil, (Eq ((__Us, __Vs), (__Us', __Vs'))), sc)
      | (GQ, __D, UsVs, UsVs', sc, k) ->
          k (GQ, __D, nil, (Eq (UsVs, UsVs')), sc)(* UsVs = Lam *)
      (* either leftInstantiate D or atomic reasoning *)
    let rec eqSpineR (GQ) (__D) (__Ss, __Vs) (__Ss', __Vs') sc k =
      eqSpineRW
        (GQ, __D, (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')), sc,
          k)
    let rec eqSpineRW __172__ __173__ __174__ __175__ __176__ __177__ =
      match (__172__, __173__, __174__, __175__, __176__, __177__) with
      | (GQ, __D, ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), sc, k) -> true
      | (GQ, __D, ((SClo (__S, s'), s''), __Vs), SsVs', sc, k) ->
          eqSpineR (GQ, __D, ((__S, (I.comp (s', s''))), __Vs), SsVs', sc, k)
      | (GQ, __D, SsVs, ((SClo (__S', s'), s''), __Vs'), sc, k) ->
          eqSpineR
            (GQ, __D, SsVs, ((__S', (I.comp (s', s''))), __Vs'), sc, k)
      | (GQ, __D,
         ((App (__U, __S), s1), (Pi ((Dec (_, __V1), _), __V2), s2)),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc,
         k) ->
          (eqAtomicR
             (GQ, __D, ((__U, s1), (__V1, s2)), ((__U', s1'), (V1', s2')),
               sc, k))
            &&
            (eqSpineR
               (GQ, __D,
                 ((__S, s1),
                   (__V2, (I.Dot ((I.Exp (I.EClo (__U, s1))), s2)))),
                 ((__S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), sc,
                 k))
      | (GQ, __D, SsVs, SsVs', sc, k) -> false
    let rec leftDecompose __178__ __179__ __180__ __181__ =
      match (__178__, __179__, __180__, __181__) with
      | (((__G, __Q) as GQ), nil, __D', __P) ->
          rightDecompose (GQ, __D', __P)
      | (GQ, (Less (Arg (UsVs), Arg (UsVs')))::__D, __D', __P) ->
          ltAtomicL (GQ, __D, __D', UsVs, UsVs', __P)
      | (GQ, (Less (Lex (__O), Lex (__O')))::__D, __D', __P) ->
          ltLexL (GQ, __D, __D', __O, __O', __P)
      | (GQ, (Less (Simul (__O), Simul (__O')))::__D, __D', __P) ->
          ltSimulL (GQ, __D, __D', __O, __O', __P)
      | (GQ, (Leq (Arg (UsVs), Arg (UsVs')))::__D, __D', __P) ->
          leAtomicL (GQ, __D, __D', UsVs, UsVs', __P)
      | (GQ, (Leq (Lex (__O), Lex (__O')))::__D, __D', __P) ->
          (leftDecompose
             (GQ, ((Less ((R.Lex __O), (R.Lex __O'))) :: __D), __D', __P))
            &&
            (leftDecompose
               (GQ, ((Eq ((R.Lex __O), (R.Lex __O'))) :: __D), __D', __P))
      | (GQ, (Leq (Simul (__O), Simul (__O')))::__D, __D', __P) ->
          leSimulL (GQ, __D, __D', __O, __O', __P)
      | (GQ, (Eq (Arg (UsVs), Arg (UsVs')))::__D, __D', __P) ->
          eqAtomicL (GQ, __D, __D', UsVs, UsVs', __P)
      | (GQ, (Eq (Lex (__O), Lex (__O')))::__D, __D', __P) ->
          eqsL (GQ, __D, __D', __O, __O', __P)
      | (GQ, (Eq (Simul (__O), Simul (__O')))::__D, __D', __P) ->
          eqsL (GQ, __D, __D', __O, __O', __P)
      | (((__G, __Q) as GQ), (Pi (Dec, __O))::__D, __D', __P) ->
          (if (!Global.chatter) > 3
           then
             (print " Ignoring quantified order ";
              print (F.makestring_fmt (fmtPredicate (__G, (Pi (Dec, __O))))))
           else ();
           leftDecompose (GQ, __D, __D', __P))(* drop assumption Pi D. P *)
      (* eq *)(* le *)(* less *)
    let rec ltLexL __182__ __183__ __184__ __185__ __186__ __187__ =
      match (__182__, __183__, __184__, __185__, __186__, __187__) with
      | (GQ, __D, __D', nil, nil, __P) -> true
      | (GQ, __D, __D', (__O)::__L, (__O')::__L', __P) ->
          (leftDecompose (GQ, ((Less (__O, __O')) :: __D), __D', __P)) &&
            (ltLexL (GQ, ((Eq (__O, __O')) :: __D), __D', __L, __L', __P))
    let rec eqsL __188__ __189__ __190__ __191__ __192__ __193__ =
      match (__188__, __189__, __190__, __191__, __192__, __193__) with
      | (GQ, __D, __D', nil, nil, __P) -> true
      | (GQ, __D, __D', (__O)::__L, (__O')::__L', __P) ->
          (leftDecompose (GQ, ((Eq (__O, __O')) :: __D), __D', __P)) &&
            (eqsL (GQ, __D, __D', __L, __L', __P))
    let rec ltSimulL __194__ __195__ __196__ __197__ __198__ __199__ =
      match (__194__, __195__, __196__, __197__, __198__, __199__) with
      | (GQ, __D, __D', nil, nil, __P) -> leftDecompose (GQ, __D, __D', __P)
      | (GQ, __D, __D', (__O)::__L, (__O')::__L', __P) ->
          (leSimulL (GQ, ((Less (__O, __O')) :: __D), __D', __L, __L', __P))
            ||
            (ltSimulL (GQ, ((Eq (__O, __O')) :: __D), __D', __L, __L', __P))
    let rec leSimulL __200__ __201__ __202__ __203__ __204__ __205__ =
      match (__200__, __201__, __202__, __203__, __204__, __205__) with
      | (GQ, __D, __D', nil, nil, __P) -> leftDecompose (GQ, __D, __D', __P)
      | (GQ, __D, __D', (__O)::__L, (__O')::__L', __P) ->
          leSimulL (GQ, ((Leq (__O, __O')) :: __D), __D', __L, __L', __P)
    let rec ltAtomicL (GQ) (__D) (__D') (UsVs) (UsVs') (__P) =
      ltAtomicLW (GQ, __D, __D', UsVs, (Whnf.whnfEta UsVs'), __P)
    let rec ltAtomicLW __206__ __207__ __208__ __209__ __210__ __211__ =
      match (__206__, __207__, __208__, __209__, __210__, __211__) with
      | (((__G, __Q) as GQ), __D, __D', UsVs, (__Us', ((Root _, s') as Vs')),
         __P) -> ltL (GQ, __D, __D', UsVs, (__Us', __Vs'), __P)
      | (((__G, __Q) as GQ), __D, __D', ((__U, s1), (__V, s2)),
         ((Lam (_, __U'), s1'), (Pi ((Dec', _), __V'), s2')), __P) ->
          let __D1 = shiftRCtx __D (fun s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx __D' (fun s -> I.comp (s, I.shift)) in
          let UsVs =
            ((__U, (I.comp (s1, I.shift))), (__V, (I.comp (s2, I.shift)))) in
          let UsVs' = ((__U', (I.dot1 s1')), (__V', (I.dot1 s2'))) in
          let __P' = shiftP __P (fun s -> I.comp (s, I.shift)) in
          ltAtomicL
            (((I.Decl (__G, (N.decLUName (__G, (I.decSub (Dec', s2')))))),
               (I.Decl (__Q, All))), __D1, D1', UsVs, UsVs', __P')
    let rec leAtomicL (GQ) (__D) (__D') (UsVs) (UsVs') (__P) =
      leAtomicLW (GQ, __D, __D', UsVs, (Whnf.whnfEta UsVs'), __P)
    let rec leAtomicLW __212__ __213__ __214__ __215__ __216__ __217__ =
      match (__212__, __213__, __214__, __215__, __216__, __217__) with
      | (GQ, __D, __D', UsVs, (__Us', ((Root (__H, __S), s') as Vs')), __P)
          -> leL (GQ, __D, __D', UsVs, (__Us', __Vs'), __P)
      | (((__G, __Q) as GQ), __D, __D', ((__U, s1), (__V, s2)),
         ((Lam (_, __U'), s1'), (Pi ((Dec', _), __V'), s2')), __P) ->
          let __D1 = shiftRCtx __D (fun s -> I.comp (s, I.shift)) in
          let D1' = shiftACtx __D' (fun s -> I.comp (s, I.shift)) in
          let UsVs =
            ((__U, (I.comp (s1, I.shift))), (__V, (I.comp (s2, I.shift)))) in
          let UsVs' = ((__U', (I.dot1 s1')), (__V', (I.dot1 s2'))) in
          let __P' = shiftP __P (fun s -> I.comp (s, I.shift)) in
          leAtomicL
            (((I.Decl (__G, (N.decLUName (__G, (I.decSub (Dec', s2')))))),
               (I.Decl (__Q, All))), __D1, D1', UsVs, UsVs', __P')
    let rec eqAtomicL (GQ) (__D) (__D') (UsVs) (UsVs') (__P) =
      eqAtomicLW
        (GQ, __D, __D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), __P)
    let rec eqAtomicLW __218__ __219__ __220__ __221__ __222__ __223__ =
      match (__218__, __219__, __220__, __221__, __222__, __223__) with
      | (GQ, __D, __D', (__Us, ((Root _, s) as Vs)),
         (__Us', ((Root _, s') as Vs')), __P) ->
          eqL (GQ, __D, __D', (__Us, __Vs), (__Us', __Vs'), __P)
      | (GQ, __D, __D', (__Us, ((Root _, s) as Vs)),
         (__Us', ((Pi _, s') as Vs')), __P) -> true
      | (GQ, __D, __D', (__Us, ((Pi _, s) as Vs)),
         (__Us', ((Root _, s') as Vs')), __P) -> true
      | (GQ, __D, __D', (__Us, ((Pi _, s) as Vs)),
         (__Us', ((Pi _, s') as Vs')), __P) ->
          leftDecompose
            (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P)
    let rec leL (GQ) (__D) (__D') (UsVs) (UsVs') (__P) =
      (ltAtomicL (GQ, __D, __D', UsVs, UsVs', __P)) &&
        (eqAtomicL (GQ, __D, __D', UsVs, UsVs', __P))
    let rec ltL (GQ) (__D) (__D') (UsVs) (__Us', __Vs') (__P) =
      ltLW (GQ, __D, __D', UsVs, ((Whnf.whnf __Us'), __Vs'), __P)
    let rec ltLW __224__ __225__ __226__ __227__ __228__ __229__ =
      match (__224__, __225__, __226__, __227__, __228__, __229__) with
      | (((__G, __Q) as GQ), __D, __D', UsVs,
         (((Root (BVar n, __S'), s') as Us'), __Vs'), __P) ->
          if isAtomic (GQ, __Us')
          then
            leftDecompose
              (GQ, __D, ((Less (UsVs, (__Us', __Vs'))) :: __D'), __P)
          else
            (let Dec (_, __V') = I.ctxDec (__G, n) in
             ltSpineL (GQ, __D, __D', UsVs, ((__S', s'), (__V', I.id)), __P))
      | (GQ, __D, __D', UsVs, ((Root (Const c, __S'), s'), __Vs'), __P) ->
          ltSpineL
            (GQ, __D, __D', UsVs, ((__S', s'), ((I.constType c), I.id)), __P)
      | (GQ, __D, __D', UsVs, ((Root (Def c, __S'), s'), __Vs'), __P) ->
          ltSpineL
            (GQ, __D, __D', UsVs, ((__S', s'), ((I.constType c), I.id)), __P)
    let rec ltSpineL (GQ) (__D) (__D') (UsVs) (__Ss', __Vs') (__P) =
      ltSpineLW (GQ, __D, __D', UsVs, (__Ss', (Whnf.whnf __Vs')), __P)
    let rec ltSpineLW __230__ __231__ __232__ __233__ __234__ __235__ =
      match (__230__, __231__, __232__, __233__, __234__, __235__) with
      | (GQ, __D, __D', UsVs, ((I.Nil, _), _), _) -> true
      | (GQ, __D, __D', UsVs, ((SClo (__S, s'), s''), __Vs'), __P) ->
          ltSpineL
            (GQ, __D, __D', UsVs, ((__S, (I.comp (s', s''))), __Vs'), __P)
      | (GQ, __D, __D', UsVs,
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), __P)
          ->
          (leAtomicL (GQ, __D, __D', UsVs, ((__U', s1'), (V1', s2')), __P))
            &&
            (ltSpineL
               (GQ, __D, __D', UsVs,
                 ((__S', s1'),
                   (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), __P))
    let rec eqL (GQ) (__D) (__D') (UsVs) (UsVs') (__P) =
      eqLW (GQ, __D, __D', (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), __P)
    let rec eqLW __236__ __237__ __238__ __239__ __240__ __241__ =
      match (__236__, __237__, __238__, __239__, __240__, __241__) with
      | (GQ, __D, __D', (__Us, ((Pi ((Dec (_, V2'), _), __V'), s2') as Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), __P) ->
          leftDecompose
            (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P)
      | (GQ, __D, __D', (__Us, ((Pi ((Dec (_, V2'), _), __V'), s2') as Vs)),
         (__Us', ((Root _, s2'') as Vs')), __P) -> true
      | (GQ, __D, __D', (__Us, ((Root _, s2') as Vs)),
         (__Us', ((Pi ((Dec (_, V2''), _), V''), s2'') as Vs')), __P) ->
          true
      | (GQ, __D, __D', (((Root (Const c, __S), s), __Vs) as UsVs),
         (((Root (Const c', __S'), s'), __Vs') as UsVs'), __P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, __D, __D', ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), __P)
          else true
      | (GQ, __D, __D', (((Root (Const c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), __P) ->
          if isAtomic (GQ, __Us')
          then
            leftDecompose
              (GQ, __D, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __D'), __P)
          else true
      | (GQ, __D, __D', (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Const c, __S'), s') as Us'), __Vs'), __P) ->
          if isAtomic (GQ, __Us)
          then
            leftDecompose
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P)
          else true
      | (GQ, __D, __D', (((Root (Def c, __S), s), __Vs) as UsVs),
         (((Root (Def c', __S'), s'), __Vs') as UsVs'), __P) ->
          if eqCid (c, c')
          then
            eqSpineL
              (GQ, __D, __D', ((__S, s), ((I.constType c), I.id)),
                ((__S', s'), ((I.constType c'), I.id)), __P)
          else true
      | (GQ, __D, __D', (((Root (Def c, __S), s) as Us), __Vs),
         (((Root (BVar n, __S'), s') as Us'), __Vs'), __P) ->
          if isAtomic (GQ, __Us')
          then
            leftDecompose
              (GQ, __D, ((Eq ((__Us', __Vs'), (__Us, __Vs))) :: __D'), __P)
          else true
      | (GQ, __D, __D', (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (Def c, __S'), s') as Us'), __Vs'), __P) ->
          if isAtomic (GQ, __Us)
          then
            leftDecompose
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P)
          else true
      | (((__G, __Q) as GQ), __D, __D',
         (((Root (BVar n, __S), s) as Us), __Vs),
         (((Root (BVar n', __S'), s') as Us'), __Vs'), __P) ->
          if n = n'
          then
            let Dec (_, __V') = I.ctxDec (__G, n) in
            eqSpineL
              (GQ, __D, __D', ((__S, s), (__V', I.id)),
                ((__S', s'), (__V', I.id)), __P)
          else
            leftDecompose
              (GQ, __D, ((Eq ((__Us, __Vs), (__Us', __Vs'))) :: __D'), __P)
      | (GQ, __D, __D', UsVs, UsVs', __P) ->
          leftDecompose (GQ, __D, ((Eq (UsVs, UsVs')) :: __D'), __P)(* UsVs = Lam *)
      (*
     | eqLW (GQ, D, D', UsVs as ((I.Root (I.BVar n, I.Nil), s), Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, D, D', P)
         else
           leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

*)
    let rec eqSpineL (GQ) (__D) (__D') (__Ss, __Vs) (__Ss', __Vs') (__P) =
      eqSpineLW
        (GQ, __D, __D', (__Ss, (Whnf.whnf __Vs)), (__Ss', (Whnf.whnf __Vs')),
          __P)
    let rec eqSpineLW __242__ __243__ __244__ __245__ __246__ __247__ =
      match (__242__, __243__, __244__, __245__, __246__, __247__) with
      | (GQ, __D, __D', ((I.Nil, s), __Vs), ((I.Nil, s'), __Vs'), __P) ->
          leftDecompose (GQ, __D, __D', __P)
      | (GQ, __D, __D', ((SClo (__S, s'), s''), __Vs), SsVs', __P) ->
          eqSpineL
            (GQ, __D, __D', ((__S, (I.comp (s', s''))), __Vs), SsVs', __P)
      | (GQ, __D, __D', SsVs, ((SClo (__S', s'), s''), __Vs'), __P) ->
          eqSpineL
            (GQ, __D, __D', SsVs, ((__S', (I.comp (s', s''))), __Vs'), __P)
      | (GQ, __D, __D',
         ((App (__U, __S), s1), (Pi ((Dec (_, __V1), _), __V2), s2)),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), __P)
          ->
          let __D1 =
            (Eq
               ((R.Arg ((__U, s1), (__V1, s2))),
                 (R.Arg ((__U', s1'), (V1', s2')))))
              :: __D in
          eqSpineL
            (GQ, __D1, __D',
              ((__S, s1), (__V2, (I.Dot ((I.Exp (I.EClo (__U, s1))), s2)))),
              ((__S', s1'),
                (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), __P)
    let rec deduce (__G) (__Q) (__D) (__P) =
      leftDecompose ((__G, __Q), __D, nil, __P)
    let deduce = deduce
    let shiftRCtx = shiftRCtx
    let shiftPred = shiftP
  end ;;
