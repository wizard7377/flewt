
module type RECURSION  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expandLazy : MetaSyn.__State -> operator list
    val expandEager : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State
    val menu : operator -> string
  end;;




module Recursion(Recursion:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Conv : CONV
                             module Names : NAMES
                             module Subordinate : SUBORDINATE
                             module Print : PRINT
                             module Order : ORDER
                             module ModeTable : MODETABLE
                             module Lemma : LEMMA
                             module Filling : FILLING
                             module MetaPrint : METAPRINT
                             module MetaAbstract : METAABSTRACT
                             module Formatter : FORMATTER
                           end) : RECURSION =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    type nonrec operator = MetaSyn.__State
    module M = MetaSyn
    module I = IntSyn
    module O = Order
    module N = Names
    module F = Formatter
    type __Quantifier =
      | Universal 
      | Existential 
    let rec vectorToString (__G) (__O) =
      let rec fmtOrder =
        function
        | Arg (__Us, __Vs) ->
            [F.String (Print.expToString (__G, (I.EClo __Us)));
            F.String ":";
            F.String (Print.expToString (__G, (I.EClo __Vs)))]
        | Lex (__L) -> [F.String "{"; F.HVbox (fmtOrders __L); F.String "}"]
        | Simul (__L) ->
            [F.String "["; F.HVbox (fmtOrders __L); F.String "]"]
      and fmtOrders =
        function
        | nil -> nil
        | (__O)::nil -> fmtOrder __O
        | (__O)::__L -> (fmtOrder __O) @ ((::) (F.String " ") fmtOrders __L) in
      F.makestring_fmt (F.HVbox (fmtOrder __O))
    let rec vector c (__S, s) =
      let Vid = ((I.constType c), I.id) in
      let rec select' n (__Ss', Vs'') =
        select'W (n, (__Ss', (Whnf.whnf Vs'')))
      and select'W __0__ __1__ =
        match (__0__, __1__) with
        | (1, ((App (__U', __S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((__U', s'), (V'', s''))
        | (n, ((SClo (__S', s1'), s2'), Vs'')) ->
            select'W (n, ((__S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (__U', __S'), s'), (Pi ((Dec (_, V1''), _), V2''), s'')))
            ->
            select'
              ((n - 1),
                ((__S', s'),
                  (V2'', (I.Dot ((I.Exp (I.EClo (__U', s'))), s'')))))
      (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *) in
      let rec select =
        function
        | Arg n -> O.Arg (select' (n, ((__S, s), Vid)))
        | Lex (__L) -> O.Lex (map select __L)
        | Simul (__L) -> O.Simul (map select __L) in
      select (O.selLookup c)
    let rec set_parameter (__G) (EVar (r, _, __V, _) as X) k sc ops =
      let rec set_parameter' __2__ __3__ =
        match (__2__, __3__) with
        | (0, ops') -> ops'
        | (k', ops') ->
            let Dec (_, __V') as D' = I.ctxDec (__G, k') in
            let ops'' =
              CSManager.trail
                (fun () ->
                   if
                     (Unify.unifiable (__G, (__V, I.id), (__V', I.id))) &&
                       (Unify.unifiable
                          (__G, (__X, I.id),
                            ((I.Root ((I.BVar k'), I.Nil)), I.id)))
                   then sc ops'
                   else ops') in
            set_parameter' ((k' - 1), ops'') in
      set_parameter' (k, ops)
    let rec ltinit (__G) k (__Us, __Vs) (UsVs') sc ops =
      ltinitW (__G, k, (Whnf.whnfEta (__Us, __Vs)), UsVs', sc, ops)
    let rec ltinitW __4__ __5__ __6__ __7__ __8__ __9__ =
      match (__4__, __5__, __6__, __7__, __8__, __9__) with
      | (__G, k, (__Us, ((Root _, _) as Vs)), UsVs', sc, ops) ->
          lt (__G, k, (__Us, __Vs), UsVs', sc, ops)
      | (__G, k, ((Lam (__D1, __U), s1), (Pi (__D2, __V), s2)),
         ((__U', s1'), (__V', s2')), sc, ops) ->
          ltinit
            ((I.Decl (((__G, (I.decSub (__D1, s1))))
                (* = I.decSub (D2, s2) *))), (k + 1),
              ((__U, (I.dot1 s1)), (__V, (I.dot1 s2))),
              ((__U', (I.comp (s1', I.shift))),
                (__V', (I.comp (s2', I.shift)))), sc, ops)
    let rec lt (__G) k (__Us, __Vs) (__Us', __Vs') sc ops =
      ltW (__G, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ops)
    let rec ltW __10__ __11__ __12__ __13__ __14__ __15__ =
      match (__10__, __11__, __12__, __13__, __14__, __15__) with
      | (__G, k, (__Us, __Vs), ((Root (Const c, __S'), s'), __Vs'), sc, ops)
          ->
          ltSpine
            (__G, k, (__Us, __Vs), ((__S', s'), ((I.constType c), I.id)), sc,
              ops)
      | (__G, k, (__Us, __Vs), ((Root (BVar n, __S'), s'), __Vs'), sc, ops)
          ->
          ((if n <= k
            then
              let Dec (_, __V') = I.ctxDec (__G, n) in
              ltSpine
                (__G, k, (__Us, __Vs), ((__S', s'), (__V', I.id)), sc, ops)
            else ops)
          (* n must be a local variable *))
      | (__G, _, _, ((EVar _, _), _), _, ops) -> ops
      | (__G, k, ((__U, s1), (__V, s2)),
         ((Lam ((Dec (_, V1') as D), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, ops) ->
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' ops' = set_parameter (__G, __X, k, sc, ops') in
              ((lt
                  (__G, k, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', ops))
                (* enforce that X gets only bound to parameters *)
                (* = I.newEVar (I.EClo (V2', s2')) *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 ((lt
                     (__G, k, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc, ops))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else ops)
          (* == I.targetFam V2' *))
    let rec ltSpine (__G) k (__Us, __Vs) (__Ss', __Vs') sc ops =
      ltSpineW (__G, k, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, ops)
    let rec ltSpineW __16__ __17__ __18__ __19__ __20__ __21__ =
      match (__16__, __17__, __18__, __19__, __20__, __21__) with
      | (__G, k, (__Us, __Vs), ((I.Nil, _), _), _, ops) -> ops
      | (__G, k, (__Us, __Vs), ((SClo (__S, s'), s''), __Vs'), sc, ops) ->
          ltSpineW
            (__G, k, (__Us, __Vs), ((__S, (I.comp (s', s''))), __Vs'), sc,
              ops)
      | (__G, k, (__Us, __Vs),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc,
         ops) ->
          let ops' =
            le (__G, k, (__Us, __Vs), ((__U', s1'), (V1', s2')), sc, ops) in
          ltSpine
            (__G, k, (__Us, __Vs),
              ((__S', s1'),
                (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), sc,
              ops')
    let rec eq (__G) (__Us, __Vs) (__Us', __Vs') sc ops =
      CSManager.trail
        (fun () ->
           if
             (Unify.unifiable (__G, __Vs, __Vs')) &&
               (Unify.unifiable (__G, __Us, __Us'))
           then sc ops
           else ops)
    let rec le (__G) k (__Us, __Vs) (__Us', __Vs') sc ops =
      let ops' = eq (__G, (__Us, __Vs), (__Us', __Vs'), sc, ops) in
      leW (__G, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ops')
    let rec leW __22__ __23__ __24__ __25__ __26__ __27__ =
      match (__22__, __23__, __24__, __25__, __26__, __27__) with
      | (__G, k, ((__U, s1), (__V, s2)),
         ((Lam ((Dec (_, V1') as D), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, ops) ->
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' ops' = set_parameter (__G, __X, k, sc, ops') in
              ((le
                  (__G, k, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', ops))
                (* = I.newEVar (I.EClo (V2', s2')) *)
                (* enforces that X can only bound to parameter *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 ((le
                     (__G, k, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc, ops))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else ops)
          (* == I.targetFam V2' *))
      | (__G, k, (__Us, __Vs), (__Us', __Vs'), sc, ops) ->
          lt (__G, k, (__Us, __Vs), (__Us', __Vs'), sc, ops)
    let rec ordlt __28__ __29__ __30__ __31__ __32__ =
      match (__28__, __29__, __30__, __31__, __32__) with
      | (__G, Arg (UsVs), Arg (UsVs'), sc, ops) ->
          ltinit (__G, 0, UsVs, UsVs', sc, ops)
      | (__G, Lex (__L), Lex (__L'), sc, ops) ->
          ordltLex (__G, __L, __L', sc, ops)
      | (__G, Simul (__L), Simul (__L'), sc, ops) ->
          ordltSimul (__G, __L, __L', sc, ops)
    let rec ordltLex __33__ __34__ __35__ __36__ __37__ =
      match (__33__, __34__, __35__, __36__, __37__) with
      | (__G, nil, nil, sc, ops) -> ops
      | (__G, (__O)::__L, (__O')::__L', sc, ops) ->
          let ops' =
            CSManager.trail (fun () -> ordlt (__G, __O, __O', sc, ops)) in
          ordeq
            (__G, __O, __O',
              (fun ops'' -> ordltLex (__G, __L, __L', sc, ops'')), ops')
    let rec ordltSimul __38__ __39__ __40__ __41__ __42__ =
      match (__38__, __39__, __40__, __41__, __42__) with
      | (__G, nil, nil, sc, ops) -> ops
      | (__G, (__O)::__L, (__O')::__L', sc, ops) ->
          let ops'' =
            CSManager.trail
              (fun () ->
                 ordlt
                   (__G, __O, __O',
                     (fun ops' -> ordleSimul (__G, __L, __L', sc, ops')),
                     ops)) in
          ordeq
            (__G, __O, __O',
              (fun ops' -> ordltSimul (__G, __L, __L', sc, ops')), ops'')
    let rec ordleSimul __43__ __44__ __45__ __46__ __47__ =
      match (__43__, __44__, __45__, __46__, __47__) with
      | (__G, nil, nil, sc, ops) -> sc ops
      | (__G, (__O)::__L, (__O')::__L', sc, ops) ->
          ordle
            (__G, __O, __O',
              (fun ops' -> ordleSimul (__G, __L, __L', sc, ops')), ops)
    let rec ordeq __48__ __49__ __50__ __51__ __52__ =
      match (__48__, __49__, __50__, __51__, __52__) with
      | (__G, Arg (__Us, __Vs), Arg (__Us', __Vs'), sc, ops) ->
          if
            (Unify.unifiable (__G, __Vs, __Vs')) &&
              (Unify.unifiable (__G, __Us, __Us'))
          then sc ops
          else ops
      | (__G, Lex (__L), Lex (__L'), sc, ops) ->
          ordeqs (__G, __L, __L', sc, ops)
      | (__G, Simul (__L), Simul (__L'), sc, ops) ->
          ordeqs (__G, __L, __L', sc, ops)
    let rec ordeqs __53__ __54__ __55__ __56__ __57__ =
      match (__53__, __54__, __55__, __56__, __57__) with
      | (__G, nil, nil, sc, ops) -> sc ops
      | (__G, (__O)::__L, (__O')::__L', sc, ops) ->
          ordeq
            (__G, __O, __O', (fun ops' -> ordeqs (__G, __L, __L', sc, ops')),
              ops)
    let rec ordle (__G) (__O) (__O') sc ops =
      let ops' = CSManager.trail (fun () -> ordeq (__G, __O, __O', sc, ops)) in
      ordlt (__G, __O, __O', sc, ops')
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (__G, __D), Decl (__M, M.Top), Decl (__B, b)) ->
          let (Prefix (__G', __M', __B'), s') =
            createEVars (M.Prefix (__G, __M, __B)) in
          ((M.Prefix
              ((I.Decl (__G', (I.decSub (__D, s')))), (I.Decl (__M', M.Top)),
                (I.Decl (__B', b)))), (I.dot1 s'))
      | Prefix (Decl (__G, Dec (_, __V)), Decl (__M, M.Bot), Decl (__B, _))
          ->
          let (Prefix (__G', __M', __B'), s') =
            createEVars (M.Prefix (__G, __M, __B)) in
          let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
          ((M.Prefix (__G', __M', __B')), (I.Dot ((I.Exp __X), s')))
    let rec select (__G) (__Vs) = selectW (__G, (Whnf.whnf __Vs))
    let rec selectW (__G) (Pi (((Dec (_, __V1) as D), _), __V2), s) =
      let rec select' (__G) (__Vs1, __Vs2) =
        selectW' (__G, (__Vs1, (Whnf.whnf __Vs2)))
      and selectW' __58__ __59__ =
        match (__58__, __59__) with
        | (__G, (__Vs1, ((Root _, _) as Vs2))) -> (__G, (__Vs1, __Vs2))
        | (__G, ((__V1, s1), (Pi ((__D, __P), V2'), s2))) ->
            select'
              ((I.Decl (__G, (I.decSub (__D, s2)))),
                ((__V1, (I.comp (s1, I.shift))), (V2', (I.dot1 s2)))) in
      select'
        ((I.Decl (__G, (I.decSub (__D, s)))),
          ((__V1, (I.comp (s, I.shift))), (__V2, (I.dot1 s))))
    let rec lemma (__S) t ops =
      let State (name, GM, __V) = Lemma.apply (__S, t) in
      let (Prefix (__G', __M', __B'), s') = createEVars GM in
      let (G'', ((Root (Const a1, __S1), s1), (Root (Const a2, __S2), s2))) =
        select (__G', (__V, s')) in
      (G'', (vector (a1, (__S1, s1))), (vector (a2, (__S2, s2))),
        (fun ops' ->
           (MetaAbstract.abstract
              (M.State
                 (name, (M.Prefix (__G', __M', __B')), (I.EClo (__V, s')))))
             :: ops'), ops)
    let rec expandLazy' __60__ __61__ __62__ =
      match (__60__, __61__, __62__) with
      | (__S, O.Empty, ops) -> ops
      | (__S, LE (t, __L), ops) ->
          expandLazy' (__S, __L, (ordle (lemma (__S, t, ops))))
      | (__S, LT (t, __L), ops) ->
          expandLazy' (__S, __L, (ordlt (lemma (__S, t, ops))))
    let rec recursionDepth (__V) =
      let rec recursionDepth' __63__ __64__ =
        match (__63__, __64__) with
        | (Root _, n) -> n
        | (Pi (_, __V), n) -> recursionDepth' (__V, (n + 1)) in
      recursionDepth' (__V, 0)
    let rec expandLazy (State (_, _, __V) as S) =
      if (recursionDepth __V) > (!MetaGlobal.maxRecurse)
      then nil
      else expandLazy' (__S, (O.mutLookup (I.targetFam __V)), nil)
    let rec inputConv (__Vs1) (__Vs2) =
      inputConvW ((Whnf.whnf __Vs1), (Whnf.whnf __Vs2))
    let rec inputConvW (Root (Const c1, __S1), s1)
      (Root (Const c2, __S2), s2) =
      if c1 = c2
      then
        inputConvSpine
          ((valOf (ModeTable.modeLookup c1)),
            ((__S1, s1), ((I.constType c1), I.id)),
            ((__S2, s2), ((I.constType c2), I.id)))
      else false__(* s1 = s2 = id *)
    let rec inputConvSpine __65__ __66__ __67__ =
      match (__65__, __66__, __67__) with
      | (ModeSyn.Mnil, ((__S1, _), _), ((__S2, _), _)) -> true__
      | (mS, ((SClo (__S1, s1'), s1), __Vs1), (__Ss2, __Vs2)) ->
          inputConvSpine
            (mS, ((__S1, (I.comp (s1', s1))), __Vs1), (__Ss2, __Vs2))
      | (mS, (__Ss1, __Vs1), ((SClo (__S2, s2'), s2), __Vs2)) ->
          inputConvSpine
            (mS, (__Ss1, __Vs1), ((__S2, (I.comp (s2', s2))), __Vs2))
      | (Mapp (Marg (ModeSyn.Minus, _), mS),
         ((App (__U1, __S1), s1), (Pi ((Dec (_, __V1), _), __W1), t1)),
         ((App (__U2, __S2), s2), (Pi ((Dec (_, __V2), _), __W2), t2))) ->
          (Conv.conv ((__V1, t1), (__V2, t2))) &&
            (inputConvSpine
               (mS,
                 ((__S1, s1),
                   (__W1, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t1)))),
                 ((__S2, s2),
                   (__W2, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t2))))))
      | (Mapp (Marg (ModeSyn.Plus, _), mS),
         ((App (__U1, __S1), s1), (Pi ((Dec (_, __V1), _), __W1), t1)),
         ((App (__U2, __S2), s2), (Pi ((Dec (_, __V2), _), __W2), t2))) ->
          inputConvSpine
            (mS,
              ((__S1, s1), (__W1, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t1)))),
              ((__S2, s2), (__W2, (I.Dot ((I.Exp (I.EClo (__U2, s2))), t2)))))
      (* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
      (* S1 = S2 = Nil *)
    let rec removeDuplicates =
      function
      | nil -> nil
      | (__S')::ops ->
          let rec compExp (__Vs1) (__Vs2) =
            compExpW ((Whnf.whnf __Vs1), (Whnf.whnf __Vs2))
          and compExpW __68__ __69__ =
            match (__68__, __69__) with
            | (__Vs1, (Root _, _)) -> false__
            | (((__V1, s1) as Vs1), (Pi ((__D2, _), __V2), s2)) ->
                (compDec (__Vs1, (__D2, s2))) ||
                  (compExp
                     ((__V1, (I.comp (s1, I.shift))), (__V2, (I.dot1 s2))))
          and compDec (__Vs1) (Dec (_, __V2), s2) =
            inputConv (__Vs1, (__V2, s2)) in
          let rec check (State (name, GM, __V)) =
            checkW (Whnf.whnf (__V, I.id))
          and checkW (Pi ((__D, _), __V)) s =
            checkDec ((__D, (I.comp (s, I.shift))), (__V, (I.dot1 s)))
          and checkDec (Dec (_, __V1), s1) (__Vs2) =
            compExp ((__V1, s1), __Vs2) in
          if check __S'
          then removeDuplicates ops
          else __S' :: (removeDuplicates ops)
    let rec fillOps =
      function
      | nil -> nil
      | (__S')::ops ->
          let rec fillOps' =
            function | nil -> nil | (__O)::_ -> Filling.apply __O in
          let (fillop, _) = Filling.expand __S' in
          (fillOps' fillop) @ (fillOps ops)
    let rec expandEager (__S) = removeDuplicates (fillOps (expandLazy __S))
    let rec apply (__S) = __S
    let rec menu
      (State (name, Prefix (__G', __M', __B'), Pi ((Dec (_, __V), _), _)) as
         S)
      = "Recursion : " ^ (Print.expToString (__G', __V))
    let rec handleExceptions f (__P) =
      try f __P with | Error s -> raise (Error s)
    let expandLazy = handleExceptions expandLazy
    let expandEager = handleExceptions expandEager
    let apply = apply
    let menu = menu
  end ;;
