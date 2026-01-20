
module type SPLITTING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expand : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State list
    val var : operator -> int
    val menu : operator -> string
    val index : operator -> int
  end;;




module Splitting(Splitting:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module MetaAbstract : METAABSTRACT
                             module MetaPrint : METAPRINT
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Print : PRINT
                             module Unify : UNIFY
                           end) : SPLITTING =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    type 'a flag =
      | Active of 'a 
      | InActive 
    type nonrec operator =
      ((MetaSyn.__State * int) * MetaSyn.__State flag list)
    module M = MetaSyn
    module I = IntSyn
    let rec constCases __0__ __1__ __2__ __3__ __4__ =
      match (__0__, __1__, __2__, __3__, __4__) with
      | (__G, __Vs, nil, abstract, ops) -> ops
      | (__G, __Vs, (Const c)::Sgn, abstract, ops) ->
          let (__U, __Vs') = M.createAtomConst (__G, (I.Const c)) in
          constCases
            (__G, __Vs, Sgn, abstract,
              (CSManager.trail
                 (fun () ->
                    try
                      if Unify.unifiable (__G, __Vs, __Vs')
                      then
                        (Active
                           (abstract
                              (((I.conDecName (I.sgnLookup c)) ^ "/"), __U)))
                          :: ops
                      else ops
                    with | Error _ -> InActive :: ops)))
    let rec paramCases __5__ __6__ __7__ __8__ __9__ =
      match (__5__, __6__, __7__, __8__, __9__) with
      | (__G, __Vs, 0, abstract, ops) -> ops
      | (__G, __Vs, k, abstract, ops) ->
          let (__U, __Vs') = M.createAtomBVar (__G, k) in
          paramCases
            (__G, __Vs, (k - 1), abstract,
              (CSManager.trail
                 (fun () ->
                    try
                      if Unify.unifiable (__G, __Vs, __Vs')
                      then
                        (Active (abstract (((Int.toString k) ^ "/"), __U)))
                          :: ops
                      else ops
                    with | Error _ -> InActive :: ops)))
    let rec lowerSplitDest __10__ __11__ __12__ =
      match (__10__, __11__, __12__) with
      | (__G, ((Root (Const c, _) as V), s'), abstract) ->
          constCases
            (__G, (__V, s'), (Index.lookup c), abstract,
              (paramCases (__G, (__V, s'), (I.ctxLength __G), abstract, nil)))
      | (__G, (Pi ((__D, __P), __V), s'), abstract) ->
          let __D' = I.decSub (__D, s') in
          lowerSplitDest
            ((I.Decl (__G, __D')), (__V, (I.dot1 s')),
              (fun name -> fun (__U) -> abstract (name, (I.Lam (__D', __U)))))
    let rec split (Prefix (__G, __M, __B)) ((Dec (_, __V) as D), s) abstract
      =
      lowerSplitDest
        (I.Null, (__V, s),
          (fun name' ->
             fun (__U') ->
               abstract
                 (name', (M.Prefix (__G, __M, __B)),
                   (I.Dot ((I.Exp __U'), s)))))
    let rec occursInExp __13__ __14__ =
      match (__13__, __14__) with
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
    let rec occursInCon __15__ __16__ =
      match (__15__, __16__) with
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false
      | (k, Def _) -> false
      | (k, Skonst _) -> false
    let rec occursInSpine __17__ __18__ =
      match (__17__, __18__) with
      | (_, I.Nil) -> false
      | (k, App (__U, __S)) ->
          (occursInExp (k, __U)) || (occursInSpine (k, __S))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec isIndexInit k = false
    let rec isIndexSucc (__D) isIndex k =
      (occursInDec (k, __D)) || (isIndex (k + 1))
    let rec isIndexFail (__D) isIndex k = isIndex (k + 1)
    let rec checkVar __19__ __20__ =
      match (__19__, __20__) with
      | (Decl (__M, M.Top), 1) -> true
      | (Decl (__M, M.Bot), 1) -> false
      | (Decl (__M, _), k) -> checkVar (__M, (k - 1))
    let rec checkExp __21__ __22__ =
      match (__21__, __22__) with
      | (__M, Uni _) -> true
      | (__M, Pi ((__D, __P), __V)) ->
          (checkDec (__M, __D)) && (checkExp ((I.Decl (__M, M.Top)), __V))
      | (__M, Lam (__D, __V)) ->
          (checkDec (__M, __D)) && (checkExp ((I.Decl (__M, M.Top)), __V))
      | (__M, Root (BVar k, __S)) ->
          (checkVar (__M, k)) && (checkSpine (__M, __S))
      | (__M, Root (_, __S)) -> checkSpine (__M, __S)
    let rec checkSpine __23__ __24__ =
      match (__23__, __24__) with
      | (__M, I.Nil) -> true
      | (__M, App (__U, __S)) ->
          (checkExp (__M, __U)) && (checkSpine (__M, __S))
    let rec checkDec (__M) (Dec (_, __V)) = checkExp (__M, __V)
    let rec modeEq __25__ __26__ =
      match (__25__, __26__) with
      | (Marg (ModeSyn.Plus, _), M.Top) -> true
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true
      | _ -> false
    let rec inheritBelow __27__ __28__ __29__ __30__ =
      match (__27__, __28__, __29__, __30__) with
      | (b', k', Lam (__D', __U'), Bdd') ->
          inheritBelow
            (b', (k' + 1), __U', (inheritBelowDec (b', k', __D', Bdd')))
      | (b', k', Pi ((__D', _), __V'), Bdd') ->
          inheritBelow
            (b', (k' + 1), __V', (inheritBelowDec (b', k', __D', Bdd')))
      | (b', k', Root (BVar n', __S'), (__B', d, d')) ->
          ((if ((n' = k') + d') && (n' > k')
            then
              inheritBelowSpine
                (b', k', __S', ((I.Decl (__B', b')), d, (d' - 1)))
            else inheritBelowSpine (b', k', __S', (__B', d, d')))
          (* necessary for d' = 0 *))
      | (b', k', Root (__C, __S'), Bdd') ->
          inheritBelowSpine (b', k', __S', Bdd')
    let rec inheritBelowSpine __31__ __32__ __33__ __34__ =
      match (__31__, __32__, __33__, __34__) with
      | (b', k', I.Nil, Bdd') -> Bdd'
      | (b', k', App (__U', __S'), Bdd') ->
          inheritBelowSpine
            (b', k', __S', (inheritBelow (b', k', __U', Bdd')))
    let rec inheritBelowDec b' k' (Dec (x, __V')) (Bdd') =
      inheritBelow (b', k', __V', Bdd')
    let rec skip __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (k, Lam (__D, __U), Bdd') ->
          skip ((k + 1), __U, (skipDec (k, __D, Bdd')))
      | (k, Pi ((__D, _), __V), Bdd') ->
          skip ((k + 1), __V, (skipDec (k, __D, Bdd')))
      | (k, Root (BVar n, __S), (__B', d, d')) ->
          ((if ((n = k) + d) && (n > k)
            then skipSpine (k, __S, (__B', (d - 1), d'))
            else skipSpine (k, __S, (__B', d, d')))
          (* necessary for d = 0 *))
      | (k, Root (__C, __S), Bdd') -> skipSpine (k, __S, Bdd')
    let rec skipSpine __38__ __39__ __40__ =
      match (__38__, __39__, __40__) with
      | (k, I.Nil, Bdd') -> Bdd'
      | (k, App (__U, __S), Bdd') ->
          skipSpine (k, __S, (skip (k, __U, Bdd')))
    let rec skipDec k (Dec (x, __V)) (Bdd') = skip (k, __V, Bdd')
    let rec inheritExp __41__ __42__ __43__ __44__ __45__ __46__ =
      match (__41__, __42__, __43__, __44__, __45__, __46__) with
      | (__B, k, Lam (__D, __U), k', Lam (__D', __U'), Bdd') ->
          inheritExp
            (__B, (k + 1), __U, (k' + 1), __U',
              (inheritDec (__B, k, __D, k', __D', Bdd')))
      | (__B, k, Pi ((__D, _), __V), k', Pi ((__D', _), __V'), Bdd') ->
          inheritExp
            (__B, (k + 1), __V, (k' + 1), __V',
              (inheritDec (__B, k, __D, k', __D', Bdd')))
      | (__B, k, (Root (BVar n, __S) as V), k', __V', (__B', d, d')) ->
          ((if ((n = k) + d) && (n > k)
            then
              skipSpine
                (k, __S,
                  (inheritNewRoot
                     (__B, (I.ctxLookup (__B, (n - k))), k, __V, k', __V',
                       (__B', d, d'))))
            else
              ((if (n > k) + d
                then
                  skipSpine
                    (k, __S,
                      (inheritBelow
                         (((I.ctxLookup (__B, (n - k))) - 1), k', __V',
                           (__B', d, d'))))
                else
                  (let Root (__C', __S') = __V' in
                   ((inheritSpine (__B, k, __S, k', __S', (__B', d, d')))
                     (* C' = BVar (n) *))))
              (* already seen original variable *)(* then (B', d, d') *)
              (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
              (* must correspond *)))
          (* new original variable *)(* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *))
      | (__B, k, Root (__C, __S), k', Root (__C', __S'), Bdd') ->
          inheritSpine (__B, k, __S, k', __S', Bdd')(* C ~ C' *)
    let rec inheritNewRoot __47__ __48__ __49__ __50__ __51__ __52__ __53__ =
      match (__47__, __48__, __49__, __50__, __51__, __52__, __53__) with
      | (__B, b, k, Root (BVar n, __S), k', (Root (BVar n', __S') as V'),
         (__B', d, d')) ->
          ((if ((n' = k') + d') && (n' > k')
            then inheritBelow (b, k', __V', (__B', (d - 1), d'))
            else inheritBelow ((b - 1), k', __V', (__B', (d - 1), d')))
          (* n' also new --- same variable: do not decrease *))
      | (__B, b, k, __V, k', __V', (__B', d, d')) ->
          inheritBelow ((b - 1), k', __V', (__B', (d - 1), d'))(* n' not new --- decrease the splitting depth of all variables in V' *)
      (* n = k+d *)
    let rec inheritSpine __54__ __55__ __56__ __57__ __58__ __59__ =
      match (__54__, __55__, __56__, __57__, __58__, __59__) with
      | (__B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (__B, k, App (__U, __S), k', App (__U', __S'), Bdd') ->
          inheritSpine
            (__B, k, __S, k', __S',
              (inheritExp (__B, k, __U, k', __U', Bdd')))
    let rec inheritDec (__B) k (Dec (_, __V)) k' (Dec (_, __V')) (Bdd') =
      inheritExp (__B, k, __V, k', __V', Bdd')
    let rec inheritDTop __60__ __61__ __62__ __63__ __64__ __65__ =
      match (__60__, __61__, __62__, __63__, __64__, __65__) with
      | (__B, k, Pi ((Dec (_, __V1), I.No), __V2), k', Pi
         ((Dec (_, V1'), I.No), V2'), Bdd') ->
          inheritG
            (__B, k, __V1, k', V1',
              (inheritDTop (__B, (k + 1), __V2, (k' + 1), V2', Bdd')))
      | (__B, k, (Root (Const cid, __S) as V), k',
         (Root (Const cid', __S') as V'), Bdd') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Top, mS, __B, k, __S, k', __S', Bdd')(* cid = cid' *)
    let rec inheritDBot __66__ __67__ __68__ __69__ __70__ __71__ =
      match (__66__, __67__, __68__, __69__, __70__, __71__) with
      | (__B, k, Pi ((Dec (_, __V1), I.No), __V2), k', Pi
         ((Dec (_, V1'), I.No), V2'), Bdd') ->
          inheritDBot (__B, (k + 1), __V2, (k' + 1), V2', Bdd')
      | (__B, k, Root (Const cid, __S), k', Root (Const cid', __S'), Bdd') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Bot, mS, __B, k, __S, k', __S', Bdd')(* cid = cid' *)
    let rec inheritG (__B) k (Root (Const cid, __S)) k'
      (Root (Const cid', __S') as V') (Bdd') =
      let mS = valOf (ModeTable.modeLookup cid) in
      ((inheritSpineMode
          (M.Bot, mS, __B, k, __S, k', __S',
            (inheritSpineMode (M.Top, mS, __B, k, __S, k', __S', Bdd'))))
        (* mode dependency in Goal: first M.Top, then M.Bot *))
    let rec inheritSpineMode __72__ __73__ __74__ __75__ __76__ __77__ __78__
      __79__ =
      match (__72__, __73__, __74__, __75__, __76__, __77__, __78__, __79__)
      with
      | (mode, ModeSyn.Mnil, __B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (mode, Mapp (m, mS), __B, k, App (__U, __S), k', App (__U', __S'),
         Bdd') ->
          if modeEq (m, mode)
          then
            inheritSpineMode
              (mode, mS, __B, k, __S, k', __S',
                (inheritExp (__B, k, __U, k', __U', Bdd')))
          else inheritSpineMode (mode, mS, __B, k, __S, k', __S', Bdd')
    let rec inheritSplitDepth (State (_, Prefix (__G, __M, __B), __V) as S)
      (State (name', Prefix (__G', __M', __B'), __V') as S') =
      let d = I.ctxLength __G in
      let d' = I.ctxLength __G' in
      let __V = Whnf.normalize (__V, I.id) in
      let __V' = Whnf.normalize (__V', I.id) in
      let (B'', 0, 0) =
        inheritDBot
          (__B, 0, __V, 0, __V',
            (inheritDTop (__B, 0, __V, 0, __V', (I.Null, d, d')))) in
      ((M.State (name', (M.Prefix (__G', __M', B'')), __V'))
        (* current first occurrence depth in V *)(* current first occurrence depth in V' *)
        (* mode dependency in Clause: first M.Top then M.Bot *)(* check proper traversal *))
      (* S' *)
    let rec abstractInit (State (name, GM, __V)) name' (Prefix
      (__G', __M', __B')) s' =
      inheritSplitDepth
        ((M.State (name, GM, __V)),
          (MetaAbstract.abstract
             (M.State
                ((name ^ name'), (M.Prefix (__G', __M', __B')),
                  (I.EClo (__V, s'))))))
    let rec abstractCont (__D, mode, b) abstract name' (Prefix
      (__G', __M', __B')) s' =
      abstract
        (name',
          (M.Prefix
             ((I.Decl (__G', (I.decSub (__D, s')))), (I.Decl (__M', mode)),
               (I.Decl (__B', b)))), (I.dot1 s'))
    let rec makeAddressInit (__S) k = (__S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec expand' __80__ __81__ __82__ __83__ =
      match (__80__, __81__, __82__, __83__) with
      | (Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | (Prefix
         (Decl (__G, __D), Decl (__M, (M.Top as mode)), Decl (__B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (__G', __M', __B'), s', ops) =
            expand'
              ((M.Prefix (__G, __M, __B)), (isIndexSucc (__D, isIndex)),
                (abstractCont ((__D, mode, b), abstract)),
                (makeAddressCont makeAddress)) in
          let Dec (xOpt, __V) = __D in
          let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
          let ops' =
            if (((b > 0) && ((not (isIndex 1)) && (checkDec (__M, __D))))
              (* check if splitting bound > 0 *))
            then
              ((makeAddress 1),
                (split ((M.Prefix (__G', __M', __B')), (__D, s'), abstract)))
                :: ops
            else ops in
          ((M.Prefix (__G', __M', __B')), (I.Dot ((I.Exp __X), s')), ops')
      | (Prefix
         (Decl (__G, __D), Decl (__M, (M.Bot as mode)), Decl (__B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (__G', __M', __B'), s', ops) =
            expand'
              ((((M.Prefix (__G, __M, __B)), (isIndexSucc (__D, isIndex)),
                  (abstractCont ((__D, mode, b), abstract)),
                  (makeAddressCont makeAddress)))
              (* -###- *)) in
          ((((M.Prefix
                ((I.Decl (__G', (I.decSub (__D, s')))),
                  (I.Decl (__M', M.Bot)), (I.Decl (__B', b)))), (I.dot1 s'),
              ops))
            (* b = 0 *))
    let rec expand (State (name, Prefix (__G, __M, __B), __V) as S) =
      let (_, _, ops) =
        expand'
          ((M.Prefix (__G, __M, __B)), isIndexInit, (abstractInit __S),
            (makeAddressInit __S)) in
      ops
    let rec index _ (Sl) = List.length Sl
    let rec apply _ (Sl) =
      map
        (function
         | Active (__S) -> __S
         | InActive -> raise (Error "Not applicable: leftover constraints"))
        Sl
    let rec menu (((State (name, Prefix (__G, __M, __B), __V), i), Sl) as Op)
      =
      let rec active __84__ __85__ =
        match (__84__, __85__) with
        | (nil, n) -> n
        | ((InActive)::__L, n) -> active (__L, n)
        | ((Active _)::__L, n) -> active (__L, (n + 1)) in
      let rec inactive __86__ __87__ =
        match (__86__, __87__) with
        | (nil, n) -> n
        | ((InActive)::__L, n) -> inactive (__L, (n + 1))
        | ((Active _)::__L, n) -> inactive (__L, n) in
      let rec indexToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let rec flagToString __88__ __89__ =
        match (__88__, __89__) with
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (__G, (I.ctxDec (__G, i)))) ^
           " (")
          ^ (indexToString (index Op)))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ")"
    let rec var (_, i) _ = i
    let expand = expand
    let apply = apply
    let var = var
    let index = index
    let menu = menu
  end ;;
