
module type TOMEGA  =
  sig
    type nonrec label = int
    type nonrec lemma = int
    type __Worlds =
      | Worlds of IntSyn.cid list 
    type __Quantifier =
      | Implicit 
      | Explicit 
    type __TC =
      | Abs of (IntSyn.__Dec * __TC) 
      | Conj of (__TC * __TC) 
      | Base of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) Order.__Order 
    type __For =
      | World of (__Worlds * __For) 
      | All of ((__Dec * __Quantifier) * __For) 
      | Ex of ((IntSyn.__Dec * __Quantifier) * __For) 
      | True 
      | And of (__For * __For) 
      | FClo of (__For * __Sub) 
      | FVar of (__Dec IntSyn.__Ctx * __For option ref) 
    and __Dec =
      | UDec of IntSyn.__Dec 
      | PDec of (string option * __For * __TC option * __TC option) 
    and __Prg =
      | Box of (__Worlds * __Prg) 
      | Lam of (__Dec * __Prg) 
      | New of __Prg 
      | Choose of __Prg 
      | PairExp of (IntSyn.__Exp * __Prg) 
      | PairBlock of (IntSyn.__Block * __Prg) 
      | PairPrg of (__Prg * __Prg) 
      | Unit 
      | Redex of (__Prg * __Spine) 
      | Rec of (__Dec * __Prg) 
      | Case of __Cases 
      | PClo of (__Prg * __Sub) 
      | Let of (__Dec * __Prg * __Prg) 
      | EVar of (__Dec IntSyn.__Ctx * __Prg option ref * __For * __TC option
      * __TC option * IntSyn.__Exp) 
      | Const of lemma 
      | Var of int 
      | LetPairExp of (IntSyn.__Dec * __Dec * __Prg * __Prg) 
      | LetUnit of (__Prg * __Prg) 
    and __Spine =
      | Nil 
      | AppExp of (IntSyn.__Exp * __Spine) 
      | AppBlock of (IntSyn.__Block * __Spine) 
      | AppPrg of (__Prg * __Spine) 
      | SClo of (__Spine * __Sub) 
    and __Sub =
      | Shift of int 
      | Dot of (__Front * __Sub) 
    and __Front =
      | Idx of int 
      | Prg of __Prg 
      | Exp of IntSyn.__Exp 
      | Block of IntSyn.__Block 
      | Undef 
    and __Cases =
      | Cases of (__Dec IntSyn.__Ctx * __Sub * __Prg) list 
    type __ConDec =
      | ForDec of (string * __For) 
      | ValDec of (string * __Prg * __For) 
    exception NoMatch 
    val coerceSub : __Sub -> IntSyn.__Sub
    val embedSub : IntSyn.__Sub -> __Sub
    val coerceCtx : __Dec IntSyn.__Ctx -> IntSyn.__Dec IntSyn.__Ctx
    val strengthenCtx :
      __Dec IntSyn.__Ctx -> (IntSyn.__Dec IntSyn.__Ctx * __Sub * __Sub)
    val embedCtx : IntSyn.__Dec IntSyn.__Ctx -> __Dec IntSyn.__Ctx
    val weakenSub : __Dec IntSyn.__Ctx -> __Sub
    val invertSub : __Sub -> __Sub
    val id : __Sub
    val shift : __Sub
    val dot1 : __Sub -> __Sub
    val dotEta : __Front -> __Sub -> __Sub
    val comp : __Sub -> __Sub -> __Sub
    val varSub : int -> __Sub -> __Front
    val decSub : __Dec -> __Sub -> __Dec
    val forSub : __For -> __Sub -> __For
    val whnfFor : __For -> __Sub -> (__For * __Sub)
    val normalizePrg : __Prg -> __Sub -> __Prg
    val normalizeSub : __Sub -> __Sub
    val derefPrg : __Prg -> __Prg
    val lemmaLookup : lemma -> __ConDec
    val lemmaName : string -> lemma
    val lemmaAdd : __ConDec -> lemma
    val lemmaSize : unit -> int
    val lemmaDef : lemma -> __Prg
    val lemmaFor : lemma -> __For
    val eqWorlds : __Worlds -> __Worlds -> bool
    val convFor : (__For * __Sub) -> (__For * __Sub) -> bool
    val newEVar : __Dec IntSyn.__Ctx -> __For -> __Prg
    val newEVarTC :
      __Dec IntSyn.__Ctx -> __For -> __TC option -> __TC option -> __Prg
    val ctxDec : __Dec IntSyn.__Ctx -> int -> __Dec
    val revCoerceSub : IntSyn.__Sub -> __Sub
    val revCoerceCtx : IntSyn.__Dec IntSyn.__Ctx -> __Dec IntSyn.__Ctx
    val coerceFront : __Front -> IntSyn.__Front
    val revCoerceFront : IntSyn.__Front -> __Front
    val deblockify :
      IntSyn.__Dec IntSyn.__Ctx -> (IntSyn.__Dec IntSyn.__Ctx * __Sub)
    val TCSub : __TC -> IntSyn.__Sub -> __TC
    val normalizeTC : __TC -> __TC
    val convTC : __TC -> __TC -> bool
    val transformTC :
      IntSyn.__Dec IntSyn.__Ctx -> __For -> int Order.__Order list -> __TC
  end;;




module Tomega(Tomega:sig module Whnf : WHNF module Conv : CONV end) : TOMEGA
  =
  struct
    exception Error of string 
    type nonrec label = int
    type nonrec lemma = int
    type __Worlds =
      | Worlds of IntSyn.cid list 
    type __Quantifier =
      | Implicit 
      | Explicit 
    type __TC =
      | Abs of (IntSyn.__Dec * __TC) 
      | Conj of (__TC * __TC) 
      | Base of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) Order.__Order 
    type __For =
      | World of (__Worlds * __For) 
      | All of ((__Dec * __Quantifier) * __For) 
      | Ex of ((IntSyn.__Dec * __Quantifier) * __For) 
      | True 
      | And of (__For * __For) 
      | FClo of (__For * __Sub) 
      | FVar of (__Dec IntSyn.__Ctx * __For option ref) 
    and __Dec =
      | UDec of IntSyn.__Dec 
      | PDec of (string option * __For * __TC option * __TC option) 
    and __Prg =
      | Box of (__Worlds * __Prg) 
      | Lam of (__Dec * __Prg) 
      | New of __Prg 
      | Choose of __Prg 
      | PairExp of (IntSyn.__Exp * __Prg) 
      | PairBlock of (IntSyn.__Block * __Prg) 
      | PairPrg of (__Prg * __Prg) 
      | Unit 
      | Redex of (__Prg * __Spine) 
      | Rec of (__Dec * __Prg) 
      | Case of __Cases 
      | PClo of (__Prg * __Sub) 
      | Let of (__Dec * __Prg * __Prg) 
      | EVar of (__Dec IntSyn.__Ctx * __Prg option ref * __For * __TC option
      * __TC option * IntSyn.__Exp) 
      | Const of lemma 
      | Var of int 
      | LetPairExp of (IntSyn.__Dec * __Dec * __Prg * __Prg) 
      | LetUnit of (__Prg * __Prg) 
    and __Spine =
      | Nil 
      | AppExp of (IntSyn.__Exp * __Spine) 
      | AppBlock of (IntSyn.__Block * __Spine) 
      | AppPrg of (__Prg * __Spine) 
      | SClo of (__Spine * __Sub) 
    and __Sub =
      | Shift of int 
      | Dot of (__Front * __Sub) 
    and __Front =
      | Idx of int 
      | Prg of __Prg 
      | Exp of IntSyn.__Exp 
      | Block of IntSyn.__Block 
      | Undef 
    and __Cases =
      | Cases of (__Dec IntSyn.__Ctx * __Sub * __Prg) list 
    type __ConDec =
      | ForDec of (string * __For) 
      | ValDec of (string * __Prg * __For) 
    exception NoMatch 
    module I = IntSyn
    module O = Order
    let maxLemma = Global.maxCid
    let lemmaArray =
      (Array.array ((maxLemma + 1), (ForDec ("", True))) : __ConDec
                                                             Array.array)
    let nextLemma = ref 0
    let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    let rec lemmaAdd lemmaDec =
      let lemma = !nextLemma in
      if lemma > maxLemma
      then
        raise
          (Error
             (((^) "Global signature size " Int.toString (maxLemma + 1)) ^
                " exceeded"))
      else
        (Array.update (lemmaArray, lemma, lemmaDec);
         (nextLemma := lemma) + 1;
         lemma)
    let rec lemmaSize () = !nextLemma
    let rec lemmaDef lemma =
      match lemmaLookup lemma with | ValDec (_, __P, _) -> __P
    let rec lemmaFor lemma =
      match lemmaLookup lemma with
      | ForDec (_, __F) -> __F
      | ValDec (_, _, __F) -> __F
    let rec lemmaName s = lemmaName' (!nextLemma) s
    let rec lemmaName' __0__ __1__ =
      match (__0__, __1__) with
      | ((-1), s) -> raise (Error "Function name not found")
      | (n, s) ->
          (match lemmaLookup n with
           | ForDec (s', __F) -> if s = s' then n else lemmaName' (n - 1) s
           | ValDec (s', __P, __F) ->
               if s = s' then n else lemmaName' (n - 1) s)
    let rec coerceFront =
      function
      | Idx k -> I.Idx k
      | Prg (__P) -> I.Undef
      | Exp (__M) -> I.Exp __M
      | Block (__B) -> I.Block __B
      | Undef -> I.Undef
    let rec embedFront =
      function
      | Idx k -> Idx k
      | Exp (__U) -> Exp __U
      | Block (__B) -> Block __B
      | I.Undef -> Undef
    let rec coerceSub =
      function
      | Shift n -> I.Shift n
      | Dot (Ft, t) -> I.Dot ((coerceFront Ft), (coerceSub t))
    let rec embedSub =
      function
      | Shift n -> Shift n
      | Dot (Ft, s) -> Dot ((embedFront Ft), (embedSub s))
    let rec revCoerceFront =
      function
      | Idx k -> Idx k
      | Exp (__M) -> Exp __M
      | Block b -> Block b
      | I.Undef -> Undef
    let rec revCoerceSub =
      function
      | Shift n -> Shift n
      | Dot (Ft, t) -> Dot ((revCoerceFront Ft), (revCoerceSub t))
    let rec revCoerceCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, (BDec (_, (__L, t)) as D)) ->
          I.Decl ((revCoerceCtx Psi), (UDec __D))
    let id = Shift 0
    let rec dotEta __2__ __3__ =
      match (__2__, __3__) with
      | ((Idx _ as Ft), s) -> Dot (Ft, s)
      | ((Exp (__U) as Ft), s) ->
          let Ft' = try Idx (Whnf.etaContract __U) with | Eta -> Ft in
          Dot (Ft', s)
      | ((Undef as Ft), s) -> Dot (Ft, s)
    let rec embedCtx =
      function
      | I.Null -> I.Null
      | Decl (__G, __D) -> I.Decl ((embedCtx __G), (UDec __D))
    let rec orderSub __4__ __5__ =
      match (__4__, __5__) with
      | (Arg ((__U, s1), (__V, s2)), s) ->
          O.Arg ((__U, (I.comp (s1, s))), (__V, (I.comp (s2, s))))
      | (Lex (__Os), s) -> O.Lex (map (fun (__O) -> orderSub (__O, s)) __Os)
      | (Simul (__Os), s) ->
          O.Simul (map (fun (__O) -> orderSub (__O, s)) __Os)
    let rec TCSub __6__ __7__ =
      match (__6__, __7__) with
      | (Base (__O), s) -> Base (orderSub (__O, s))
      | (Conj (TC1, TC2), s) -> Conj ((TCSub (TC1, s)), (TCSub (TC2, s)))
      | (Abs (__D, TC), s) ->
          Abs ((I.decSub (__D, s)), (TCSub (TC, (I.dot1 s))))
    let rec TCSubOpt __8__ __9__ =
      match (__8__, __9__) with
      | (None, s) -> None
      | (Some (TC), s) -> Some (TCSub (TC, s))
    let rec normalizeTC' =
      function
      | Arg (__Us, __Vs) ->
          O.Arg
            (((Whnf.normalize __Us), I.id), ((Whnf.normalize __Vs), I.id))
      | Lex (__Os) -> O.Lex (map normalizeTC' __Os)
      | Simul (__Os) -> O.Simul (map normalizeTC' __Os)
    let rec normalizeTC =
      function
      | Base (__O) -> Base (normalizeTC' __O)
      | Conj (TC1, TC2) -> Conj ((normalizeTC TC1), (normalizeTC TC2))
      | Abs (__D, TC) ->
          Abs ((Whnf.normalizeDec (__D, I.id)), (normalizeTC TC))
    let rec normalizeTCOpt =
      function | None -> None | Some (TC) -> Some (normalizeTC TC)
    let rec convTC' __10__ __11__ =
      match (__10__, __11__) with
      | (Arg (__Us1, _), Arg (__Us2, _)) -> Conv.conv (__Us1, __Us2)
      | (Lex (__Os1), Lex (__Os2)) -> convTCs (__Os1, __Os2)
      | (Simul (__Os1), Simul (__Os2)) -> convTCs (__Os1, __Os2)
    let rec convTCs __12__ __13__ =
      match (__12__, __13__) with
      | (nil, nil) -> true
      | ((__O1)::__L1, (__O2)::__L2) ->
          (convTC' (__O1, __O2)) && (convTCs (__L1, __L2))
    let rec convTC __14__ __15__ =
      match (__14__, __15__) with
      | (Base (__O), Base (__O')) -> convTC' (__O, __O')
      | (Conj (TC1, TC2), Conj (TC1', TC2')) ->
          (convTC (TC1, TC1')) && (convTC (TC2, TC2'))
      | (Abs (__D, TC), Abs (__D', TC')) ->
          (Conv.convDec ((__D, I.id), (__D', I.id))) && (convTC (TC, TC'))
      | _ -> false
    let rec convTCOpt __16__ __17__ =
      match (__16__, __17__) with
      | (None, None) -> true
      | (Some (TC1), Some (TC2)) -> convTC (TC1, TC2)
      | _ -> false
    let rec transformTC' __18__ __19__ =
      match (__18__, __19__) with
      | (__G, Arg k) ->
          let k' = ((I.ctxLength __G) - k) + 1 in
          let Dec (_, __V) = I.ctxDec (__G, k') in
          O.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__V, I.id))
      | (__G, Lex (__Os)) ->
          O.Lex (map (fun (__O) -> transformTC' (__G, __O)) __Os)
      | (__G, Simul (__Os)) ->
          O.Simul (map (fun (__O) -> transformTC' (__G, __O)) __Os)
    let rec transformTC __20__ __21__ __22__ =
      match (__20__, __21__, __22__) with
      | (__G, All ((UDec (__D), _), __F), __Os) ->
          Abs (__D, (transformTC ((I.Decl (__G, __D)), __F, __Os)))
      | (__G, And (__F1, __F2), (__O)::__Os) ->
          Conj
            ((transformTC (__G, __F1, [__O])),
              (transformTC (__G, __F2, __Os)))
      | (__G, Ex _, (__O)::[]) -> Base (transformTC' (__G, __O))
    let rec varSub __23__ __24__ =
      match (__23__, __24__) with
      | (1, Dot (Ft, t)) -> Ft
      | (n, Dot (Ft, t)) -> varSub ((n - 1), t)
      | (n, Shift k) -> Idx (n + k)
    let rec frontSub __25__ __26__ =
      match (__25__, __26__) with
      | (Idx n, t) -> varSub (n, t)
      | (Exp (__U), t) -> Exp (I.EClo (__U, (coerceSub t)))
      | (Prg (__P), t) -> Prg (PClo (__P, t))
      | (Block (__B), t) -> Block (I.blockSub (__B, (coerceSub t)))
    let rec comp __27__ __28__ =
      match (__27__, __28__) with
      | (Shift 0, t) -> t
      | (t, Shift 0) -> t
      | (Shift n, Dot (Ft, t)) -> comp ((Shift (n - 1)), t)
      | (Shift n, Shift m) -> Shift (n + m)
      | (Dot (Ft, t), t') -> Dot ((frontSub (Ft, t')), (comp (t, t')))
    let rec dot1 =
      function
      | Shift 0 as t -> t
      | t -> Dot ((Idx 1), (comp (t, (Shift 1))))
    let id = Shift 0
    let shift = Shift 1
    let rec weakenSub =
      function
      | I.Null -> id
      | Decl (Psi, (UDec _ as D)) -> dot1 (weakenSub Psi)
      | Decl (Psi, (PDec _ as D)) -> comp ((weakenSub Psi), shift)
    let rec forSub __29__ __30__ =
      match (__29__, __30__) with
      | (All ((__D, __Q), __F), t) ->
          All (((decSub (__D, t)), __Q), (forSub (__F, (dot1 t))))
      | (Ex ((__D, __Q), __F), t) ->
          Ex
            (((I.decSub (__D, (coerceSub t))), __Q),
              (forSub (__F, (dot1 t))))
      | (And (__F1, __F2), t) -> And ((forSub (__F1, t)), (forSub (__F2, t)))
      | (FClo (__F, t1), t2) -> forSub (__F, (comp (t1, t2)))
      | (World (__W, __F), t) -> World (__W, (forSub (__F, t)))
      | (True, _) -> True
    let rec decSub __31__ __32__ =
      match (__31__, __32__) with
      | (PDec (x, __F, TC1, None), t) ->
          let s = coerceSub t in
          PDec (x, (forSub (__F, t)), (TCSubOpt (TC1, s)), None)
      | (UDec (__D), t) -> UDec (I.decSub (__D, (coerceSub t)))
    let rec invertSub s =
      let rec getFrontIndex =
        function
        | Idx k -> Some k
        | Prg (__P) -> getPrgIndex __P
        | Exp (__U) -> getExpIndex __U
        | Block (__B) -> getBlockIndex __B
        | Undef -> None
      and getPrgIndex =
        function
        | Redex (Var k, Nil) -> Some k
        | Redex (__P, Nil) -> getPrgIndex __P
        | PClo (__P, t) ->
            (match getPrgIndex __P with
             | None -> None
             | Some i -> getFrontIndex (varSub (i, t)))
        | _ -> None(* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
      and getExpIndex =
        function
        | Root (BVar k, I.Nil) -> Some k
        | Redex (__U, I.Nil) -> getExpIndex __U
        | EClo (__U, t) ->
            (match getExpIndex __U with
             | None -> None
             | Some i -> getFrontIndex (revCoerceFront (I.bvarSub (i, t))))
        | Lam (Dec (_, __U1), __U2) as U ->
            (try Some (Whnf.etaContract __U) with | Whnf.Eta -> None)
        | _ -> None
      and getBlockIndex = function | Bidx k -> Some k | _ -> None in
      let rec lookup __33__ __34__ __35__ =
        match (__33__, __34__, __35__) with
        | (n, Shift _, p) -> None
        | (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Idx k, s'), p) ->
            if k = p then Some n else lookup ((n + 1), s', p) in
      let rec invertSub'' __36__ __37__ =
        match (__36__, __37__) with
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | Some k -> invertSub'' ((p - 1), (Dot ((Idx k), si)))
             | None -> invertSub'' ((p - 1), (Dot (Undef, si)))) in
      let rec invertSub' __38__ __39__ =
        match (__38__, __39__) with
        | (n, Shift p) -> invertSub'' (p, (Shift n))
        | (n, Dot (_, s')) -> invertSub' ((n + 1), s') in
      ((invertSub' (0, s))
        (* returns None if not found *)(* getPrgIndex returns None if it is not an index *)
        (* getExpIndex returns None if it is not an index *)
        (* getBlockIndex returns None if it is not an index *)(* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 None => lookup (n+1, s', p)
               | Some k => if (k=p) then Some n else lookup (n+1, s', p))
        *))
    let rec coerceCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, UDec (__D)) -> I.Decl ((coerceCtx Psi), __D)
      | Decl (Psi, PDec (x, _, _, _)) -> I.Decl ((coerceCtx Psi), (I.NDec x))
    let rec strengthenCtx (Psi) =
      let w = weakenSub Psi in let s = invertSub w in ((coerceCtx Psi), w, s)
    let rec convFor __40__ __41__ =
      match (__40__, __41__) with
      | ((True, _), (True, _)) -> true
      | ((All ((__D1, _), __F1), t1), (All ((__D2, _), __F2), t2)) ->
          (convDec ((__D1, t1), (__D2, t2))) &&
            (convFor ((__F1, (dot1 t1)), (__F2, (dot1 t2))))
      | ((Ex ((__D1, _), __F1), t1), (Ex ((__D2, _), __F2), t2)) ->
          (Conv.convDec ((__D1, (coerceSub t1)), (__D2, (coerceSub t2)))) &&
            (convFor ((__F1, (dot1 t1)), (__F2, (dot1 t2))))
      | ((And (__F1, F1'), t1), (And (__F2, F2'), t2)) ->
          (convFor ((__F1, t1), (__F2, t2))) &&
            (convFor ((F1', t1), (F2', t2)))
      | _ -> false
    let rec convDec __42__ __43__ =
      match (__42__, __43__) with
      | ((UDec (__D1), t1), (UDec (__D2), t2)) ->
          Conv.convDec ((__D1, (coerceSub t1)), (__D2, (coerceSub t2)))
      | ((PDec (_, __F1, TC1, TC1'), t1), (PDec (_, __F2, TC2, TC2'), t2)) ->
          (convFor ((__F1, t1), (__F2, t2));
           convTCOpt (TC1, TC1');
           convTCOpt (TC2, TC2'))
    let rec newEVar (Psi) (__F) =
      EVar
        (Psi, (ref None), __F, None, None,
          (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
    let rec newEVarTC (Psi) (__F) (TC) (TC') =
      EVar
        (Psi, (ref None), __F, TC, TC',
          (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
    let rec exists __44__ __45__ =
      match (__44__, __45__) with
      | (x, []) -> false
      | (x, y::__W2) -> (x = y) || (exists (x, __W2))
    let rec subset __46__ __47__ =
      match (__46__, __47__) with
      | ([], _) -> true
      | (x::__W1, __W2) -> (exists (x, __W2)) && (subset (__W1, __W2))
    let rec eqWorlds (Worlds (__W1)) (Worlds (__W2)) =
      (subset (__W1, __W2)) && (subset (__W2, __W1))
    let rec ctxDec (__G) k =
      let rec ctxDec' __48__ __49__ =
        match (__48__, __49__) with
        | (Decl (__G', UDec (Dec (x, __V'))), 1) ->
            UDec (I.Dec (x, (I.EClo (__V', (I.Shift k)))))
        | (Decl (__G', UDec (BDec (l, (c, s)))), 1) ->
            UDec (I.BDec (l, (c, (I.comp (s, (I.Shift k))))))
        | (Decl (__G', PDec (x, __F, TC1, TC2)), 1) ->
            PDec
              (x, (forSub (__F, (Shift k))), (TCSubOpt (TC1, (I.Shift k))),
                (TCSubOpt (TC2, (I.Shift k))))
        | (Decl (__G', _), k') -> ctxDec' (__G', (k' - 1)) in
      ((ctxDec' (__G, k))
        (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        (* ctxDec' (Null, k')  should not occur by invariant *))
    let rec mkInst =
      function
      | 0 -> nil
      | n -> (::) (I.Root ((I.BVar n), I.Nil)) mkInst (n - 1)
    let rec deblockify =
      function
      | I.Null -> (I.Null, id)
      | Decl (__G, BDec (x, (c, s))) ->
          let (__G', t') = deblockify __G in
          let (_, __L) = I.constBlock c in
          let n = List.length __L in
          let G'' = append (__G', (__L, (I.comp (s, (coerceSub t'))))) in
          let t'' = comp (t', (Shift n)) in
          let __I = I.Inst (mkInst n) in
          let t''' = Dot ((Block __I), t'') in (((G'', t'''))
            (* G' |- t' : G *)(* G'' = G', V1 ... Vn *)
            (* G'' |- t'' : G *)(* I = (n, n-1 ... 1)  *)
            (* G'' |- t''' : G, x:(c,s) *))
    let rec append __50__ __51__ =
      match (__50__, __51__) with
      | (__G', (nil, s)) -> __G'
      | (__G', ((__D)::__L, s)) ->
          append ((I.Decl (__G', (I.decSub (__D, s)))), (__L, (I.dot1 s)))
    let rec whnfFor __52__ =
      match __52__ with
      | (All (__D, _), t) as Ft -> Ft
      | (Ex (__D, __F), t) as Ft -> Ft
      | (And (__F1, __F2), t) as Ft -> Ft
      | (FClo (__F, t1), t2) -> whnfFor (__F, (comp (t1, t2)))
      | (World (__W, __F), t) as Ft -> Ft
      | (True, _) as Ft -> Ft
    let rec normalizePrg __53__ __54__ =
      match (__53__, __54__) with
      | (Var n, t) ->
          (match varSub (n, t) with
           | Prg (__P) -> __P
           | Idx _ -> raise Domain
           | Exp _ -> raise Domain
           | Block _ -> raise Domain
           | Undef -> raise Domain)
      | (PairExp (__U, __P'), t) ->
          PairExp
            ((Whnf.normalize (__U, (coerceSub t))), (normalizePrg (__P', t)))
      | (PairBlock (__B, __P'), t) ->
          PairBlock
            ((I.blockSub (__B, (coerceSub t))), (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (Unit, _) -> Unit
      | (EVar (_, { contents = Some (__P) }, _, _, _, _), t) -> PClo (__P, t)
      | ((EVar _ as P), t) -> PClo (__P, t)
      | (Lam (__D, __P), t) ->
          Lam ((normalizeDec (__D, t)), (normalizePrg (__P, (dot1 t))))
      | (Rec (__D, __P), t) ->
          Rec ((normalizeDec (__D, t)), (normalizePrg (__P, (dot1 t))))
      | (PClo (__P, t), t') -> normalizePrg (__P, (comp (t, t')))
    let rec normalizeSpine __55__ __56__ =
      match (__55__, __56__) with
      | (Nil, t) -> Nil
      | (AppExp (__U, __S), t) ->
          AppExp
            ((Whnf.normalize (__U, (coerceSub t))),
              (normalizeSpine (__S, t)))
      | (AppPrg (__P, __S), t) ->
          AppPrg ((normalizePrg (__P, t)), (normalizeSpine (__S, t)))
      | (AppBlock (__B, __S), t) ->
          AppBlock
            ((I.blockSub (__B, (coerceSub t))), (normalizeSpine (__S, t)))
      | (SClo (__S, t1), t2) -> normalizeSpine (__S, (comp (t1, t2)))
    let rec normalizeDec __57__ __58__ =
      match (__57__, __58__) with
      | (PDec (name, __F, TC1, None), t) ->
          PDec
            (name, (forSub (__F, t)),
              (normalizeTCOpt (TCSubOpt (TC1, (coerceSub t)))), None)
      | (UDec (__D), t) -> UDec (Whnf.normalizeDec (__D, (coerceSub t)))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (__P), s) ->
          Dot ((Prg (normalizePrg (__P, id))), (normalizeSub s))
      | Dot (Exp (__E), s) ->
          Dot ((Exp (Whnf.normalize (__E, I.id))), (normalizeSub s))
      | Dot (Block k, s) -> Dot ((Block k), (normalizeSub s))
      | Dot (Idx k, s) -> Dot ((Idx k), (normalizeSub s))
    let rec derefPrg =
      function
      | Var n -> Var n
      | PairExp (__U, __P') -> PairExp (__U, (derefPrg __P'))
      | PairBlock (__B, __P') -> PairBlock (__B, (derefPrg __P'))
      | PairPrg (__P1, __P2) -> PairPrg ((derefPrg __P1), (derefPrg __P2))
      | Unit -> Unit
      | EVar (_, { contents = Some (__P) }, _, _, _, _) -> __P
      | EVar _ as P -> __P
      | Lam (__D, __P) -> Lam ((derefDec __D), (derefPrg __P))
      | Rec (__D, __P) -> Rec ((derefDec __D), (derefPrg __P))
      | Redex (__P, __S) -> Redex ((derefPrg __P), (derefSpine __S))
      | Case (Cases (__Cs)) ->
          Case
            (Cases
               (flattenCases
                  (map
                     (fun (Psi) ->
                        fun s -> fun (__P) -> (Psi, s, (derefPrg __P))) __Cs)))
      | Let (__D, __P1, __P2) ->
          Let ((derefDec __D), (derefPrg __P1), (derefPrg __P2))
      | LetPairExp (__D1, __D2, __P1, __P2) ->
          LetPairExp
            (__D1, (derefDec __D2), (derefPrg __P1), (derefPrg __P2))
      | LetUnit (__P1, __P2) -> LetUnit ((derefPrg __P1), (derefPrg __P2))
    let rec flattenCases =
      function
      | (Psi, s, Case (Cases (__L)))::__Cs ->
          (@) (map
                 (fun (Psi') ->
                    fun s' -> fun (__P') -> (Psi', (comp (s, s')), __P'))
                 (flattenCases __L))
            flattenCases __Cs
      | (Psi, s, __P)::__Cs -> (::) (Psi, s, __P) flattenCases __Cs
      | nil -> nil
    let rec derefSpine =
      function
      | Nil -> Nil
      | AppExp (__U, __S) -> AppExp (__U, (derefSpine __S))
      | AppPrg (__P, __S) -> AppPrg ((derefPrg __P), (derefSpine __S))
      | AppBlock (__B, __S) -> AppBlock (__B, (derefSpine __S))
    let rec derefDec =
      function
      | PDec (name, __F, TC1, TC2) -> PDec (name, __F, TC1, TC2)
      | UDec (__D) -> UDec __D
    let lemmaLookup = lemmaLookup
    let lemmaAdd = lemmaAdd
    let lemmaSize = lemmaSize
    let lemmaDef = lemmaDef
    let lemmaName = lemmaName
    let lemmaFor = lemmaFor
    let coerceSub = coerceSub
    let coerceCtx = coerceCtx
    let strengthenCtx = strengthenCtx
    let embedCtx = embedCtx
    let id = id
    let shift = shift
    let comp = comp
    let dot1 = dot1
    let varSub = varSub
    let decSub = decSub
    let weakenSub = weakenSub
    let invertSub = invertSub
    let ctxDec = ctxDec
    let forSub = forSub
    let whnfFor = whnfFor
    let normalizePrg = normalizePrg
    let normalizeSub = normalizeSub
    let derefPrg = derefPrg
    let id = id
    let dotEta = dotEta
    let convFor = convFor
    let newEVar = newEVar
    let newEVarTC = newEVarTC
    let embedSub = embedSub
    let eqWorlds = eqWorlds
    let ctxDec = ctxDec
    let revCoerceSub = revCoerceSub
    let revCoerceCtx = revCoerceCtx
    let coerceFront = coerceFront
    let revCoerceFront = revCoerceFront
    let deblockify = deblockify
    let TCSub = TCSub
    let normalizeTC = normalizeTC
    let convTC = convTC
    let transformTC = transformTC
  end ;;




module Whnf = (Make_Whnf)(struct  end)
module Conv = (Make_Conv)(struct module Whnf = Whnf end)
module Tomega : TOMEGA =
  (Make_Tomega)(struct module Whnf = Whnf
                       module Conv = Conv end) ;;
