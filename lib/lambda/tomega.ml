
(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)
module type TOMEGA  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* make abstract *)
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
    (* C ::= (Psi' |> s |-> P)    *)
    type __ConDec =
      | ForDec of (string * __For) 
      | ValDec of (string * __Prg * __For) 
    (*      | f == P              *)
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
    val dotEta : (__Front * __Sub) -> __Sub
    val comp : (__Sub * __Sub) -> __Sub
    val varSub : (int * __Sub) -> __Front
    val decSub : (__Dec * __Sub) -> __Dec
    val forSub : (__For * __Sub) -> __For
    val whnfFor : (__For * __Sub) -> (__For * __Sub)
    val normalizePrg : (__Prg * __Sub) -> __Prg
    val normalizeSub : __Sub -> __Sub
    val derefPrg : __Prg -> __Prg
    val lemmaLookup : lemma -> __ConDec
    val lemmaName : string -> lemma
    val lemmaAdd : __ConDec -> lemma
    val lemmaSize : unit -> int
    val lemmaDef : lemma -> __Prg
    val lemmaFor : lemma -> __For
    val eqWorlds : (__Worlds * __Worlds) -> bool
    val convFor : ((__For * __Sub) * (__For * __Sub)) -> bool
    val newEVar : (__Dec IntSyn.__Ctx * __For) -> __Prg
    val newEVarTC :
      (__Dec IntSyn.__Ctx * __For * __TC option * __TC option) -> __Prg
    (* Below are added by Yu Liao *)
    val ctxDec : (__Dec IntSyn.__Ctx * int) -> __Dec
    val revCoerceSub : IntSyn.__Sub -> __Sub
    val revCoerceCtx : IntSyn.__Dec IntSyn.__Ctx -> __Dec IntSyn.__Ctx
    (* Added references by ABP *)
    val coerceFront : __Front -> IntSyn.__Front
    val revCoerceFront : IntSyn.__Front -> __Front
    val deblockify :
      IntSyn.__Dec IntSyn.__Ctx -> (IntSyn.__Dec IntSyn.__Ctx * __Sub)
    (* Stuff that has to do with termination conditions *)
    val TCSub : (__TC * IntSyn.__Sub) -> __TC
    val normalizeTC : __TC -> __TC
    val convTC : (__TC * __TC) -> bool
    val transformTC :
      (IntSyn.__Dec IntSyn.__Ctx * __For * int Order.__Order list) -> __TC
  end;;




(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)
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
    (* C ::= (Psi' |> s |-> P)    *)
    type __ConDec =
      | ForDec of (string * __For) 
      | ValDec of (string * __Prg * __For) 
    (*      | f == P              *)
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
      match lemmaLookup lemma with | ValDec (_, P, _) -> P
    let rec lemmaFor lemma =
      match lemmaLookup lemma with
      | ForDec (_, F) -> F
      | ValDec (_, _, F) -> F
    let rec lemmaName s = lemmaName' (!nextLemma) s
    let rec lemmaName' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((-1), s) -> raise (Error "Function name not found")
      | (n, s) ->
          (match lemmaLookup n with
           | ForDec (s', F) -> if s = s' then n else lemmaName' (n - 1) s
           | ValDec (s', P, F) -> if s = s' then n else lemmaName' (n - 1) s)
    let rec coerceFront =
      function
      | Idx k -> I.Idx k
      | Prg (P) -> I.Undef
      | Exp (M) -> I.Exp M
      | Block (B) -> I.Block B
      | Undef -> I.Undef
    let rec embedFront =
      function
      | Idx k -> Idx k
      | Exp (__u) -> Exp __u
      | Block (B) -> Block B
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
      | Exp (M) -> Exp M
      | Block b -> Block b
      | I.Undef -> Undef
    let rec revCoerceSub =
      function
      | Shift n -> Shift n
      | Dot (Ft, t) -> Dot ((revCoerceFront Ft), (revCoerceSub t))
    let rec revCoerceCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, (BDec (_, (__l, t)) as __d)) ->
          I.Decl ((revCoerceCtx Psi), (UDec __d))
    let id = Shift 0
    let rec dotEta =
      function
      | ((Idx _ as Ft), s) -> Dot (Ft, s)
      | ((Exp (__u) as Ft), s) ->
          let Ft' = try Idx (Whnf.etaContract __u) with | Eta -> Ft in
          Dot (Ft', s)
      | ((Undef as Ft), s) -> Dot (Ft, s)
    let rec embedCtx =
      function
      | I.Null -> I.Null
      | Decl (__g, __d) -> I.Decl ((embedCtx __g), (UDec __d))
    let rec orderSub =
      function
      | (Arg ((__u, s1), (__v, s2)), s) ->
          O.Arg ((__u, (I.comp (s1, s))), (__v, (I.comp (s2, s))))
      | (Lex (__Os), s) -> O.Lex (map (function | O -> orderSub (O, s)) __Os)
      | (Simul (__Os), s) -> O.Simul (map (function | O -> orderSub (O, s)) __Os)
    let rec TCSub =
      function
      | (Base (O), s) -> Base (orderSub (O, s))
      | (Conj (TC1, TC2), s) -> Conj ((TCSub (TC1, s)), (TCSub (TC2, s)))
      | (Abs (__d, TC), s) -> Abs ((I.decSub (__d, s)), (TCSub (TC, (I.dot1 s))))
    let rec TCSubOpt =
      function | (None, s) -> None | (Some (TC), s) -> Some (TCSub (TC, s))
    let rec normalizeTC' =
      function
      | Arg (__Us, __Vs) ->
          O.Arg (((Whnf.normalize __Us), I.id), ((Whnf.normalize __Vs), I.id))
      | Lex (__Os) -> O.Lex (map normalizeTC' __Os)
      | Simul (__Os) -> O.Simul (map normalizeTC' __Os)
    let rec normalizeTC =
      function
      | Base (O) -> Base (normalizeTC' O)
      | Conj (TC1, TC2) -> Conj ((normalizeTC TC1), (normalizeTC TC2))
      | Abs (__d, TC) -> Abs ((Whnf.normalizeDec (__d, I.id)), (normalizeTC TC))
    let rec normalizeTCOpt =
      function | None -> None | Some (TC) -> Some (normalizeTC TC)
    let rec convTC' =
      function
      | (Arg (us1, _), Arg (us2, _)) -> Conv.conv (us1, us2)
      | (Lex (Os1), Lex (Os2)) -> convTCs (Os1, Os2)
      | (Simul (Os1), Simul (Os2)) -> convTCs (Os1, Os2)
    let rec convTCs =
      function
      | (nil, nil) -> true__
      | ((O1)::L1, (O2)::L2) -> (convTC' (O1, O2)) && (convTCs (L1, L2))
    let rec convTC =
      function
      | (Base (O), Base (O')) -> convTC' (O, O')
      | (Conj (TC1, TC2), Conj (TC1', TC2')) ->
          (convTC (TC1, TC1')) && (convTC (TC2, TC2'))
      | (Abs (__d, TC), Abs (__d', TC')) ->
          (Conv.convDec ((__d, I.id), (__d', I.id))) && (convTC (TC, TC'))
      | _ -> false__
    let rec convTCOpt =
      function
      | (None, None) -> true__
      | (Some (TC1), Some (TC2)) -> convTC (TC1, TC2)
      | _ -> false__
    let rec transformTC' =
      function
      | (__g, Arg k) ->
          let k' = ((I.ctxLength __g) - k) + 1 in
          let Dec (_, __v) = I.ctxDec (__g, k') in
          O.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__v, I.id))
      | (__g, Lex (__Os)) -> O.Lex (map (function | O -> transformTC' (__g, O)) __Os)
      | (__g, Simul (__Os)) ->
          O.Simul (map (function | O -> transformTC' (__g, O)) __Os)
    let rec transformTC =
      function
      | (__g, All ((UDec (__d), _), F), __Os) ->
          Abs (__d, (transformTC ((I.Decl (__g, __d)), F, __Os)))
      | (__g, And (__F1, __F2), (O)::__Os) ->
          Conj ((transformTC (__g, __F1, [O])), (transformTC (__g, __F2, __Os)))
      | (__g, Ex _, (O)::[]) -> Base (transformTC' (__g, O))
    let rec varSub =
      function
      | (1, Dot (Ft, t)) -> Ft
      | (n, Dot (Ft, t)) -> varSub ((n - 1), t)
      | (n, Shift k) -> Idx (n + k)
    let rec frontSub =
      function
      | (Idx n, t) -> varSub (n, t)
      | (Exp (__u), t) -> Exp (I.EClo (__u, (coerceSub t)))
      | (Prg (P), t) -> Prg (PClo (P, t))
      | (Block (B), t) -> Block (I.blockSub (B, (coerceSub t)))
    let rec comp =
      function
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
      | Decl (Psi, (UDec _ as __d)) -> dot1 (weakenSub Psi)
      | Decl (Psi, (PDec _ as __d)) -> comp ((weakenSub Psi), shift)
    let rec forSub =
      function
      | (All ((__d, Q), F), t) ->
          All (((decSub (__d, t)), Q), (forSub (F, (dot1 t))))
      | (Ex ((__d, Q), F), t) ->
          Ex (((I.decSub (__d, (coerceSub t))), Q), (forSub (F, (dot1 t))))
      | (And (__F1, __F2), t) -> And ((forSub (__F1, t)), (forSub (__F2, t)))
      | (FClo (F, t1), t2) -> forSub (F, (comp (t1, t2)))
      | (World (W, F), t) -> World (W, (forSub (F, t)))
      | (True, _) -> True
    let rec decSub =
      function
      | (PDec (x, F, TC1, None), t) ->
          let s = coerceSub t in
          PDec (x, (forSub (F, t)), (TCSubOpt (TC1, s)), None)
      | (UDec (__d), t) -> UDec (I.decSub (__d, (coerceSub t)))
    let rec invertSub s =
      let rec getFrontIndex =
        function
        | Idx k -> Some k
        | Prg (P) -> getPrgIndex P
        | Exp (__u) -> getExpIndex __u
        | Block (B) -> getBlockIndex B
        | Undef -> None
      and getPrgIndex =
        function
        | Redex (Var k, Nil) -> Some k
        | Redex (P, Nil) -> getPrgIndex P
        | PClo (P, t) ->
            (match getPrgIndex P with
             | None -> None
             | Some i -> getFrontIndex (varSub (i, t)))
        | _ -> None
      and getExpIndex =
        function
        | Root (BVar k, I.Nil) -> Some k
        | Redex (__u, I.Nil) -> getExpIndex __u
        | EClo (__u, t) ->
            (match getExpIndex __u with
             | None -> None
             | Some i -> getFrontIndex (revCoerceFront (I.bvarSub (i, t))))
        | Lam (Dec (_, __U1), __U2) as __u ->
            (try Some (Whnf.etaContract __u) with | Whnf.Eta -> None)
        | _ -> None
      and getBlockIndex = function | Bidx k -> Some k | _ -> None in
      let rec lookup =
        function
        | (n, Shift _, p) -> None
        | (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Idx k, s'), p) ->
            if k = p then Some n else lookup ((n + 1), s', p) in
      let rec invertSub'' =
        function
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | Some k -> invertSub'' ((p - 1), (Dot ((Idx k), si)))
             | None -> invertSub'' ((p - 1), (Dot (Undef, si)))) in
      let rec invertSub' =
        function
        | (n, Shift p) -> invertSub'' (p, (Shift n))
        | (n, Dot (_, s')) -> invertSub' ((n + 1), s') in
      invertSub' (0, s)
    let rec coerceCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, UDec (__d)) -> I.Decl ((coerceCtx Psi), __d)
      | Decl (Psi, PDec (x, _, _, _)) -> I.Decl ((coerceCtx Psi), (I.NDec x))
    let rec strengthenCtx (Psi) =
      let w = weakenSub Psi in let s = invertSub w in ((coerceCtx Psi), w, s)
    let rec convFor =
      function
      | ((True, _), (True, _)) -> true__
      | ((All ((D1, _), __F1), t1), (All ((D2, _), __F2), t2)) ->
          (convDec ((D1, t1), (D2, t2))) &&
            (convFor ((__F1, (dot1 t1)), (__F2, (dot1 t2))))
      | ((Ex ((D1, _), __F1), t1), (Ex ((D2, _), __F2), t2)) ->
          (Conv.convDec ((D1, (coerceSub t1)), (D2, (coerceSub t2)))) &&
            (convFor ((__F1, (dot1 t1)), (__F2, (dot1 t2))))
      | ((And (__F1, __F1'), t1), (And (__F2, __F2'), t2)) ->
          (convFor ((__F1, t1), (__F2, t2))) && (convFor ((__F1', t1), (__F2', t2)))
      | _ -> false__
    let rec convDec =
      function
      | ((UDec (D1), t1), (UDec (D2), t2)) ->
          Conv.convDec ((D1, (coerceSub t1)), (D2, (coerceSub t2)))
      | ((PDec (_, __F1, TC1, TC1'), t1), (PDec (_, __F2, TC2, TC2'), t2)) ->
          (convFor ((__F1, t1), (__F2, t2));
           convTCOpt (TC1, TC1');
           convTCOpt (TC2, TC2'))
    let rec newEVar (Psi, F) =
      EVar
        (Psi, (ref None), F, None, None,
          (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
    let rec newEVarTC (Psi, F, TC, TC') =
      EVar
        (Psi, (ref None), F, TC, TC',
          (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
    let rec exists =
      function
      | (x, []) -> false__
      | (x, y::W2) -> (x = y) || (exists (x, W2))
    let rec subset =
      function
      | ([], _) -> true__
      | (x::W1, W2) -> (exists (x, W2)) && (subset (W1, W2))
    let rec eqWorlds (Worlds (W1), Worlds (W2)) =
      (subset (W1, W2)) && (subset (W2, W1))
    let rec ctxDec (__g, k) =
      let rec ctxDec' =
        function
        | (Decl (__g', UDec (Dec (x, __v'))), 1) ->
            UDec (I.Dec (x, (I.EClo (__v', (I.Shift k)))))
        | (Decl (__g', UDec (BDec (l, (c, s)))), 1) ->
            UDec (I.BDec (l, (c, (I.comp (s, (I.Shift k))))))
        | (Decl (__g', PDec (x, F, TC1, TC2)), 1) ->
            PDec
              (x, (forSub (F, (Shift k))), (TCSubOpt (TC1, (I.Shift k))),
                (TCSubOpt (TC2, (I.Shift k))))
        | (Decl (__g', _), k') -> ctxDec' (__g', (k' - 1)) in
      ctxDec' (__g, k)
    let rec mkInst =
      function
      | 0 -> nil
      | n -> (::) (I.Root ((I.BVar n), I.Nil)) mkInst (n - 1)
    let rec deblockify =
      function
      | I.Null -> (I.Null, id)
      | Decl (__g, BDec (x, (c, s))) ->
          let (__g', t') = deblockify __g in
          let (_, __l) = I.constBlock c in
          let n = List.length __l in
          let __g'' = append (__g', (__l, (I.comp (s, (coerceSub t'))))) in
          let t'' = comp (t', (Shift n)) in
          let I = I.Inst (mkInst n) in
          let t''' = Dot ((Block I), t'') in (__g'', t''')
    let rec append =
      function
      | (__g', (nil, s)) -> __g'
      | (__g', ((__d)::__l, s)) ->
          append ((I.Decl (__g', (I.decSub (__d, s)))), (__l, (I.dot1 s)))
    let rec whnfFor =
      function
      | (All (__d, _), t) as Ft -> Ft
      | (Ex (__d, F), t) as Ft -> Ft
      | (And (__F1, __F2), t) as Ft -> Ft
      | (FClo (F, t1), t2) -> whnfFor (F, (comp (t1, t2)))
      | (World (W, F), t) as Ft -> Ft
      | (True, _) as Ft -> Ft
    let rec normalizePrg =
      function
      | (Var n, t) ->
          (match varSub (n, t) with
           | Prg (P) -> P
           | Idx _ -> raise Domain
           | Exp _ -> raise Domain
           | Block _ -> raise Domain
           | Undef -> raise Domain)
      | (PairExp (__u, __P'), t) ->
          PairExp
            ((Whnf.normalize (__u, (coerceSub t))), (normalizePrg (__P', t)))
      | (PairBlock (B, __P'), t) ->
          PairBlock ((I.blockSub (B, (coerceSub t))), (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (Unit, _) -> Unit
      | (EVar (_, ref (Some (P)), _, _, _, _), t) -> PClo (P, t)
      | ((EVar _ as P), t) -> PClo (P, t)
      | (Lam (__d, P), t) ->
          Lam ((normalizeDec (__d, t)), (normalizePrg (P, (dot1 t))))
      | (Rec (__d, P), t) ->
          Rec ((normalizeDec (__d, t)), (normalizePrg (P, (dot1 t))))
      | (PClo (P, t), t') -> normalizePrg (P, (comp (t, t')))
    let rec normalizeSpine =
      function
      | (Nil, t) -> Nil
      | (AppExp (__u, S), t) ->
          AppExp
            ((Whnf.normalize (__u, (coerceSub t))), (normalizeSpine (S, t)))
      | (AppPrg (P, S), t) ->
          AppPrg ((normalizePrg (P, t)), (normalizeSpine (S, t)))
      | (AppBlock (B, S), t) ->
          AppBlock ((I.blockSub (B, (coerceSub t))), (normalizeSpine (S, t)))
      | (SClo (S, t1), t2) -> normalizeSpine (S, (comp (t1, t2)))
    let rec normalizeDec =
      function
      | (PDec (name, F, TC1, None), t) ->
          PDec
            (name, (forSub (F, t)),
              (normalizeTCOpt (TCSubOpt (TC1, (coerceSub t)))), None)
      | (UDec (__d), t) -> UDec (Whnf.normalizeDec (__d, (coerceSub t)))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (P), s) ->
          Dot ((Prg (normalizePrg (P, id))), (normalizeSub s))
      | Dot (Exp (E), s) ->
          Dot ((Exp (Whnf.normalize (E, I.id))), (normalizeSub s))
      | Dot (Block k, s) -> Dot ((Block k), (normalizeSub s))
      | Dot (Idx k, s) -> Dot ((Idx k), (normalizeSub s))
    let rec derefPrg =
      function
      | Var n -> Var n
      | PairExp (__u, __P') -> PairExp (__u, (derefPrg __P'))
      | PairBlock (B, __P') -> PairBlock (B, (derefPrg __P'))
      | PairPrg (__P1, __P2) -> PairPrg ((derefPrg __P1), (derefPrg __P2))
      | Unit -> Unit
      | EVar (_, ref (Some (P)), _, _, _, _) -> P
      | EVar _ as P -> P
      | Lam (__d, P) -> Lam ((derefDec __d), (derefPrg P))
      | Rec (__d, P) -> Rec ((derefDec __d), (derefPrg P))
      | Redex (P, S) -> Redex ((derefPrg P), (derefSpine S))
      | Case (Cases (__Cs)) ->
          Case
            (Cases
               (flattenCases
                  (map (function | (Psi, s, P) -> (Psi, s, (derefPrg P))) __Cs)))
      | Let (__d, __P1, __P2) -> Let ((derefDec __d), (derefPrg __P1), (derefPrg __P2))
      | LetPairExp (D1, D2, __P1, __P2) ->
          LetPairExp (D1, (derefDec D2), (derefPrg __P1), (derefPrg __P2))
      | LetUnit (__P1, __P2) -> LetUnit ((derefPrg __P1), (derefPrg __P2))
    let rec flattenCases =
      function
      | (Psi, s, Case (Cases (__l)))::__Cs ->
          (@) (map (function | (Psi', s', __P') -> (Psi', (comp (s, s')), __P'))
                 (flattenCases __l))
            flattenCases __Cs
      | (Psi, s, P)::__Cs -> (::) (Psi, s, P) flattenCases __Cs
      | nil -> nil
    let rec derefSpine =
      function
      | Nil -> Nil
      | AppExp (__u, S) -> AppExp (__u, (derefSpine S))
      | AppPrg (P, S) -> AppPrg ((derefPrg P), (derefSpine S))
      | AppBlock (B, S) -> AppBlock (B, (derefSpine S))
    let rec derefDec =
      function
      | PDec (name, F, TC1, TC2) -> PDec (name, F, TC1, TC2)
      | UDec (__d) -> UDec __d
    (* not very efficient, improve !!! *)
    (* coerceFront F = __F'

       Invariant:
       If    Psi |- F front
       and   __g = mu G. __g \in Psi
       then  __g   |- __F' front
    *)
    (* --Yu Liao Why cases: Block, Undef aren't defined *)
    (* embedFront F = __F'

       Invariant:
       If    Psi |- F front
       and   __g = mu G. __g \in Psi
       then  __g   |- __F' front
    *)
    (* coerceSub t = s

       Invariant:
       If    Psi |- t : Psi'
       then  __g   |- s : __g'
       where __g = mu G. __g \in Psi
       and   __g' = mu G. __g \in Psi'
    *)
    (* Definition:
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)
    (* revCoerceSub t = s
    coerce substitution in LF level t ==> s in Tomega level *)
    (* Invariant Yu? *)
    (* dotEta (Ft, s) = s'

       Invariant:
       If   __g |- s : G1, __v  and __g |- Ft : __v [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  __g |- s' : G1, __v
    *)
    (* embedCtx __g = Psi

       Invariant:
       If   __g is an LF ctx
       then Psi is __g, embedded into Tomega
    *)
    (* orderSub (O, s) = O'

         Invariant:
         If   __g' |- O order    and    __g |- s : __g'
         then __g |- O' order
         and  __g |- O' == O[s] order
      *)
    (* normalizeTC (O) = O'

         Invariant:
         If   __g |- O TC
         then __g |- O' TC
         and  __g |- O = O' TC
         and  each sub term of O' is in normal form.
      *)
    (* convTC (O1, O2) = B'

         Invariant:
         If   __g |- O1 TC
         and  __g |- O2 TC
         then B' holds iff __g |- O1 == O2 TC
      *)
    (* bvarSub (n, t) = Ft'

       Invariant:
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)
    (* frontSub (Ft, t) = Ft'

       Invariant:
       If   Psi |- Ft :: F
       and  Psi' |- t :: Psi
       then Ft' = Ft[t]
       and  Psi' |- Ft' :: F[t]
    *)
    (* Block case is missing --cs *)
    (* comp (t1, t2) = t

       Invariant:
       If   Psi'' |- t2 :: Psi'
       and  Psi' |- t1 :: Psi
       then t = t1 o t2
       and  Psi'' |- t1 o t2 :: Psi'
    *)
    (* dot1 (t) = t'

       Invariant:
       If   __g |- t : __g'
       then t' = 1. (t o ^)
       and  for all __v t.t.  __g' |- __v : __l
            __g, __v[t] |- t' : __g', __v

       If t patsub then t' patsub
    *)
    (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then __g is embed Psi
       and  Psi |- w : __g
    *)
    (* forSub (F, t) = __F'

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- __F' = F[t] for
    *)
    (* decSub (x::F, t) = __d'

       Invariant:
       If   Psi  |- t : Psi'    Psi' |- F formula
       then __d' = x:F[t]
       and  Psi  |- F[t] formula
    *)
    (* invertSub s = s'

       Invariant:
       If   __g |- s : __g'    (and s patsub)
       then __g' |- s' : __g
       s.t. s o s' = id
    *)
    (* returns None if not found *)
    (* getPrgIndex returns None if it is not an index *)
    (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
    (* getExpIndex returns None if it is not an index *)
    (* getBlockIndex returns None if it is not an index *)
    (* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 None => lookup (n+1, s', p)
               | Some k => if (k=p) then Some n else lookup (n+1, s', p))
        *)
    (* coerceCtx (Psi) = __g

       Invariant:
       If   |- Psi ctx[block]
       then |- __g lf-ctx[block]
       and  |- Psi == __g
    *)
    (* coerceCtx (Psi) = (__g, s)

       Invariant:
       If   |- Psi ctx[block]
       then |- __g lf-ctx[block]
       and  |- Psi == __g
       and  __g |- s : Psi
    *)
    (* convFor ((__F1, t1), (__F2, t2)) = B

       Invariant:
       If   __g |- t1 : G1
       and  G1 |- __F1 : formula
       and  __g |- t2 : G2
       and  G2 |- __F2 : formula
       and  (__F1, __F2 do not contain abstraction over contextblocks )
       then B holds iff __g |- __F1[s1] = __F2[s2] formula
    *)
    (* newEVar (__g, __v) = newEVarCnstr (__g, __v, nil) *)
    (* ctxDec (__g, k) = x:__v
     Invariant:
     If      |__g| >= k, where |__g| is size of __g,
     then    __g |- k : __v  and  __g |- __v : __l
  *)
    (* ctxDec' (__g'', k') = x:__v
             where __g |- ^(k-k') : __g'', 1 <= k' <= k
           *)
    (* ctxDec' (Null, k')  should not occur by invariant *)
    (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)
    (* deblockify __g = (__g', t')

       Invariant:
       If   |- __g ctx
       then __g' |- t' : __g
    *)
    (* __g' |- t' : __g *)
    (* __g'' = __g', V1 ... Vn *)
    (* __g'' |- t'' : __g *)
    (* I = (n, n-1 ... 1)  *)
    (* __g'' |- t''' : __g, x:(c,s) *)
    (* whnfFor (F, t) = (__F', t')

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- __F' :for
       and   Psi' |- __F'[t'] = F[t] for
    *)
    (* normalizePrg (P, t) = (__P', t')

       Invariant:
       If   Psi' |- __v :: F
       and  Psi' |- __v value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', __F'
       s.t. Psi'' |- __F' for
       and  Psi'' |- __P' :: __F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == __F' [t']
       and  Psi |- P [t] == __P' [t'] : F [t]
       and  Psi |- __P' [t'] :nf: F [t]
    *)
    (* derefPrg (P, t) = (__P', t')

       Invariant:
       If   Psi' |- __v :: F
       and  Psi' |- __v value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', __F'
       s.t. Psi'' |- __F' for
       and  Psi'' |- __P' :: __F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == __F' [t']
       and  Psi |- P [t] == __P' [t'] : F [t]
       and  Psi |- __P' [t'] :nf: F [t]
    *)
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
    (* Below are added by Yu Liao *)
    let embedSub = embedSub
    let eqWorlds = eqWorlds
    let ctxDec = ctxDec
    let revCoerceSub = revCoerceSub
    let revCoerceCtx = revCoerceCtx
    (* Added referenced by ABP *)
    let coerceFront = coerceFront
    let revCoerceFront = revCoerceFront
    let deblockify = deblockify
    (* Stuff that has to do with termination conditions *)
    let TCSub = TCSub
    let normalizeTC = normalizeTC
    let convTC = convTC
    let transformTC = transformTC
  end ;;




module Whnf = (Make_Whnf)(struct  end)
module Conv =
  (Make_Conv)(struct
                (*! structure IntSyn' = IntSyn !*)
                module Whnf = Whnf
              end)
module Tomega : TOMEGA =
  (Make_Tomega)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  module Whnf = Whnf
                  module Conv = Conv
                end) ;;
