module type TOMEGA  =
  sig
    type nonrec label = int
    type nonrec lemma = int
    type worlds_ =
      | Worlds of IntSyn.cid list 
    type quantifier_ =
      | Implicit 
      | Explicit 
    type tC_ =
      | Abs of (IntSyn.dec_ * tC_) 
      | Conj of (tC_ * tC_) 
      | Base of ((IntSyn.exp_ * IntSyn.sub_) * (IntSyn.exp_ * IntSyn.sub_))
      Order.order_ 
    type for_ =
      | World of (worlds_ * for_) 
      | All of ((dec_ * quantifier_) * for_) 
      | Ex of ((IntSyn.dec_ * quantifier_) * for_) 
      | True 
      | And of (for_ * for_) 
      | FClo of (for_ * sub_) 
      | FVar of (dec_ IntSyn.ctx_ * for_ option ref) 
    and dec_ =
      | UDec of IntSyn.dec_ 
      | PDec of (string option * for_ * tC_ option * tC_ option) 
    and prg_ =
      | Box of (worlds_ * prg_) 
      | Lam of (dec_ * prg_) 
      | New of prg_ 
      | Choose of prg_ 
      | PairExp of (IntSyn.exp_ * prg_) 
      | PairBlock of (IntSyn.block_ * prg_) 
      | PairPrg of (prg_ * prg_) 
      | Unit 
      | Redex of (prg_ * spine_) 
      | Rec of (dec_ * prg_) 
      | Case of cases_ 
      | PClo of (prg_ * sub_) 
      | Let of (dec_ * prg_ * prg_) 
      | EVar of (dec_ IntSyn.ctx_ * prg_ option ref * for_ * tC_ option * tC_
      option * IntSyn.exp_) 
      | Const of lemma 
      | Var of int 
      | LetPairExp of (IntSyn.dec_ * dec_ * prg_ * prg_) 
      | LetUnit of (prg_ * prg_) 
    and spine_ =
      | Nil 
      | AppExp of (IntSyn.exp_ * spine_) 
      | AppBlock of (IntSyn.block_ * spine_) 
      | AppPrg of (prg_ * spine_) 
      | SClo of (spine_ * sub_) 
    and sub_ =
      | Shift of int 
      | Dot of (front_ * sub_) 
    and front_ =
      | Idx of int 
      | Prg of prg_ 
      | Exp of IntSyn.exp_ 
      | Block of IntSyn.block_ 
      | Undef 
    and cases_ =
      | Cases of (dec_ IntSyn.ctx_ * sub_ * prg_) list 
    type conDec_ =
      | ForDec of (string * for_) 
      | ValDec of (string * prg_ * for_) 
    exception NoMatch 
    val coerceSub : sub_ -> IntSyn.sub_
    val embedSub : IntSyn.sub_ -> sub_
    val coerceCtx : dec_ IntSyn.ctx_ -> IntSyn.dec_ IntSyn.ctx_
    val strengthenCtx :
      dec_ IntSyn.ctx_ -> (IntSyn.dec_ IntSyn.ctx_ * sub_ * sub_)
    val embedCtx : IntSyn.dec_ IntSyn.ctx_ -> dec_ IntSyn.ctx_
    val weakenSub : dec_ IntSyn.ctx_ -> sub_
    val invertSub : sub_ -> sub_
    val id : sub_
    val shift : sub_
    val dot1 : sub_ -> sub_
    val dotEta : (front_ * sub_) -> sub_
    val comp : (sub_ * sub_) -> sub_
    val varSub : (int * sub_) -> front_
    val decSub : (dec_ * sub_) -> dec_
    val forSub : (for_ * sub_) -> for_
    val whnfFor : (for_ * sub_) -> (for_ * sub_)
    val normalizePrg : (prg_ * sub_) -> prg_
    val normalizeSub : sub_ -> sub_
    val derefPrg : prg_ -> prg_
    val lemmaLookup : lemma -> conDec_
    val lemmaName : string -> lemma
    val lemmaAdd : conDec_ -> lemma
    val lemmaSize : unit -> int
    val lemmaDef : lemma -> prg_
    val lemmaFor : lemma -> for_
    val eqWorlds : (worlds_ * worlds_) -> bool
    val convFor : ((for_ * sub_) * (for_ * sub_)) -> bool
    val newEVar : (dec_ IntSyn.ctx_ * for_) -> prg_
    val newEVarTC :
      (dec_ IntSyn.ctx_ * for_ * tC_ option * tC_ option) -> prg_
    val ctxDec : (dec_ IntSyn.ctx_ * int) -> dec_
    val revCoerceSub : IntSyn.sub_ -> sub_
    val revCoerceCtx : IntSyn.dec_ IntSyn.ctx_ -> dec_ IntSyn.ctx_
    val coerceFront : front_ -> IntSyn.front_
    val revCoerceFront : IntSyn.front_ -> front_
    val deblockify :
      IntSyn.dec_ IntSyn.ctx_ -> (IntSyn.dec_ IntSyn.ctx_ * sub_)
    val TCSub : (tC_ * IntSyn.sub_) -> tC_
    val normalizeTC : tC_ -> tC_
    val convTC : (tC_ * tC_) -> bool
    val transformTC :
      (IntSyn.dec_ IntSyn.ctx_ * for_ * int Order.order_ list) -> tC_
  end


module Tomega(Tomega:sig module Whnf : WHNF module Conv : CONV end) : TOMEGA
  =
  struct
    exception Error of string 
    type nonrec label = int
    type nonrec lemma = int
    type worlds_ =
      | Worlds of IntSyn.cid list 
    type quantifier_ =
      | Implicit 
      | Explicit 
    type tC_ =
      | Abs of (IntSyn.dec_ * tC_) 
      | Conj of (tC_ * tC_) 
      | Base of ((IntSyn.exp_ * IntSyn.sub_) * (IntSyn.exp_ * IntSyn.sub_))
      Order.order_ 
    type for_ =
      | World of (worlds_ * for_) 
      | All of ((dec_ * quantifier_) * for_) 
      | Ex of ((IntSyn.dec_ * quantifier_) * for_) 
      | True 
      | And of (for_ * for_) 
      | FClo of (for_ * sub_) 
      | FVar of (dec_ IntSyn.ctx_ * for_ option ref) 
    and dec_ =
      | UDec of IntSyn.dec_ 
      | PDec of (string option * for_ * tC_ option * tC_ option) 
    and prg_ =
      | Box of (worlds_ * prg_) 
      | Lam of (dec_ * prg_) 
      | New of prg_ 
      | Choose of prg_ 
      | PairExp of (IntSyn.exp_ * prg_) 
      | PairBlock of (IntSyn.block_ * prg_) 
      | PairPrg of (prg_ * prg_) 
      | Unit 
      | Redex of (prg_ * spine_) 
      | Rec of (dec_ * prg_) 
      | Case of cases_ 
      | PClo of (prg_ * sub_) 
      | Let of (dec_ * prg_ * prg_) 
      | EVar of (dec_ IntSyn.ctx_ * prg_ option ref * for_ * tC_ option * tC_
      option * IntSyn.exp_) 
      | Const of lemma 
      | Var of int 
      | LetPairExp of (IntSyn.dec_ * dec_ * prg_ * prg_) 
      | LetUnit of (prg_ * prg_) 
    and spine_ =
      | Nil 
      | AppExp of (IntSyn.exp_ * spine_) 
      | AppBlock of (IntSyn.block_ * spine_) 
      | AppPrg of (prg_ * spine_) 
      | SClo of (spine_ * sub_) 
    and sub_ =
      | Shift of int 
      | Dot of (front_ * sub_) 
    and front_ =
      | Idx of int 
      | Prg of prg_ 
      | Exp of IntSyn.exp_ 
      | Block of IntSyn.block_ 
      | Undef 
    and cases_ =
      | Cases of (dec_ IntSyn.ctx_ * sub_ * prg_) list 
    type conDec_ =
      | ForDec of (string * for_) 
      | ValDec of (string * prg_ * for_) 
    exception NoMatch 
    module I = IntSyn
    module O = Order
    let maxLemma = Global.maxCid
    let lemmaArray =
      (Array.array ((maxLemma + 1), (ForDec ("", True))) : conDec_
                                                             Array.array)
    let nextLemma = ref 0
    let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    let rec lemmaAdd lemmaDec =
      let lemma = !nextLemma in
      if lemma > maxLemma
      then
        begin raise
                (Error
                   (((^) "Global signature size " Int.toString (maxLemma + 1))
                      ^ " exceeded")) end
        else begin
          (begin Array.update (lemmaArray, lemma, lemmaDec);
           (nextLemma := lemma) + 1;
           lemma end) end
let rec lemmaSize () = !nextLemma
let rec lemmaDef lemma =
  begin match lemmaLookup lemma with | ValDec (_, p_, _) -> p_ end
let rec lemmaFor lemma =
  begin match lemmaLookup lemma with
  | ForDec (_, f_) -> f_
  | ValDec (_, _, f_) -> f_ end
let rec lemmaName s = lemmaName' !nextLemma s
let rec lemmaName' arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | ((-1), s) -> raise (Error "Function name not found")
  | (n, s) ->
      (begin match lemmaLookup n with
       | ForDec (s', f_) -> if s = s' then begin n end
           else begin lemmaName' (n - 1) s end
  | ValDec (s', p_, f_) -> if s = s' then begin n end
      else begin lemmaName' (n - 1) s end end) end
let rec coerceFront =
  begin function
  | Idx k -> I.Idx k
  | Prg (p_) -> I.Undef
  | Exp (m_) -> I.Exp m_
  | Block (b_) -> I.Block b_
  | Undef -> I.Undef end
let rec embedFront =
  begin function
  | Idx k -> Idx k
  | Exp (u_) -> Exp u_
  | Block (b_) -> Block b_
  | I.Undef -> Undef end
let rec coerceSub =
  begin function
  | Shift n -> I.Shift n
  | Dot (Ft, t) -> I.Dot ((coerceFront Ft), (coerceSub t)) end
let rec embedSub =
  begin function
  | Shift n -> Shift n
  | Dot (Ft, s) -> Dot ((embedFront Ft), (embedSub s)) end
let rec revCoerceFront =
  begin function
  | Idx k -> Idx k
  | Exp (m_) -> Exp m_
  | Block b -> Block b
  | I.Undef -> Undef end
let rec revCoerceSub =
  begin function
  | Shift n -> Shift n
  | Dot (Ft, t) -> Dot ((revCoerceFront Ft), (revCoerceSub t)) end
let rec revCoerceCtx =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, (BDec (_, (l_, t)) as d_)) ->
      I.Decl ((revCoerceCtx Psi), (UDec d_)) end
let id = Shift 0
let rec dotEta =
  begin function
  | ((Idx _ as Ft), s) -> Dot (Ft, s)
  | ((Exp (u_) as Ft), s) ->
      let Ft' = begin try Idx (Whnf.etaContract u_) with | Eta -> Ft end in
    Dot (Ft', s)
  | ((Undef as Ft), s) -> Dot (Ft, s) end
let rec embedCtx =
  begin function
  | I.Null -> I.Null
  | Decl (g_, d_) -> I.Decl ((embedCtx g_), (UDec d_)) end
let rec orderSub =
  begin function
  | (Arg ((u_, s1), (v_, s2)), s) ->
      O.Arg ((u_, (I.comp (s1, s))), (v_, (I.comp (s2, s))))
  | (Lex (os_), s) ->
      O.Lex (map (begin function | o_ -> orderSub (o_, s) end) os_)
  | (Simul (os_), s) ->
      O.Simul (map (begin function | o_ -> orderSub (o_, s) end) os_) end
let rec TCSub =
  begin function
  | (Base (o_), s) -> Base (orderSub (o_, s))
  | (Conj (TC1, TC2), s) -> Conj ((TCSub (TC1, s)), (TCSub (TC2, s)))
  | (Abs (d_, TC), s) -> Abs ((I.decSub (d_, s)), (TCSub (TC, (I.dot1 s)))) end
let rec TCSubOpt =
  begin function | (None, s) -> None | (Some (TC), s) -> Some (TCSub (TC, s)) end
let rec normalizeTC' =
  begin function
  | Arg (us_, vs_) ->
      O.Arg (((Whnf.normalize us_), I.id), ((Whnf.normalize vs_), I.id))
  | Lex (os_) -> O.Lex (map normalizeTC' os_)
  | Simul (os_) -> O.Simul (map normalizeTC' os_) end
let rec normalizeTC =
  begin function
  | Base (o_) -> Base (normalizeTC' o_)
  | Conj (TC1, TC2) -> Conj ((normalizeTC TC1), (normalizeTC TC2))
  | Abs (d_, TC) -> Abs ((Whnf.normalizeDec (d_, I.id)), (normalizeTC TC)) end
let rec normalizeTCOpt =
  begin function | None -> None | Some (TC) -> Some (normalizeTC TC) end
let rec convTC' =
  begin function
  | (Arg (us1_, _), Arg (us2_, _)) -> Conv.conv (us1_, us2_)
  | (Lex (os1_), Lex (os2_)) -> convTCs (os1_, os2_)
  | (Simul (os1_), Simul (os2_)) -> convTCs (os1_, os2_) end
let rec convTCs =
  begin function
  | ([], []) -> true
  | ((o1_)::l1_, (o2_)::l2_) -> (convTC' (o1_, o2_)) && (convTCs (l1_, l2_)) end
let rec convTC =
  begin function
  | (Base (o_), Base (o'_)) -> convTC' (o_, o'_)
  | (Conj (TC1, TC2), Conj (TC1', TC2')) ->
      (convTC (TC1, TC1')) && (convTC (TC2, TC2'))
  | (Abs (d_, TC), Abs (d'_, TC')) ->
      (Conv.convDec ((d_, I.id), (d'_, I.id))) && (convTC (TC, TC'))
  | _ -> false end
let rec convTCOpt =
  begin function
  | (None, None) -> true
  | (Some (TC1), Some (TC2)) -> convTC (TC1, TC2)
  | _ -> false end
let rec transformTC' =
  begin function
  | (g_, Arg k) ->
      let k' = ((I.ctxLength g_) - k) + 1 in
      let Dec (_, v_) = I.ctxDec (g_, k') in
      O.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (v_, I.id))
  | (g_, Lex (os_)) ->
      O.Lex (map (begin function | o_ -> transformTC' (g_, o_) end) os_)
  | (g_, Simul (os_)) ->
      O.Simul (map (begin function | o_ -> transformTC' (g_, o_) end) os_) end
let rec transformTC =
  begin function
  | (g_, All ((UDec (d_), _), f_), os_) ->
      Abs (d_, (transformTC ((I.Decl (g_, d_)), f_, os_)))
  | (g_, And (f1_, f2_), (o_)::os_) ->
      Conj ((transformTC (g_, f1_, [o_])), (transformTC (g_, f2_, os_)))
  | (g_, Ex _, (o_)::[]) -> Base (transformTC' (g_, o_)) end
let rec varSub =
  begin function
  | (1, Dot (Ft, t)) -> Ft
  | (n, Dot (Ft, t)) -> varSub ((n - 1), t)
  | (n, Shift k) -> Idx (n + k) end
let rec frontSub =
  begin function
  | (Idx n, t) -> varSub (n, t)
  | (Exp (u_), t) -> Exp (I.EClo (u_, (coerceSub t)))
  | (Prg (p_), t) -> Prg (PClo (p_, t))
  | (Block (b_), t) -> Block (I.blockSub (b_, (coerceSub t))) end
let rec comp =
  begin function
  | (Shift 0, t) -> t
  | (t, Shift 0) -> t
  | (Shift n, Dot (Ft, t)) -> comp ((Shift (n - 1)), t)
  | (Shift n, Shift m) -> Shift (n + m)
  | (Dot (Ft, t), t') -> Dot ((frontSub (Ft, t')), (comp (t, t'))) end
let rec dot1 =
  begin function
  | Shift 0 as t -> t
  | t -> Dot ((Idx 1), (comp (t, (Shift 1)))) end
let id = Shift 0
let shift = Shift 1
let rec weakenSub =
  begin function
  | I.Null -> id
  | Decl (Psi, (UDec _ as d_)) -> dot1 (weakenSub Psi)
  | Decl (Psi, (PDec _ as d_)) -> comp ((weakenSub Psi), shift) end
let rec forSub =
  begin function
  | (All ((d_, q_), f_), t) ->
      All (((decSub (d_, t)), q_), (forSub (f_, (dot1 t))))
  | (Ex ((d_, q_), f_), t) ->
      Ex (((I.decSub (d_, (coerceSub t))), q_), (forSub (f_, (dot1 t))))
  | (And (f1_, f2_), t) -> And ((forSub (f1_, t)), (forSub (f2_, t)))
  | (FClo (f_, t1), t2) -> forSub (f_, (comp (t1, t2)))
  | (World (w_, f_), t) -> World (w_, (forSub (f_, t)))
  | (True, _) -> True end
let rec decSub =
  begin function
  | (PDec (x, f_, TC1, None), t) ->
      let s = coerceSub t in
      PDec (x, (forSub (f_, t)), (TCSubOpt (TC1, s)), None)
  | (UDec (d_), t) -> UDec (I.decSub (d_, (coerceSub t))) end
let rec invertSub s =
  let rec getFrontIndex =
    begin function
    | Idx k -> Some k
    | Prg (p_) -> getPrgIndex p_
    | Exp (u_) -> getExpIndex u_
    | Block (b_) -> getBlockIndex b_
    | Undef -> None end
    and getPrgIndex =
      begin function
      | Redex (Var k, Nil) -> Some k
      | Redex (p_, Nil) -> getPrgIndex p_
      | PClo (p_, t) ->
          (begin match getPrgIndex p_ with
           | None -> None
           | Some i -> getFrontIndex (varSub (i, t)) end)
      | _ -> None end(* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
  and getExpIndex =
    begin function
    | Root (BVar k, I.Nil) -> Some k
    | Redex (u_, I.Nil) -> getExpIndex u_
    | EClo (u_, t) ->
        (begin match getExpIndex u_ with
         | None -> None
         | Some i -> getFrontIndex (revCoerceFront (I.bvarSub (i, t))) end)
    | Lam (Dec (_, u1_), u2_) as u_ ->
        (begin try Some (Whnf.etaContract u_) with | Whnf.Eta -> None end)
  | _ -> None end
and getBlockIndex = begin function | Bidx k -> Some k | _ -> None end in
let rec lookup =
begin function
| (n, Shift _, p) -> None
| (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
| (n, Dot (Idx k, s'), p) -> if k = p then begin Some n end
    else begin lookup ((n + 1), s', p) end end in
let rec invertSub'' =
begin function
| (0, si) -> si
| (p, si) ->
    (begin match lookup (1, s, p) with
     | Some k -> invertSub'' ((p - 1), (Dot ((Idx k), si)))
     | None -> invertSub'' ((p - 1), (Dot (Undef, si))) end) end in
let rec invertSub' =
begin function
| (n, Shift p) -> invertSub'' (p, (Shift n))
| (n, Dot (_, s')) -> invertSub' ((n + 1), s') end in ((invertSub' (0, s))
(* returns NONE if not found *)(* getPrgIndex returns NONE if it is not an index *)
(* getExpIndex returns NONE if it is not an index *)
(* getBlockIndex returns NONE if it is not an index *)
(* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *))
let rec coerceCtx =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, UDec (d_)) -> I.Decl ((coerceCtx Psi), d_)
  | Decl (Psi, PDec (x, _, _, _)) -> I.Decl ((coerceCtx Psi), (I.NDec x)) end
let rec strengthenCtx (Psi) =
  let w = weakenSub Psi in let s = invertSub w in ((coerceCtx Psi), w, s)
let rec convFor =
  begin function
  | ((True, _), (True, _)) -> true
  | ((All ((d1_, _), f1_), t1), (All ((d2_, _), f2_), t2)) ->
      (convDec ((d1_, t1), (d2_, t2))) &&
        (convFor ((f1_, (dot1 t1)), (f2_, (dot1 t2))))
  | ((Ex ((d1_, _), f1_), t1), (Ex ((d2_, _), f2_), t2)) ->
      (Conv.convDec ((d1_, (coerceSub t1)), (d2_, (coerceSub t2)))) &&
        (convFor ((f1_, (dot1 t1)), (f2_, (dot1 t2))))
  | ((And (f1_, F1'), t1), (And (f2_, F2'), t2)) ->
      (convFor ((f1_, t1), (f2_, t2))) && (convFor ((F1', t1), (F2', t2)))
  | _ -> false end
let rec convDec =
  begin function
  | ((UDec (d1_), t1), (UDec (d2_), t2)) ->
      Conv.convDec ((d1_, (coerceSub t1)), (d2_, (coerceSub t2)))
  | ((PDec (_, f1_, TC1, TC1'), t1), (PDec (_, f2_, TC2, TC2'), t2)) ->
      (begin convFor ((f1_, t1), (f2_, t2));
       convTCOpt (TC1, TC1');
       convTCOpt (TC2, TC2') end) end
let rec newEVar (Psi, f_) =
  EVar
    (Psi, (ref None), f_, None, None,
      (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
let rec newEVarTC (Psi, f_, TC, TC') =
  EVar
    (Psi, (ref None), f_, TC, TC',
      (I.newEVar ((coerceCtx Psi), (I.Uni I.Type))))
let rec exists =
  begin function
  | (x, []) -> false
  | (x, y::w2_) -> (x = y) || (exists (x, w2_)) end
let rec subset =
  begin function
  | ([], _) -> true
  | (x::w1_, w2_) -> (exists (x, w2_)) && (subset (w1_, w2_)) end
let rec eqWorlds (Worlds (w1_), Worlds (w2_)) =
  (subset (w1_, w2_)) && (subset (w2_, w1_))
let rec ctxDec (g_, k) =
  let rec ctxDec' =
    begin function
    | (Decl (g'_, UDec (Dec (x, v'_))), 1) ->
        UDec (I.Dec (x, (I.EClo (v'_, (I.Shift k)))))
    | (Decl (g'_, UDec (BDec (l, (c, s)))), 1) ->
        UDec (I.BDec (l, (c, (I.comp (s, (I.Shift k))))))
    | (Decl (g'_, PDec (x, f_, TC1, TC2)), 1) ->
        PDec
          (x, (forSub (f_, (Shift k))), (TCSubOpt (TC1, (I.Shift k))),
            (TCSubOpt (TC2, (I.Shift k))))
    | (Decl (g'_, _), k') -> ctxDec' (g'_, (k' - 1)) end in
((ctxDec' (g_, k))
  (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
  (* ctxDec' (Null, k')  should not occur by invariant *))
let rec mkInst =
  begin function
  | 0 -> []
  | n -> (::) (I.Root ((I.BVar n), I.Nil)) mkInst (n - 1) end
let rec deblockify =
  begin function
  | I.Null -> (I.Null, id)
  | Decl (g_, BDec (x, (c, s))) ->
      let (g'_, t') = deblockify g_ in
      let (_, l_) = I.constBlock c in
      let n = List.length l_ in
      let G'' = append (g'_, (l_, (I.comp (s, (coerceSub t'))))) in
      let t'' = comp (t', (Shift n)) in
      let i_ = I.Inst (mkInst n) in
      let t''' = Dot ((Block i_), t'') in (((G'', t'''))
        (* G' |- t' : G *)(* G'' = G', V1 ... Vn *)
        (* G'' |- t'' : G *)(* I = (n, n-1 ... 1)  *)
        (* G'' |- t''' : G, x:(c,s) *)) end
let rec append =
  begin function
  | (g'_, ([], s)) -> g'_
  | (g'_, ((d_)::l_, s)) ->
      append ((I.Decl (g'_, (I.decSub (d_, s)))), (l_, (I.dot1 s))) end
let rec whnfFor =
  begin function
  | (All (d_, _), t) as Ft -> Ft
  | (Ex (d_, f_), t) as Ft -> Ft
  | (And (f1_, f2_), t) as Ft -> Ft
  | (FClo (f_, t1), t2) -> whnfFor (f_, (comp (t1, t2)))
  | (World (w_, f_), t) as Ft -> Ft
  | (True, _) as Ft -> Ft end
let rec normalizePrg =
  begin function
  | (Var n, t) ->
      (begin match varSub (n, t) with
       | Prg (p_) -> p_
       | Idx _ -> raise Domain
       | Exp _ -> raise Domain
       | Block _ -> raise Domain
       | Undef -> raise Domain end)
  | (PairExp (u_, p'_), t) ->
      PairExp ((Whnf.normalize (u_, (coerceSub t))), (normalizePrg (p'_, t)))
  | (PairBlock (b_, p'_), t) ->
      PairBlock ((I.blockSub (b_, (coerceSub t))), (normalizePrg (p'_, t)))
  | (PairPrg (p1_, p2_), t) ->
      PairPrg ((normalizePrg (p1_, t)), (normalizePrg (p2_, t)))
  | (Unit, _) -> Unit
  | (EVar (_, { contents = Some (p_) }, _, _, _, _), t) -> PClo (p_, t)
  | ((EVar _ as p_), t) -> PClo (p_, t)
  | (Lam (d_, p_), t) ->
      Lam ((normalizeDec (d_, t)), (normalizePrg (p_, (dot1 t))))
  | (Rec (d_, p_), t) ->
      Rec ((normalizeDec (d_, t)), (normalizePrg (p_, (dot1 t))))
  | (PClo (p_, t), t') -> normalizePrg (p_, (comp (t, t'))) end
let rec normalizeSpine =
  begin function
  | (Nil, t) -> Nil
  | (AppExp (u_, s_), t) ->
      AppExp ((Whnf.normalize (u_, (coerceSub t))), (normalizeSpine (s_, t)))
  | (AppPrg (p_, s_), t) ->
      AppPrg ((normalizePrg (p_, t)), (normalizeSpine (s_, t)))
  | (AppBlock (b_, s_), t) ->
      AppBlock ((I.blockSub (b_, (coerceSub t))), (normalizeSpine (s_, t)))
  | (SClo (s_, t1), t2) -> normalizeSpine (s_, (comp (t1, t2))) end
let rec normalizeDec =
  begin function
  | (PDec (name, f_, TC1, None), t) ->
      PDec
        (name, (forSub (f_, t)),
          (normalizeTCOpt (TCSubOpt (TC1, (coerceSub t)))), None)
  | (UDec (d_), t) -> UDec (Whnf.normalizeDec (d_, (coerceSub t))) end
let rec normalizeSub =
  begin function
  | Shift n as s -> s
  | Dot (Prg (p_), s) ->
      Dot ((Prg (normalizePrg (p_, id))), (normalizeSub s))
  | Dot (Exp (e_), s) ->
      Dot ((Exp (Whnf.normalize (e_, I.id))), (normalizeSub s))
  | Dot (Block k, s) -> Dot ((Block k), (normalizeSub s))
  | Dot (Idx k, s) -> Dot ((Idx k), (normalizeSub s)) end
let rec derefPrg =
  begin function
  | Var n -> Var n
  | PairExp (u_, p'_) -> PairExp (u_, (derefPrg p'_))
  | PairBlock (b_, p'_) -> PairBlock (b_, (derefPrg p'_))
  | PairPrg (p1_, p2_) -> PairPrg ((derefPrg p1_), (derefPrg p2_))
  | Unit -> Unit
  | EVar (_, { contents = Some (p_) }, _, _, _, _) -> p_
  | EVar _ as p_ -> p_
  | Lam (d_, p_) -> Lam ((derefDec d_), (derefPrg p_))
  | Rec (d_, p_) -> Rec ((derefDec d_), (derefPrg p_))
  | Redex (p_, s_) -> Redex ((derefPrg p_), (derefSpine s_))
  | Case (Cases (cs_)) ->
      Case
        (Cases
           (flattenCases
              (map
                 (begin function | (Psi, s, p_) -> (Psi, s, (derefPrg p_)) end)
              cs_)))
  | Let (d_, p1_, p2_) -> Let ((derefDec d_), (derefPrg p1_), (derefPrg p2_))
  | LetPairExp (d1_, d2_, p1_, p2_) ->
      LetPairExp (d1_, (derefDec d2_), (derefPrg p1_), (derefPrg p2_))
  | LetUnit (p1_, p2_) -> LetUnit ((derefPrg p1_), (derefPrg p2_)) end
let rec flattenCases =
  begin function
  | (Psi, s, Case (Cases (l_)))::cs_ ->
      (@) (map
             (begin function | (Psi', s', p'_) -> (Psi', (comp (s, s')), p'_) end)
        (flattenCases l_))
      flattenCases cs_
  | (Psi, s, p_)::cs_ -> (::) (Psi, s, p_) flattenCases cs_ | [] -> [] end
let rec derefSpine =
  begin function
  | Nil -> Nil
  | AppExp (u_, s_) -> AppExp (u_, (derefSpine s_))
  | AppPrg (p_, s_) -> AppPrg ((derefPrg p_), (derefSpine s_))
  | AppBlock (b_, s_) -> AppBlock (b_, (derefSpine s_)) end
let rec derefDec =
  begin function
  | PDec (name, f_, TC1, TC2) -> PDec (name, f_, TC1, TC2)
  | UDec (d_) -> UDec d_ end
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
let transformTC = transformTC end



module Whnf = (Whnf)(struct  end)
module Conv = (Conv)(struct module Whnf = Whnf end)
module Tomega : TOMEGA =
  (Tomega)(struct module Whnf = Whnf
                       module Conv = Conv end) 