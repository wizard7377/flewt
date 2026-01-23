module type WHNF  =
  sig
    val isPatSub : IntSyn.sub_ -> bool
    val makePatSub : IntSyn.sub_ -> IntSyn.sub_ option
    val dotEta : (IntSyn.front_ * IntSyn.sub_) -> IntSyn.sub_
    exception Eta 
    val etaContract : IntSyn.exp_ -> int
    val whnf : IntSyn.eclo -> IntSyn.eclo
    val expandDef : IntSyn.eclo -> IntSyn.eclo
    val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
    val etaExpandRoot : IntSyn.exp_ -> IntSyn.exp_
    val whnfEta : (IntSyn.eclo * IntSyn.eclo) -> (IntSyn.eclo * IntSyn.eclo)
    val lowerEVar : IntSyn.exp_ -> IntSyn.exp_
    val newLoweredEVar : (IntSyn.dctx * IntSyn.eclo) -> IntSyn.exp_
    val newSpineVar : (IntSyn.dctx * IntSyn.eclo) -> IntSyn.spine_
    val spineToSub : (IntSyn.spine_ * IntSyn.sub_) -> IntSyn.sub_
    val normalize : IntSyn.eclo -> IntSyn.exp_
    val normalizeDec : (IntSyn.dec_ * IntSyn.sub_) -> IntSyn.dec_
    val normalizeCtx : IntSyn.dctx -> IntSyn.dctx
    val invert : IntSyn.sub_ -> IntSyn.sub_
    val strengthen : (IntSyn.sub_ * IntSyn.dctx) -> IntSyn.dctx
    val isId : IntSyn.sub_ -> bool
    val cloInv : (IntSyn.exp_ * IntSyn.sub_) -> IntSyn.exp_
    val compInv : (IntSyn.sub_ * IntSyn.sub_) -> IntSyn.sub_
  end


module Whnf() : WHNF =
  struct
    open IntSyn
    exception Eta 
    let rec etaContract =
      begin function
      | (Root (BVar k, s_), s, n) ->
          (begin match bvarSub (k, s) with
           | Idx k' ->
               if k' > n
               then begin (begin etaContract' (s_, s, n); k' - n end) end
           else begin raise Eta end
      | _ -> raise Eta end)
    | (Lam (d_, u_), s, n) -> etaContract (u_, (dot1 s), (n + 1))
    | (EClo (u_, s'), s, n) -> etaContract (u_, (comp (s', s)), n)
    | (EVar ({ contents = Some (u_) }, _, _, _), s, n) ->
        etaContract (u_, s, n)
    | (AVar { contents = Some (u_) }, s, n) -> etaContract (u_, s, n)
    | _ -> raise Eta end
let rec etaContract' =
  begin function
  | (Nil, s, 0) -> ()
  | (App (u_, s_), s, n) ->
      if (etaContract (u_, s, 0)) = n
      then begin etaContract' (s_, s, (n - 1)) end else begin raise Eta end
  | (SClo (s_, s'), s, n) -> etaContract' (s_, (comp (s', s)), n)
  | _ -> raise Eta end
let rec dotEta =
  begin function
  | ((Idx _ as Ft), s) -> Dot (Ft, s)
  | ((Exp (u_) as Ft), s) ->
      let Ft' = begin try Idx (etaContract (u_, id, 0)) with | Eta -> Ft end in
    Dot (Ft', s)
  | ((Undef as Ft), s) -> Dot (Ft, s) end
let rec appendSpine =
  begin function
  | ((Nil, s1), ss2_) -> SClo ss2_
  | ((App (u1_, s1_), s1), ss2_) ->
      App ((EClo (u1_, s1)), (appendSpine ((s1_, s1), ss2_)))
  | ((SClo (s1_, s1'), s1), ss2_) ->
      appendSpine ((s1_, (comp (s1', s1))), ss2_) end
let rec whnfRedex =
  begin function
  | (us_, (SClo (s_, s2'), s2)) -> whnfRedex (us_, (s_, (comp (s2', s2))))
  | (((Root (r_), s1) as us_), (Nil, s2)) -> us_
  | ((Root (h1_, s1_), s1), (s2_, s2)) ->
      ((Root (h1_, (appendSpine ((s1_, s1), (s2_, s2))))), id)
  | ((Lam (_, u1_), s1), (App (u2_, s_), s2)) ->
      whnfRedex
        ((whnf (u1_, (dotEta ((frontSub ((Exp u2_), s2)), s1)))), (s_, s2))
  | (((Lam _, s1) as us_), _) -> us_
  | (((EVar _, s1) as us_), (Nil, s2)) -> us_
  | ((((EVar _ as x_), s1) as us_), ss2_) ->
      (begin lowerEVar x_; whnfRedex ((whnf us_), ss2_) end)
  | (((AVar { contents = Some (u_) }, s1) as us_), ss2_) ->
      whnfRedex ((u_, s1), ss2_)
  | (((AVar { contents = None }, s1) as us_), ss2_) -> us_
  | (((FgnExp _, _) as us_), _) -> us_ | (((Uni _, s1) as us_), _) -> us_
  | (((Pi _, s1) as us_), _) -> us_ end(* S2[s2] = Nil *)
(* Uni and Pi can arise after instantiation of EVar X : K *)(* lowerEVar X results in redex, optimize by unfolding call to whnfRedex *)
(* Ss2 must be App, since prior cases do not apply *)
(* S2[s2] = Nil *)(* S2 = App _, only possible if term is not eta-expanded *)
let rec lowerEVar' =
  begin function
  | (g_, (Pi ((d'_, _), v'_), s')) ->
      let D'' = decSub (d'_, s') in
      let (x'_, u_) =
        lowerEVar' ((Decl (g_, D'')), (whnfExpandDef (v'_, (dot1 s')))) in
      (x'_, (Lam (D'', u_)))
  | (g_, vs'_) -> let x'_ = newEVar (g_, (EClo vs'_)) in (x'_, x'_) end
let rec lowerEVar1 =
  begin function
  | (EVar (r, g_, _, _), ((Pi _, _) as vs_)) ->
      let (x'_, u_) = lowerEVar' (g_, vs_) in let _ = (:=) r Some u_ in x'_
  | (x_, _) -> x_ end
let rec lowerEVar =
  begin function
  | EVar (r, g_, v_, { contents = [] }) as x_ ->
      lowerEVar1 (x_, (whnfExpandDef (v_, id)))
  | EVar _ ->
      raise
        (Error
           "Typing ambiguous -- constraint of functional type cannot be simplified") end
(* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
(* It is not clear if this case can happen *)
let rec whnfRoot =
  begin function
  | ((BVar k, s_), s) ->
      (begin match bvarSub (k, s) with
       | Idx k -> ((Root ((BVar k), (SClo (s_, s)))), id)
       | Exp (u_) -> whnfRedex ((whnf (u_, id)), (s_, s)) end)
  | ((Proj ((Bidx _ as b_), i), s_), s) ->
      (begin match blockSub (b_, s) with
       | Bidx k as b'_ -> ((Root ((Proj (b'_, i)), (SClo (s_, s)))), id)
       | LVar _ as b'_ -> whnfRoot (((Proj (b'_, i)), (SClo (s_, s))), id)
       | Inst (l_) ->
           whnfRedex ((whnf ((List.nth (l_, (i - 1))), id)), (s_, s)) end)
  | ((Proj (LVar ({ contents = Some (b_) }, sk, (l, t)), i), s_), s) ->
      whnfRoot
        (((Proj ((blockSub (b_, (comp (sk, s)))), i)), (SClo (s_, s))), id)
  | ((Proj ((LVar (r, sk, (l, t)) as l_), i), s_), s) ->
      ((Root ((Proj ((LVar (r, (comp (sk, s)), (l, t))), i)), (SClo (s_, s)))),
        id)
  | ((FVar (name, v_, s'), s_), s) ->
      ((Root ((FVar (name, v_, (comp (s', s)))), (SClo (s_, s)))), id)
  | ((NSDef d, s_), s) ->
      whnfRedex ((whnf ((IntSyn.constDef d), id)), (s_, s))
  | ((h_, s_), s) -> ((Root (h_, (SClo (s_, s)))), id) end(* Undef and Exp should be impossible by definition of substitution -cs *)
(* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *)
(* going back to first version, because globality invariant *)(* was: (Root (Proj (L, i), SClo (S, s)), id) *)
(* Thu Dec  6 20:34:30 2001 -fp !!! *)(* do not compose with t due to globality invariant *)
(* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *)
(* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *)
(* r = ref NONE *)(* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *)
(* yes Thu Dec 13 21:48:10 2001 -fp !!! *)(* Sat Dec  8 13:43:17 2001 -fp !!! *)
(* could blockSub (B, s) return instantiated LVar ? *)
(* Undef should be impossible *)
let rec whnf =
  begin function
  | ((Uni _ as u_), s) -> (u_, s)
  | ((Pi _ as u_), s) -> (u_, s)
  | (Root (r_), s) -> whnfRoot (r_, s)
  | (Redex (u_, s_), s) -> whnfRedex ((whnf (u_, s)), (s_, s))
  | (Lam _, s) as us_ -> us_
  | (AVar { contents = Some (u_) }, s) -> whnf (u_, s)
  | (AVar _, s) as us_ -> us_
  | (EVar ({ contents = Some (u_) }, _, _, _), s) -> whnf (u_, s)
  | (EVar (r, _, Root _, _), s) as us_ -> us_
  | (EVar (r, _, Uni _, _), s) as us_ -> us_
  | ((EVar (r, _, v_, _) as x_), s) as us_ ->
      (((begin match whnf (v_, id) with
         | (Pi _, _) -> (begin lowerEVar x_; whnf us_ end)
      | _ -> us_ end))
  (* possible opt: call lowerEVar1 *))
  | (EClo (u_, s'), s) -> whnf (u_, (comp (s', s)))
  | (FgnExp _, Shift 0) as us_ -> us_
  | (FgnExp csfe, s) as us_ ->
      ((FgnExpStd.Map.apply csfe (begin function | u_ -> EClo (u_, s) end)),
      id) end(* next two avoid calls to whnf (V, id), where V is type of X *)
(* | whnf (Us as (EVar _, s)) = Us *)(* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *)
(*      | whnf (Us as (Root _, Shift (0))) = Us*)(* Sat Feb 14 20:53:08 1998 -fp *)
(* applied in Twelf 1.1 *)(* simple optimization (C@S)[id] = C@S[id] *)
let rec expandDef (Root (Def d, s_), s) =
  whnfRedex ((whnf ((constDef d), id)), (s_, s))(* why the call to whnf?  isn't constDef (d) in nf? -kw *)
let rec whnfExpandDefW =
  begin function
  | (Root (Def _, _), _) as us_ -> whnfExpandDefW (expandDef us_)
  | us_ -> us_ end
let rec whnfExpandDef (us_) = whnfExpandDefW (whnf us_)
let rec newLoweredEVarW =
  begin function
  | (g_, (Pi ((d_, _), v_), s)) ->
      let d'_ = decSub (d_, s) in
      Lam (d'_, (newLoweredEVar ((Decl (g_, d'_)), (v_, (dot1 s)))))
  | (g_, vs_) -> newEVar (g_, (EClo vs_)) end
let rec newLoweredEVar (g_, vs_) = newLoweredEVarW (g_, (whnfExpandDef vs_))
let rec newSpineVarW =
  begin function
  | (g_, (Pi ((Dec (_, Va), _), Vr), s)) ->
      let x_ = newLoweredEVar (g_, (Va, s)) in
      App (x_, (newSpineVar (g_, (Vr, (dotEta ((Exp x_), s))))))
  | (g_, _) -> Nil end
let rec newSpineVar (g_, vs_) = newSpineVarW (g_, (whnfExpandDef vs_))
let rec spineToSub =
  begin function
  | (Nil, s) -> s
  | (App (u_, s_), s) -> spineToSub (s_, (dotEta ((Exp u_), s))) end
let rec inferSpine =
  begin function
  | ((Nil, _), vs_) -> vs_
  | ((SClo (s_, s'), s), vs_) -> inferSpine ((s_, (comp (s', s))), vs_)
  | ((App (u_, s_), s1), (Pi (_, v2_), s2)) ->
      inferSpine
        ((s_, s1), (whnfExpandDef (v2_, (Dot ((Exp (EClo (u_, s1))), s2))))) end
let rec inferCon =
  begin function
  | Const cid -> constType cid
  | Skonst cid -> constType cid
  | Def cid -> constType cid end
let rec etaExpand' =
  begin function
  | (u_, (Root _, s)) -> u_
  | (u_, (Pi ((d_, _), v_), s)) ->
      Lam
        ((decSub (d_, s)),
          (etaExpand'
             ((Redex
                 ((EClo (u_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
               (whnfExpandDef (v_, (dot1 s)))))) end
let rec etaExpandRoot (Root (h_, s_) as u_) =
  etaExpand' (u_, (inferSpine ((s_, id), ((inferCon h_), id))))
let rec whnfEta (us_, vs_) = whnfEtaW ((whnf us_), (whnf vs_))
let rec whnfEtaW =
  begin function
  | (_, (Root _, _)) as UsVs -> UsVs
  | ((Lam _, _), (Pi _, _)) as UsVs -> UsVs
  | ((u_, s1), ((Pi ((d_, p_), v_), s2) as vs2_)) ->
      (((Lam
           ((decSub (d_, s2)),
             (Redex
                ((EClo (u_, (comp (s1, shift)))),
                  (App ((Root ((BVar 1), Nil)), Nil)))))), id), vs2_) end
let rec normalizeExp (us_) = normalizeExpW (whnf us_)
let rec normalizeExpW =
  begin function
  | ((Uni (l_) as u_), s) -> u_
  | (Pi (DP, u_), s) ->
      Pi ((normalizeDecP (DP, s)), (normalizeExp (u_, (dot1 s))))
  | ((Root (h_, s_) as u_), s) -> Root (h_, (normalizeSpine (s_, s)))
  | (Lam (d_, u_), s) ->
      Lam ((normalizeDec (d_, s)), (normalizeExp (u_, (dot1 s))))
  | (EVar _, s) as us_ -> EClo us_
  | (FgnExp csfe, s) ->
      FgnExpStd.Map.apply csfe
        (begin function | u_ -> normalizeExp (u_, s) end)
  | (AVar { contents = Some (u_) }, s) as us_ -> normalizeExpW (u_, s)
  | (AVar _, s) as us_ ->
      (begin print "Normalize  AVAR\n"; raise (Error "") end) end(* s = id *)
let rec normalizeSpine =
  begin function
  | (Nil, s) -> Nil
  | (App (u_, s_), s) ->
      App ((normalizeExp (u_, s)), (normalizeSpine (s_, s)))
  | (SClo (s_, s'), s) -> normalizeSpine (s_, (comp (s', s))) end
let rec normalizeDec =
  begin function
  | (Dec (xOpt, v_), s) -> Dec (xOpt, (normalizeExp (v_, s)))
  | (BDec (xOpt, (c, t)), s) ->
      BDec (xOpt, (c, (normalizeSub (comp (t, s))))) end
let rec normalizeDecP ((d_, p_), s) = ((normalizeDec (d_, s)), p_)
let rec normalizeSub =
  begin function
  | Shift _ as s -> s
  | Dot ((Idx _ as Ft), s) -> Dot (Ft, (normalizeSub s))
  | Dot (Exp (u_), s) ->
      dotEta ((Exp (normalizeExp (u_, id))), (normalizeSub s)) end(* Dot (Exp (normalizeExp (U, id)), normalizeSub s) *)
(* Sat Dec  7 16:58:09 2002 -fp *)(* changed to obtain pattern substitution if possible *)
let rec normalizeCtx =
  begin function
  | Null -> Null
  | Decl (g_, d_) -> Decl ((normalizeCtx g_), (normalizeDec (d_, id))) end
let rec invert s =
  let rec lookup =
    begin function
    | (n, Shift _, p) -> None
    | (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
    | (n, Dot (Idx k, s'), p) -> if k = p then begin Some n end
        else begin lookup ((n + 1), s', p) end end in
let rec invert'' =
begin function
| (0, si) -> si
| (p, si) ->
    (begin match lookup (1, s, p) with
     | Some k -> invert'' ((p - 1), (Dot ((Idx k), si)))
     | None -> invert'' ((p - 1), (Dot (Undef, si))) end) end in
let rec invert' =
begin function
| (n, Shift p) -> invert'' (p, (Shift n))
| (n, Dot (_, s')) -> invert' ((n + 1), s') end in
invert' (0, s)
let rec strengthen =
  begin function
  | (((Shift n, Null))(* = 0 *)) -> Null
  | (Dot (((Idx k, t))(* k = 1 *)), Decl (g_, d_)) ->
      let t' = comp (t, invShift) in
      ((Decl ((strengthen (t', g_)), (decSub (d_, t'))))
        (* G |- D dec *)(* G' |- t' : G *)
        (* G' |- D[t'] dec *))
  | (Dot (Undef, t), Decl (g_, d_)) -> strengthen (t, g_)
  | (Shift n, g_) -> strengthen ((Dot ((Idx (n + 1)), (Shift (n + 1)))), g_) end
let rec isId' =
  begin function
  | (Shift k, k') -> k = k'
  | (Dot (Idx n, s'), k') -> (n = k') && (isId' (s', (k' + 1)))
  | _ -> false end
let rec isId s = isId' (s, 0)
let rec cloInv (u_, w) = EClo (u_, (invert w))
let rec compInv (s, w) = comp (s, (invert w))
let rec isPatSub =
  begin function
  | Shift k -> true
  | Dot (Idx n, s) ->
      let rec checkBVar =
        begin function
        | Shift k -> n <= k
        | Dot (Idx n', s) -> (n <> n') && (checkBVar s)
        | Dot (Undef, s) -> checkBVar s
        | _ -> false end in
    (checkBVar s) && (isPatSub s)
  | Dot (Undef, s) -> isPatSub s | _ -> false end
let rec mkPatSub =
  begin function
  | Shift k as s -> s
  | Dot (Idx n, s) ->
      let s' = mkPatSub s in
      let rec checkBVar =
        begin function
        | Shift k -> n <= k
        | Dot (Idx n', s') -> (n <> n') && (checkBVar s')
        | Dot (Undef, s') -> checkBVar s' end in
      let _ = checkBVar s' in Dot ((Idx n), s')
  | Dot (Undef, s) -> Dot (Undef, (mkPatSub s))
  | Dot (Exp (u_), s) ->
      let (u'_, t') = whnf (u_, id) in
      let k = etaContract (u'_, t', 0) in ((Dot ((Idx k), (mkPatSub s)))
        (* may raise Eta *))
  | _ -> raise Eta end
let rec makePatSub s = begin try Some (mkPatSub s) with | Eta -> None end
let isPatSub = isPatSub
let makePatSub = makePatSub
let dotEta = dotEta
exception Eta = Eta
let etaContract = begin function | u_ -> etaContract (u_, id, 0) end
let whnf = whnf
let expandDef = expandDef
let whnfExpandDef = whnfExpandDef
let etaExpandRoot = etaExpandRoot
let whnfEta = whnfEta
let lowerEVar = lowerEVar
let newLoweredEVar = newLoweredEVar
let newSpineVar = newSpineVar
let spineToSub = spineToSub
let normalize = normalizeExp
let normalizeDec = normalizeDec
let normalizeCtx = normalizeCtx
let invert = invert
let strengthen = strengthen
let isId = isId
let cloInv = cloInv
let compInv = compInv end
