module type ABSTRACT  =
  sig
    exception Error of string 
    val piDepend :
      ((IntSyn.dec_ * IntSyn.depend_) * IntSyn.exp_) -> IntSyn.exp_
    val closedDec :
      (IntSyn.dec_ IntSyn.ctx_ * (IntSyn.dec_ * IntSyn.sub_)) -> bool
    val closedSub : (IntSyn.dec_ IntSyn.ctx_ * IntSyn.sub_) -> bool
    val closedExp :
      (IntSyn.dec_ IntSyn.ctx_ * (IntSyn.exp_ * IntSyn.sub_)) -> bool
    val closedCtx : IntSyn.dec_ IntSyn.ctx_ -> bool
    val closedCTX : Tomega.dec_ IntSyn.ctx_ -> bool
    val abstractDecImp : IntSyn.exp_ -> (int * IntSyn.exp_)
    val abstractDef :
      (IntSyn.exp_ * IntSyn.exp_) -> (int * (IntSyn.exp_ * IntSyn.exp_))
    val abstractCtxs :
      IntSyn.dec_ IntSyn.ctx_ list ->
        (IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_ list)
    val abstractTomegaSub :
      Tomega.sub_ -> (Tomega.dec_ IntSyn.ctx_ * Tomega.sub_)
    val abstractTomegaPrg :
      Tomega.prg_ -> (Tomega.dec_ IntSyn.ctx_ * Tomega.prg_)
    val abstractSpine :
      (IntSyn.spine_ * IntSyn.sub_) -> (IntSyn.dctx * IntSyn.spine_)
    val collectEVars :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.exp_ list) -> IntSyn.exp_ list
    val collectEVarsSpine :
      (IntSyn.dctx * (IntSyn.spine_ * IntSyn.sub_) * IntSyn.exp_ list) ->
        IntSyn.exp_ list
    val raiseTerm : (IntSyn.dctx * IntSyn.exp_) -> IntSyn.exp_
    val raiseType : (IntSyn.dctx * IntSyn.exp_) -> IntSyn.exp_
  end


module Abstract(Abstract:sig
                           module Whnf : WHNF
                           module Unify : UNIFY
                           module Constraints : CONSTRAINTS
                         end) : ABSTRACT =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module C = Constraints
    module O = Order
    type eFLVar_ =
      | EV of I.exp_ 
      | FV of (string * I.exp_) 
      | LV of I.block_ 
      | PV of T.prg_ 
    let rec collectConstraints =
      begin function
      | I.Null -> []
      | Decl (g_, FV _) -> collectConstraints g_
      | Decl (g_, EV (EVar (_, _, _, { contents = [] }))) ->
          collectConstraints g_
      | Decl (g_, EV (EVar (_, _, _, { contents = cnstrL }))) ->
          (@) (C.simplify cnstrL) collectConstraints g_
      | Decl (g_, LV _) -> collectConstraints g_ end
    let rec checkConstraints (k_) =
      let constraints = collectConstraints k_ in
      let _ =
        begin match constraints with
        | [] -> ()
        | _ -> raise (C.Error constraints) end in
      ()
  let rec eqEVar arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
    | (_, _) -> false end
let rec eqFVar arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (FVar (n1, _, _), FV (n2, _)) -> n1 = n2
  | (_, _) -> false end
let rec eqLVar arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (LVar (r1, _, _), LV (LVar (r2, _, _))) -> r1 = r2
  | (_, _) -> false end
let rec exists (p_) (k_) =
  let rec exists' =
    begin function
    | I.Null -> false
    | Decl (k'_, y_) -> (p_ y_) || (exists' k'_) end in
exists' k_
let rec or_ =
  begin function
  | (I.Maybe, _) -> I.Maybe
  | (_, I.Maybe) -> I.Maybe
  | (I.Meta, _) -> I.Meta
  | (_, I.Meta) -> I.Meta
  | (I.No, I.No) -> I.No end
let rec occursInExp =
  begin function
  | (k, Uni _) -> I.No
  | (k, Pi (DP, v_)) ->
      or_ ((occursInDecP (k, DP)), (occursInExp ((k + 1), v_)))
  | (k, Root (h_, s_)) -> occursInHead (k, h_, (occursInSpine (k, s_)))
  | (k, Lam (d_, v_)) ->
      or_ ((occursInDec (k, d_)), (occursInExp ((k + 1), v_)))
  | (k, FgnExp csfe) ->
      I.FgnExpStd.fold csfe
        (begin function
         | (u_, DP) ->
             or_ (DP, (occursInExp (k, (Whnf.normalize (u_, I.id))))) end)
      I.No end
let rec occursInHead =
  begin function
  | (k, BVar k', DP) -> if k = k' then begin I.Maybe end else begin DP end
  | (k, Const _, DP) -> DP | (k, Def _, DP) -> DP | (k, Proj _, DP) -> DP
  | (k, FgnConst _, DP) -> DP | (k, Skonst _, I.No) -> I.No
  | (k, Skonst _, I.Meta) -> I.Meta | (k, Skonst _, I.Maybe) -> I.Meta end
let rec occursInSpine =
  begin function
  | (_, I.Nil) -> I.No
  | (k, App (u_, s_)) -> or_ ((occursInExp (k, u_)), (occursInSpine (k, s_))) end
let rec occursInDec (k, Dec (_, v_)) = occursInExp (k, v_)
let rec occursInDecP (k, (d_, _)) = occursInDec (k, d_)
let rec piDepend =
  begin function
  | ((d_, I.No), v_) as DPV -> I.Pi DPV
  | ((d_, I.Meta), v_) as DPV -> I.Pi DPV
  | ((d_, I.Maybe), v_) -> I.Pi ((d_, (occursInExp (1, v_))), v_) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec raiseTerm =
  begin function
  | (I.Null, u_) -> u_
  | (Decl (g_, d_), u_) -> raiseTerm (g_, (I.Lam (d_, u_))) end
let rec collectExpW =
  begin function
  | (g_, (Uni (l_), s), k_) -> k_
  | (g_, (Pi ((d_, _), v_), s), k_) ->
      collectExp
        ((I.Decl (g_, (I.decSub (d_, s)))), (v_, (I.dot1 s)),
          (collectDec (g_, (d_, s), k_)))
  | (g_, (Root ((FVar (name, v_, s') as f_), s_), s), k_) ->
      ((if exists (eqFVar f_) k_
        then begin collectSpine (g_, (s_, s), k_) end
      else begin
        collectSpine
          (g_, (s_, s),
            (I.Decl ((collectExp (I.Null, (v_, I.id), k_)), (FV (name, v_))))) end)
  (* s' = ^|G| *))
  | (g_,
     (Root (Proj ((LVar ({ contents = None }, sk, (l, t)) as l_), i), s_), s),
     k_) ->
      collectSpine
        (g_, (s_, s), (collectBlock (g_, (I.blockSub (l_, s)), k_)))
  | (g_, (Root (_, s_), s), k_) -> collectSpine (g_, (s_, s), k_)
  | (g_, (Lam (d_, u_), s), k_) ->
      collectExp
        ((I.Decl (g_, (I.decSub (d_, s)))), (u_, (I.dot1 s)),
          (collectDec (g_, (d_, s), k_)))
  | (g_, ((EVar (r, GX, v_, cnstrs) as x_), s), k_) ->
      if exists (eqEVar x_) k_ then begin collectSub (g_, s, k_) end
      else begin
        (let v'_ = raiseType (GX, v_) in
         let k'_ = collectExp (I.Null, (v'_, I.id), k_) in
         ((collectSub (g_, s, (I.Decl (k'_, (EV x_)))))
           (* val _ = checkEmpty !cnstrs *)(* inefficient *))) end
| (g_, (FgnExp csfe, s), k_) ->
    I.FgnExpStd.fold csfe
      (begin function | (u_, k_) -> collectExp (g_, (u_, s), k_) end)
    k_ end(* was :
         collectSpine (G, (S, s), collectSub (G, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         *)
(* collectSpine (G, (S, s), I.Decl (collectSub (G, I.comp(t,s), K), LV L)) *)
(* -fp Sun Dec  1 21:12:12 2002 *)(* Sun Dec 16 10:54:52 2001 -fp !!! *)
(* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)(* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
           note: don't collect t again below *)
let rec collectExp (g_, us_, k_) = collectExpW (g_, (Whnf.whnf us_), k_)
let rec collectSpine =
  begin function
  | (g_, (I.Nil, _), k_) -> k_
  | (g_, (SClo (s_, s'), s), k_) ->
      collectSpine (g_, (s_, (I.comp (s', s))), k_)
  | (g_, (App (u_, s_), s), k_) ->
      collectSpine (g_, (s_, s), (collectExp (g_, (u_, s), k_))) end
let rec collectDec =
  begin function
  | (g_, (Dec (_, v_), s), k_) -> collectExp (g_, (v_, s), k_)
  | (g_, (BDec (_, (_, t)), s), k_) -> collectSub (g_, (I.comp (t, s)), k_)
  | (g_, (NDec _, s), k_) -> k_ end(* was: collectSub (I.Null, t, K) *)
(* Sat Dec  8 13:28:15 2001 -fp *)(* . |- t : Gsome, so do not compose with s *)
let rec collectSub =
  begin function
  | (g_, Shift _, k_) -> k_
  | (g_, Dot (Idx _, s), k_) -> collectSub (g_, s, k_)
  | (g_, Dot (Exp (u_), s), k_) ->
      collectSub (g_, s, (collectExp (g_, (u_, I.id), k_)))
  | (g_, Dot (Block (b_), s), k_) ->
      collectSub (g_, s, (collectBlock (g_, b_, k_))) end
let rec collectBlock =
  begin function
  | (g_, LVar ({ contents = Some (b_) }, sk, _), k_) ->
      collectBlock (g_, (I.blockSub (b_, sk)), k_)
  | (g_, (LVar (_, sk, (l, t)) as l_), k_) ->
      if exists (eqLVar l_) k_
      then begin collectSub (g_, (I.comp (t, sk)), k_) end
      else begin I.Decl ((collectSub (g_, (I.comp (t, sk)), k_)), (LV l_)) end end
(* correct?? -fp Sun Dec  1 21:15:33 2002 *)(* collectBlock (B, K) *)
let rec collectCtx =
  begin function
  | (g0_, I.Null, k_) -> (g0_, k_)
  | (g0_, Decl (g_, d_), k_) ->
      let (G0', k'_) = collectCtx (g0_, g_, k_) in
      let K'' = collectDec (G0', (d_, I.id), k'_) in
      ((I.Decl (g0_, d_)), K'') end
let rec collectCtxs =
  begin function
  | (g0_, [], k_) -> k_
  | (g0_, (g_)::gs_, k_) ->
      let (G0', k'_) = collectCtx (g0_, g_, k_) in
      collectCtxs (G0', gs_, k'_) end
let rec abstractEVar =
  begin function
  | (Decl (k'_, EV (EVar (r', _, _, _))), depth, (EVar (r, _, _, _) as x_))
      -> if r = r' then begin I.BVar (depth + 1) end
      else begin abstractEVar (k'_, (depth + 1), x_) end
  | (Decl (k'_, _), depth, x_) -> abstractEVar (k'_, (depth + 1), x_) end
(*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
let rec abstractFVar =
  begin function
  | (Decl (k'_, FV (n', _)), depth, (FVar (n, _, _) as f_)) ->
      if n = n' then begin I.BVar (depth + 1) end
      else begin abstractFVar (k'_, (depth + 1), f_) end
  | (Decl (k'_, _), depth, f_) -> abstractFVar (k'_, (depth + 1), f_) end
(*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
let rec abstractLVar =
  begin function
  | (Decl (k'_, LV (LVar (r', _, _))), depth, (LVar (r, _, _) as l_)) ->
      if r = r' then begin I.Bidx (depth + 1) end
      else begin abstractLVar (k'_, (depth + 1), l_) end
  | (Decl (k'_, _), depth, l_) -> abstractLVar (k'_, (depth + 1), l_) end
let rec abstractExpW =
  begin function
  | (k_, depth, ((Uni (l_) as u_), s)) -> u_
  | (k_, depth, (Pi ((d_, p_), v_), s)) ->
      piDepend
        (((abstractDec (k_, depth, (d_, s))), p_),
          (abstractExp (k_, (depth + 1), (v_, (I.dot1 s)))))
  | (k_, depth, (Root ((FVar _ as f_), s_), s)) ->
      I.Root
        ((abstractFVar (k_, depth, f_)),
          (abstractSpine (k_, depth, (s_, s))))
  | (k_, depth, (Root (Proj ((LVar _ as l_), i), s_), s)) ->
      I.Root
        ((I.Proj ((abstractLVar (k_, depth, l_)), i)),
          (abstractSpine (k_, depth, (s_, s))))
  | (k_, depth, (Root (h_, s_), s)) ->
      I.Root (h_, (abstractSpine (k_, depth, (s_, s))))
  | (k_, depth, (Lam (d_, u_), s)) ->
      I.Lam
        ((abstractDec (k_, depth, (d_, s))),
          (abstractExp (k_, (depth + 1), (u_, (I.dot1 s)))))
  | (k_, depth, ((EVar _ as x_), s)) ->
      I.Root
        ((abstractEVar (k_, depth, x_)), (abstractSub (k_, depth, s, I.Nil)))
  | (k_, depth, (FgnExp csfe, s)) ->
      I.FgnExpStd.Map.apply csfe
        (begin function | u_ -> abstractExp (k_, depth, (u_, s)) end) end
let rec abstractExp (k_, depth, us_) =
  abstractExpW (k_, depth, (Whnf.whnf us_))
let rec abstractSub =
  begin function
  | (k_, depth, Shift k, s_) ->
      ((if k < depth
        then
          begin abstractSub
                  (k_, depth, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
                    s_) end
      else begin s_ end)
  (* k = depth *))
  | (k_, depth, Dot (Idx k, s), s_) ->
      abstractSub (k_, depth, s, (I.App ((I.Root ((I.BVar k), I.Nil)), s_)))
  | (k_, depth, Dot (Exp (u_), s), s_) ->
      abstractSub
        (k_, depth, s, (I.App ((abstractExp (k_, depth, (u_, I.id))), s_))) end
let rec abstractSpine =
  begin function
  | (k_, depth, (I.Nil, _)) -> I.Nil
  | (k_, depth, (SClo (s_, s'), s)) ->
      abstractSpine (k_, depth, (s_, (I.comp (s', s))))
  | (k_, depth, (App (u_, s_), s)) ->
      I.App
        ((abstractExp (k_, depth, (u_, s))),
          (abstractSpine (k_, depth, (s_, s)))) end
let rec abstractDec (k_, depth, (Dec (x, v_), s)) =
  I.Dec (x, (abstractExp (k_, depth, (v_, s))))
let rec abstractSOME =
  begin function
  | (k_, Shift 0) -> I.Shift (I.ctxLength k_)
  | (k_, Shift n) -> I.Shift (I.ctxLength k_)
  | (k_, Dot (Idx k, s)) -> I.Dot ((I.Idx k), (abstractSOME (k_, s)))
  | (k_, Dot (Exp (u_), s)) ->
      I.Dot
        ((I.Exp (abstractExp (k_, 0, (u_, I.id)))), (abstractSOME (k_, s)))
  | (k_, Dot (Block (LVar _ as l_), s)) ->
      I.Dot ((I.Block (abstractLVar (k_, 0, l_))), (abstractSOME (k_, s))) end
(* n > 0 *)(* n = 0 by invariant, check for now *)
let rec abstractCtx =
  begin function
  | (k_, depth, I.Null) -> (I.Null, depth)
  | (k_, depth, Decl (g_, d_)) ->
      let (g'_, depth') = abstractCtx (k_, depth, g_) in
      let d'_ = abstractDec (k_, depth', (d_, I.id)) in
      ((I.Decl (g'_, d'_)), (depth' + 1)) end
let rec abstractCtxlist =
  begin function
  | (k_, depth, []) -> []
  | (k_, depth, (g_)::gs_) ->
      let (g'_, depth') = abstractCtx (k_, depth, g_) in
      let gs'_ = abstractCtxlist (k_, depth', gs_) in g'_ :: gs'_ end
let rec abstractKPi =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (k'_, EV (EVar (_, GX, VX, _))), v_) ->
      let v'_ = raiseType (GX, VX) in
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((abstractKPi (k'_, (I.Pi (((I.Dec (None, V'')), I.Maybe), v_))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | (Decl (k'_, FV (name, v'_)), v_) ->
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((abstractKPi (k'_, (I.Pi (((I.Dec ((Some name), V'')), I.Maybe), v_))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | (Decl (k'_, LV (LVar (r, _, (l, t)))), v_) ->
      let t' = abstractSOME (k'_, t) in
      abstractKPi (k'_, (I.Pi (((I.BDec (None, (l, t'))), I.Maybe), v_))) end
let rec abstractKLam =
  begin function
  | (I.Null, u_) -> u_
  | (Decl (k'_, EV (EVar (_, GX, VX, _))), u_) ->
      let v'_ = raiseType (GX, VX) in
      abstractKLam
        (k'_,
          (I.Lam ((I.Dec (None, (abstractExp (k'_, 0, (v'_, I.id))))), u_)))
  | (Decl (k'_, FV (name, v'_)), u_) ->
      abstractKLam
        (k'_,
          (I.Lam
             ((I.Dec ((Some name), (abstractExp (k'_, 0, (v'_, I.id))))), u_))) end
let rec abstractKCtx =
  begin function
  | I.Null -> I.Null
  | Decl (k'_, EV (EVar (_, GX, VX, _))) ->
      let v'_ = raiseType (GX, VX) in
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((I.Decl ((abstractKCtx k'_), (I.Dec (None, V''))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | Decl (k'_, FV (name, v'_)) ->
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((I.Decl ((abstractKCtx k'_), (I.Dec ((Some name), V''))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | Decl (k'_, LV (LVar (r, _, (l, t)))) ->
      let t' = abstractSOME (k'_, t) in
      I.Decl ((abstractKCtx k'_), (I.BDec (None, (l, t')))) end
let rec abstractDecImp (v_) =
  let k_ = collectExp (I.Null, (v_, I.id), I.Null) in
  let _ = checkConstraints k_ in
  ((I.ctxLength k_), (abstractKPi (k_, (abstractExp (k_, 0, (v_, I.id))))))
let rec abstractDef (u_, v_) =
  let k_ =
    collectExp
      (I.Null, (u_, I.id), (collectExp (I.Null, (v_, I.id), I.Null))) in
  let _ = checkConstraints k_ in
  ((I.ctxLength k_),
    ((abstractKLam (k_, (abstractExp (k_, 0, (u_, I.id))))),
      (abstractKPi (k_, (abstractExp (k_, 0, (v_, I.id)))))))
let rec abstractSpineExt (s_, s) =
  let k_ = collectSpine (I.Null, (s_, s), I.Null) in
  let _ = checkConstraints k_ in
  let g_ = abstractKCtx k_ in
  let s_ = abstractSpine (k_, 0, (s_, s)) in (g_, s_)
let rec abstractCtxs (gs_) =
  let k_ = collectCtxs (I.Null, gs_, I.Null) in
  let _ = checkConstraints k_ in
  ((abstractKCtx k_), (abstractCtxlist (k_, 0, gs_)))
let rec closedDec (g_, (Dec (_, v_), s)) =
  begin match collectExp (g_, (v_, s), I.Null) with
  | I.Null -> true
  | _ -> false end
let rec closedSub =
  begin function
  | (g_, Shift _) -> true
  | (g_, Dot (Idx _, s)) -> closedSub (g_, s)
  | (g_, Dot (Exp (u_), s)) ->
      (begin match collectExp (g_, (u_, I.id), I.Null) with
       | I.Null -> closedSub (g_, s)
       | _ -> false end) end
let rec closedExp (g_, (u_, s)) =
  begin match collectExp (g_, (u_, I.id), I.Null) with
  | I.Null -> true
  | _ -> false end
let rec closedCtx =
  begin function
  | I.Null -> true
  | Decl (g_, d_) -> (closedCtx g_) && (closedDec (g_, (d_, I.id))) end
let rec closedFor =
  begin function
  | (Psi, T.True) -> true
  | (Psi, All ((d_, _), f_)) ->
      (closedDEC (Psi, d_)) && (closedFor ((I.Decl (Psi, d_)), f_))
  | (Psi, Ex ((d_, _), f_)) ->
      (closedDec ((T.coerceCtx Psi), (d_, I.id))) &&
        (closedFor ((I.Decl (Psi, (T.UDec d_))), f_)) end
let rec closedDEC =
  begin function
  | (Psi, UDec (d_)) -> closedDec ((T.coerceCtx Psi), (d_, I.id))
  | (Psi, PDec (_, f_, _, _)) -> closedFor (Psi, f_) end
let rec closedCTX =
  begin function
  | I.Null -> true
  | Decl (Psi, d_) -> (closedCTX Psi) && (closedDEC (Psi, d_)) end
let rec evarsToK =
  begin function
  | [] -> I.Null
  | (x_)::xs_ -> I.Decl ((evarsToK xs_), (EV x_)) end
let rec KToEVars =
  begin function
  | I.Null -> []
  | Decl (k_, EV (x_)) -> (::) x_ KToEVars k_
  | Decl (k_, _) -> KToEVars k_ end
let rec collectEVars (g_, us_, xs_) =
  KToEVars (collectExp (g_, us_, (evarsToK xs_)))
let rec collectEVarsSpine (g_, (s_, s), xs_) =
  KToEVars (collectSpine (g_, (s_, s), (evarsToK xs_)))
let rec collectPrg =
  begin function
  | (_, (EVar (Psi, r, f_, _, _, _) as p_), k_) -> I.Decl (k_, (PV p_))
  | (Psi, T.Unit, k_) -> k_
  | (Psi, PairExp (u_, p_), k_) ->
      collectPrg (Psi, p_, (collectExp ((T.coerceCtx Psi), (u_, I.id), k_))) end
let rec abstractPVar =
  begin function
  | (Decl (k'_, PV (EVar (_, r', _, _, _, _))), depth,
     (EVar (_, r, _, _, _, _) as p_)) ->
      if r = r' then begin T.Var (depth + 1) end
      else begin abstractPVar (k'_, (depth + 1), p_) end
  | (Decl (k'_, _), depth, p_) -> abstractPVar (k'_, (depth + 1), p_) end
let rec abstractPrg =
  begin function
  | (k_, depth, (EVar _ as x_)) -> abstractPVar (k_, depth, x_)
  | (k_, depth, T.Unit) -> T.Unit
  | (k_, depth, PairExp (u_, p_)) ->
      T.PairExp
        ((abstractExp (k_, depth, (u_, I.id))),
          (abstractPrg (k_, depth, p_))) end
let rec collectTomegaSub =
  begin function
  | Shift 0 -> I.Null
  | Dot (Exp (u_), t) ->
      collectExp (I.Null, (u_, I.id), (collectTomegaSub t))
  | Dot (Block (b_), t) -> collectBlock (I.Null, b_, (collectTomegaSub t))
  | Dot (Prg (p_), t) -> collectPrg (I.Null, p_, (collectTomegaSub t)) end
let rec abstractOrder =
  begin function
  | (k_, depth, Arg (us1_, us2_)) ->
      O.Arg
        (((abstractExp (k_, depth, us1_)), I.id),
          ((abstractExp (k_, depth, us2_)), I.id))
  | (k_, depth, Simul (os_)) ->
      O.Simul (map (begin function | o_ -> abstractOrder (k_, depth, o_) end)
        os_)
  | (k_, depth, Lex (os_)) ->
      O.Lex (map (begin function | o_ -> abstractOrder (k_, depth, o_) end)
        os_) end
let rec abstractTC =
  begin function
  | (k_, depth, Abs (d_, TC)) ->
      T.Abs
        ((abstractDec (k_, depth, (d_, I.id))), (abstractTC (k_, depth, TC)))
  | (k_, depth, Conj (TC1, TC2)) ->
      T.Conj ((abstractTC (k_, depth, TC1)), (abstractTC (k_, depth, TC2)))
  | (k_, depth, Base (o_)) -> T.Base (abstractOrder (k_, depth, o_)) end
let rec abstractTCOpt =
  begin function
  | (k_, depth, None) -> None
  | (k_, depth, Some (TC)) -> Some (abstractTC (k_, depth, TC)) end
let rec abstractMetaDec =
  begin function
  | (k_, depth, UDec (d_)) -> T.UDec (abstractDec (k_, depth, (d_, I.id)))
  | (k_, depth, PDec (xx, f_, TC1, TC2)) ->
      T.PDec (xx, (abstractFor (k_, depth, f_)), TC1, TC2) end
let rec abstractFor =
  begin function
  | (k_, depth, T.True) -> T.True
  | (k_, depth, All ((MD, q_), f_)) ->
      T.All
        (((abstractMetaDec (k_, depth, MD)), q_),
          (abstractFor (k_, depth, f_)))
  | (k_, depth, Ex ((d_, q_), f_)) ->
      T.Ex
        (((abstractDec (k_, depth, (d_, I.id))), q_),
          (abstractFor (k_, depth, f_)))
  | (k_, depth, And (f1_, f2_)) ->
      T.And ((abstractFor (k_, depth, f1_)), (abstractFor (k_, depth, f2_)))
  | (k_, depth, World (w_, f_)) ->
      T.World (w_, (abstractFor (k_, depth, f_))) end
let rec abstractPsi =
  begin function
  | I.Null -> I.Null
  | Decl (k'_, EV (EVar (_, GX, VX, _))) ->
      let v'_ = raiseType (GX, VX) in
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((I.Decl ((abstractPsi k'_), (T.UDec (I.Dec (None, V'')))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | Decl (k'_, FV (name, v'_)) ->
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      ((I.Decl ((abstractPsi k'_), (T.UDec (I.Dec ((Some name), V'')))))
        (* enforced by reconstruction -kw
          val _ = checkType V'' *))
  | Decl (k'_, LV (LVar (r, _, (l, t)))) ->
      let t' = abstractSOME (k'_, t) in
      I.Decl ((abstractPsi k'_), (T.UDec (I.BDec (None, (l, t')))))
  | Decl (k'_, PV (EVar (GX, _, FX, TC1, TC2, _))) ->
      let f'_ = abstractFor (k'_, 0, (T.forSub (FX, T.id))) in
      let TC1' = abstractTCOpt (k'_, 0, TC1) in
      let TC2' = abstractTCOpt (k'_, 0, TC2) in
      I.Decl ((abstractPsi k'_), (T.PDec (None, f'_, TC1, TC2))) end(* What's happening with TCs? *)
(* What's happening with GX? *)
let rec abstractTomegaSub t =
  let k_ = collectTomegaSub t in
  let t' = abstractTomegaSub' (k_, 0, t) in
  let Psi = abstractPsi k_ in (Psi, t')
let rec abstractTomegaSub' =
  begin function
  | (k_, depth, Shift 0) -> T.Shift depth
  | (k_, depth, Dot (Exp (u_), t)) ->
      T.Dot
        ((T.Exp (abstractExp (k_, depth, (u_, I.id)))),
          (abstractTomegaSub' (k_, depth, t)))
  | (k_, depth, Dot (Block (b_), t)) ->
      T.Dot
        ((T.Block (abstractLVar (k_, depth, b_))),
          (abstractTomegaSub' (k_, depth, t)))
  | (k_, depth, Dot (Prg (p_), t)) ->
      T.Dot
        ((T.Prg (abstractPrg (k_, depth, p_))),
          (abstractTomegaSub' (k_, depth, t))) end
let rec abstractTomegaPrg (p_) =
  let k_ = collectPrg (I.Null, p_, I.Null) in
  let p'_ = abstractPrg (k_, 0, p_) in let Psi = abstractPsi k_ in (Psi, p'_)
let raiseType = raiseType
let raiseTerm = raiseTerm
let piDepend = piDepend
let closedDec = closedDec
let closedSub = closedSub
let closedExp = closedExp
let abstractDecImp = abstractDecImp
let abstractDef = abstractDef
let abstractCtxs = abstractCtxs
let abstractTomegaSub = abstractTomegaSub
let abstractTomegaPrg = abstractTomegaPrg
let abstractSpine = abstractSpineExt
let collectEVars = collectEVars
let collectEVarsSpine = collectEVarsSpine
let closedCtx = closedCtx
let closedCTX = closedCTX end
