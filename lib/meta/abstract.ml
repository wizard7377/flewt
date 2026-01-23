module type MTPABSTRACT  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type approxFor_ =
      | Head of (IntSyn.dctx * (FunSyn.for_ * IntSyn.sub_) * int) 
      | Block of ((IntSyn.dctx * IntSyn.sub_ * int * IntSyn.dec_ list) *
      approxFor_) 
    val weaken : (IntSyn.dctx * IntSyn.cid) -> IntSyn.sub_
    val raiseType : (IntSyn.dctx * IntSyn.exp_) -> IntSyn.exp_
    val abstractSub :
      (IntSyn.sub_ * StateSyn.tag_ IntSyn.ctx_ * (IntSyn.dctx * StateSyn.tag_
        IntSyn.ctx_) * IntSyn.sub_ * StateSyn.tag_ IntSyn.ctx_) ->
        ((IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_) * IntSyn.sub_)
    val abstractSub' :
      ((IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_) * IntSyn.sub_ *
        StateSyn.tag_ IntSyn.ctx_) ->
        ((IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_) * IntSyn.sub_)
    val abstractApproxFor : approxFor_ -> FunSyn.for_
  end


module MTPAbstract(MTPAbstract:sig
                                 module StateSyn' : STATESYN
                                 module Whnf : WHNF
                                 module Constraints : CONSTRAINTS
                                 module Unify : UNIFY
                                 module Subordinate : SUBORDINATE
                                 module TypeCheck : TYPECHECK
                                 module FunTypeCheck : FUNTYPECHECK
                                 module Abstract : ABSTRACT
                               end) : MTPABSTRACT =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type approxFor_ =
      | Head of (IntSyn.dctx * (FunSyn.for_ * IntSyn.sub_) * int) 
      | Block of ((IntSyn.dctx * IntSyn.sub_ * int * IntSyn.dec_ list) *
      approxFor_) 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module C = Constraints
    type eBVar_ =
      | EV of (I.exp_ option ref * I.exp_ * S.tag_ * int) 
      | BV of (I.dec_ * S.tag_) 
    let rec checkEmpty =
      begin function
      | [] -> ()
      | cnstrL ->
          (begin match C.simplify cnstrL with
           | [] -> ()
           | _ -> raise (Error "Typing ambiguous -- unresolved constraints") end) end
  let rec eqEVar arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | (EVar (r1, _, _, _), EV (r2, _, _, _)) -> r1 = r2
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
      or_ ((occursInDec (k, d_)), (occursInExp ((k + 1), v_))) end
let rec occursInHead =
  begin function
  | (k, BVar k', DP) -> if k = k' then begin I.Maybe end else begin DP end
  | (k, Const _, DP) -> DP | (k, Def _, DP) -> DP
  | (k, Skonst _, I.No) -> I.No | (k, Skonst _, I.Meta) -> I.Meta
  | (k, Skonst _, I.Maybe) -> I.Meta end
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
let rec weaken =
  begin function
  | (I.Null, a) -> I.id
  | (Decl (g'_, (Dec (name, v_) as d_)), a) ->
      let w' = weaken (g'_, a) in
      if Subordinate.belowEq ((I.targetFam v_), a) then begin I.dot1 w' end
        else begin I.comp (w', I.shift) end end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec restore =
  begin function
  | (0, Gp) -> (Gp, I.Null)
  | (n, Decl (g_, d_)) ->
      let (Gp', GX') = restore ((n - 1), g_) in (Gp', (I.Decl (GX', d_))) end
let rec concat =
  begin function
  | (Gp, I.Null) -> Gp
  | (Gp, Decl (g_, d_)) -> I.Decl ((concat (Gp, g_)), d_) end
let rec collectExpW =
  begin function
  | (t_, d, g_, (Uni (l_), s), k_) -> k_
  | (t_, d, g_, (Pi ((d_, _), v_), s), k_) ->
      collectExp
        (t_, d, (I.Decl (g_, (I.decSub (d_, s)))), (v_, (I.dot1 s)),
          (collectDec (t_, d, g_, (d_, s), k_)))
  | (t_, d, g_, (Root (_, s_), s), k_) ->
      collectSpine ((S.decrease t_), d, g_, (s_, s), k_)
  | (t_, d, g_, (Lam (d_, u_), s), k_) ->
      collectExp
        (t_, d, (I.Decl (g_, (I.decSub (d_, s)))), (u_, (I.dot1 s)),
          (collectDec (t_, d, g_, (d_, s), k_)))
  | (t_, d, g_, ((EVar (r, GdX, v_, cnstrs) as x_), s), k_) ->
      if exists (eqEVar x_) k_ then begin collectSub (t_, d, g_, s, k_) end
      else begin
        (let (Gp, GX) = restore (((I.ctxLength GdX) - d), GdX) in
         let _ = checkEmpty !cnstrs in
         let w = weaken (GX, (I.targetFam v_)) in
         let iw = Whnf.invert w in
         let GX' = Whnf.strengthen (iw, GX) in
         let EVar (r', _, _, _) as x'_ =
           I.newEVar ((concat (Gp, GX')), (I.EClo (v_, iw))) in
         let _ = Unify.instantiateEVar (r, (I.EClo (x'_, w)), []) in
         let v'_ = raiseType (GX', (I.EClo (v_, iw))) in
         ((collectSub
             (t_, d, g_, (I.comp (w, s)),
               (I.Decl
                  ((collectExp (t_, d, Gp, (v'_, I.id), k_)),
                    (EV (r', v'_, t_, d))))))
           (* optimization possible for d = 0 *))) end
  | (t_, d, g_, (FgnExp csfe, s), k_) ->
      I.FgnExpStd.fold csfe
        (begin function | (u_, k'_) -> collectExp (t_, d, g_, (u_, s), k'_) end)
      k_ end
let rec collectExp (t_, d, g_, us_, k_) =
  collectExpW (t_, d, g_, (Whnf.whnf us_), k_)
let rec collectSpine =
  begin function
  | (t_, d, g_, (I.Nil, _), k_) -> k_
  | (t_, d, g_, (SClo (s_, s'), s), k_) ->
      collectSpine (t_, d, g_, (s_, (I.comp (s', s))), k_)
  | (t_, d, g_, (App (u_, s_), s), k_) ->
      collectSpine
        (t_, d, g_, (s_, s), (collectExp (t_, d, g_, (u_, s), k_))) end
let rec collectDec (t_, d, g_, (Dec (_, v_), s), k_) =
  collectExp (t_, d, g_, (v_, s), k_)
let rec collectSub =
  begin function
  | (t_, d, g_, Shift _, k_) -> k_
  | (t_, d, g_, Dot (Idx _, s), k_) -> collectSub (t_, d, g_, s, k_)
  | (t_, d, g_, Dot (Exp (u_), s), k_) ->
      collectSub (t_, d, g_, s, (collectExp (t_, d, g_, (u_, I.id), k_))) end
let rec abstractEVar =
  begin function
  | (Decl (k'_, EV (r', _, _, d)), depth, (EVar (r, _, _, _) as x_)) ->
      if r = r' then begin ((I.BVar (depth + 1)), d) end
      else begin abstractEVar (k'_, (depth + 1), x_) end
  | (Decl (k'_, BV _), depth, x_) -> abstractEVar (k'_, (depth + 1), x_) end
let rec lookupBV (k_, i) =
  let rec lookupBV' =
    begin function
    | (Decl (k_, EV (r, v_, _, _)), i, k) -> lookupBV' (k_, i, (k + 1))
    | (Decl (k_, BV _), 1, k) -> k
    | (Decl (k_, BV _), i, k) -> lookupBV' (k_, (i - 1), (k + 1)) end in
((lookupBV' (k_, i, 1))
  (* lookupBV' I.Null cannot occur by invariant *))
let rec abstractExpW =
  begin function
  | (k_, depth, ((Uni (l_) as u_), s)) -> u_
  | (k_, depth, (Pi ((d_, p_), v_), s)) ->
      piDepend
        (((abstractDec (k_, depth, (d_, s))), p_),
          (abstractExp (k_, (depth + 1), (v_, (I.dot1 s)))))
  | (k_, depth, (Root ((BVar k as h_), s_), s)) ->
      if k > depth
      then
        begin let k' = lookupBV (k_, (k - depth)) in
              I.Root
                ((I.BVar (k' + depth)), (abstractSpine (k_, depth, (s_, s)))) end
      else begin I.Root (h_, (abstractSpine (k_, depth, (s_, s)))) end
  | (k_, depth, (Root (h_, s_), s)) ->
      I.Root (h_, (abstractSpine (k_, depth, (s_, s))))
  | (k_, depth, (Lam (d_, u_), s)) ->
      I.Lam
        ((abstractDec (k_, depth, (d_, s))),
          (abstractExp (k_, (depth + 1), (u_, (I.dot1 s)))))
  | (k_, depth, ((EVar (_, g_, _, _) as x_), s)) ->
      let (h_, d) = abstractEVar (k_, depth, x_) in
      I.Root
        (h_, (abstractSub (((I.ctxLength g_) - d), k_, depth, s, I.Nil)))
  | (k_, depth, (FgnExp csfe, s)) ->
      I.FgnExpStd.Map.apply csfe
        (begin function | u_ -> abstractExp (k_, depth, (u_, s)) end) end
(* s = id *)
let rec abstractExp (k_, depth, us_) =
  abstractExpW (k_, depth, (Whnf.whnf us_))
let rec abstractSub =
  begin function
  | (n, k_, depth, Shift k, s_) ->
      ((if n > 0
        then
          begin abstractSub
                  (n, k_, depth,
                    (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), s_) end
      else begin s_ end)
  (* n = 0 *))
  | (n, k_, depth, Dot (Idx k, s), s_) ->
      let h_ =
        if k > depth
        then begin let k' = lookupBV (k_, (k - depth)) in I.BVar (k' + depth) end
        else begin I.BVar k end in
abstractSub ((n - 1), k_, depth, s, (I.App ((I.Root (h_, I.Nil)), s_)))
| (n, k_, depth, Dot (Exp (u_), s), s_) ->
    abstractSub
      ((n - 1), k_, depth, s,
        (I.App ((abstractExp (k_, depth, (u_, I.id))), s_))) end
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
let rec getLevel =
  begin function
  | Uni _ -> I.Kind
  | Pi (_, u_) -> getLevel u_
  | Root _ -> I.Type
  | Redex (u_, _) -> getLevel u_
  | Lam (_, u_) -> getLevel u_
  | EClo (u_, _) -> getLevel u_ end
let rec checkType (v_) =
  begin match getLevel v_ with
  | I.Type -> ()
  | _ -> raise (Error "Typing ambiguous -- free type variable") end
let rec abstractCtx =
  begin function
  | I.Null -> (I.Null, I.Null)
  | Decl (k'_, EV (_, v'_, (Lemma b as t_), _)) ->
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      let _ = checkType V'' in
      let (g'_, b'_) = abstractCtx k'_ in
      let d'_ = I.Dec (None, V'') in
      ((I.Decl (g'_, d'_)), (I.Decl (b'_, t_)))
  | Decl (k'_, EV (_, v'_, (S.None as t_), _)) ->
      let V'' = abstractExp (k'_, 0, (v'_, I.id)) in
      let _ = checkType V'' in
      let (g'_, b'_) = abstractCtx k'_ in
      let d'_ = I.Dec (None, V'') in
      ((I.Decl (g'_, d'_)), (I.Decl (b'_, S.None)))
  | Decl (k'_, BV (d_, t_)) ->
      let d'_ = abstractDec (k'_, 0, (d_, I.id)) in
      let (g'_, b'_) = abstractCtx k'_ in
      ((I.Decl (g'_, d'_)), (I.Decl (b'_, t_))) end
let rec abstractGlobalSub =
  begin function
  | (k_, Shift _, I.Null) -> I.Shift (I.ctxLength k_)
  | (k_, Shift n, (Decl _ as b_)) ->
      abstractGlobalSub
        (k_, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), b_)
  | (k_, Dot (Idx k, s'), Decl (b_, (Parameter _ as t_))) ->
      I.Dot ((I.Idx (lookupBV (k_, k))), (abstractGlobalSub (k_, s', b_)))
  | (k_, Dot (Exp (u_), s'), Decl (b_, (Lemma _ as t_))) ->
      I.Dot
        ((I.Exp (abstractExp (k_, 0, (u_, I.id)))),
          (abstractGlobalSub (k_, s', b_))) end
let rec collectGlobalSub =
  begin function
  | (g0_, Shift _, I.Null, collect) -> collect
  | (g0_, s, (Decl (_, Parameter (Some l)) as b_), collect) ->
      let LabelDec (name, _, g2_) = F.labelLookup l in
      skip (g0_, (List.length g2_), s, b_, collect)
  | (g0_, Dot (Exp (u_), s), Decl (b_, t_), collect) ->
      collectGlobalSub
        (g0_, s, b_,
          (begin function
           | (d, k_) ->
               collect (d, (collectExp (t_, d, g0_, (u_, I.id), k_))) end)) end
let rec skip =
  begin function
  | (g0_, 0, s, b_, collect) -> collectGlobalSub (g0_, s, b_, collect)
  | (Decl (g0_, d_), n, s, Decl (b_, (Parameter _ as t_)), collect) ->
      skip
        (g0_, (n - 1), (I.invDot1 s), b_,
          (begin function
           | (d, k_) -> collect ((d + 1), (I.Decl (k_, (BV (d_, t_))))) end)) end
let rec abstractNew ((g0_, b0_), s, b_) =
  let cf =
    collectGlobalSub (g0_, s, b_, (begin function | (_, k'_) -> k'_ end)) in
let k_ = cf (0, I.Null) in
((abstractCtx k_), (abstractGlobalSub (k_, s, b_)))
let rec abstractSubAll (t, b1_, (g0_, b0_), s, b_) =
  let rec skip'' =
    begin function
    | (k_, (I.Null, I.Null)) -> k_
    | (k_, (Decl (g0_, d_), Decl (b0_, t_))) ->
        I.Decl ((skip'' (k_, (g0_, b0_))), (BV (d_, t_))) end in
let collect2 =
  collectGlobalSub (g0_, s, b_, (begin function | (_, k'_) -> k'_ end)) in
let collect0 =
  collectGlobalSub (I.Null, t, b1_, (begin function | (_, k'_) -> k'_ end)) in
let k0_ = collect0 (0, I.Null) in
let k1_ = skip'' (k0_, (g0_, b0_)) in
let d = I.ctxLength g0_ in
let k_ = collect2 (d, k1_) in
((((abstractCtx k_), (abstractGlobalSub (k_, s, b_))))
  (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *))
let rec abstractFor =
  begin function
  | (k_, depth, (All (Prim (d_), f_), s)) ->
      F.All
        ((F.Prim (abstractDec (k_, depth, (d_, s)))),
          (abstractFor (k_, (depth + 1), (f_, (I.dot1 s)))))
  | (k_, depth, (Ex (d_, f_), s)) ->
      F.Ex
        ((abstractDec (k_, depth, (d_, s))),
          (abstractFor (k_, (depth + 1), (f_, (I.dot1 s)))))
  | (k_, depth, (F.True, s)) -> F.True
  | (k_, depth, (And (f1_, f2_), s)) ->
      F.And
        ((abstractFor (k_, depth, (f1_, s))),
          (abstractFor (k_, depth, (f2_, s)))) end
let rec allClo =
  begin function
  | (I.Null, f_) -> f_
  | (Decl (Gx, d_), f_) -> allClo (Gx, (F.All ((F.Prim d_), f_))) end
let rec convert =
  begin function
  | I.Null -> I.Null
  | Decl (g_, d_) -> I.Decl ((convert g_), (BV (d_, (S.Parameter None)))) end
let rec createEmptyB =
  begin function | 0 -> I.Null | n -> I.Decl ((createEmptyB (n - 1)), S.None) end
let rec lower =
  begin function
  | (_, 0) -> I.Null
  | (Decl (g_, d_), n) -> I.Decl ((lower (g_, (n - 1))), d_) end
let rec split =
  begin function
  | (g_, 0) -> (g_, I.Null)
  | (Decl (g_, d_), n) ->
      let (g1_, g2_) = split (g_, (n - 1)) in (g1_, (I.Decl (g2_, d_))) end
let rec shift =
  begin function | I.Null -> I.shift | Decl (g_, _) -> I.dot1 (shift g_) end
let rec ctxSub =
  begin function
  | ([], s) -> []
  | ((d_)::g_, s) -> (::) (I.decSub (d_, s)) ctxSub (g_, (I.dot1 s)) end
let rec weaken2 =
  begin function
  | (I.Null, a, i) -> (I.id, ((begin function | s_ -> s_ end)))
  | (Decl (g'_, (Dec (name, v_) as d_)), a, i) ->
      let (w', s'_) = weaken2 (g'_, a, (i + 1)) in
      if Subordinate.belowEq ((I.targetFam v_), a)
      then
        begin ((I.dot1 w'),
                ((begin function
                  | s_ -> I.App ((I.Root ((I.BVar i), I.Nil)), s_) end))) end
      else begin ((I.comp (w', I.shift)), s'_) end end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) ->
      raiseType
        (g_,
          (Abstract.piDepend (((Whnf.normalizeDec (d_, I.id)), I.Maybe), v_))) end
let rec raiseFor =
  begin function
  | (k, Gorig, (F.True as f_), w, sc) -> f_
  | (k, Gorig, Ex (Dec (name, v_), f_), w, sc) ->
      let g_ = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
      let g = I.ctxLength g_ in
      let s = sc (w, k) in
      let v'_ = I.EClo (v_, s) in
      let (nw, s_) = weaken2 (g_, (I.targetFam v_), 1) in
      let iw = Whnf.invert nw in
      let Gw = Whnf.strengthen (iw, g_) in
      let V'' = Whnf.normalize (v'_, iw) in
      let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
      let S''' = s_ I.Nil in
      let sc' =
        begin function
        | (w', k') ->
            let s' = sc (w', k') in
            ((I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s'))
              (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
              (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)) end in
      let f'_ = raiseFor ((k + 1), Gorig, f_, (I.comp (w, I.shift)), sc') in
      ((F.Ex ((I.Dec (name, V''')), f'_))
        (* G0, {G}GF[..], G |- s : G0, G, GF *)(* G0, {G}GF[..], G |- V' : type *)
        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
        (* Generalize the invariant for Whnf.strengthen --cs *)(* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
        (* G0, {G}GF[..], G |- s : G0, G, GF *))
  | (k, Gorig, All (Prim (Dec (name, v_)), f_), w, sc) ->
      let g_ = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
      let g = I.ctxLength g_ in
      let s = sc (w, k) in
      let v'_ = I.EClo (v_, s) in
      let (nw, s_) = weaken2 (g_, (I.targetFam v_), 1) in
      let iw = Whnf.invert nw in
      let Gw = Whnf.strengthen (iw, g_) in
      let V'' = Whnf.normalize (v'_, iw) in
      let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
      let S''' = s_ I.Nil in
      let sc' =
        begin function
        | (w', k') ->
            let s' = sc (w', k') in
            ((I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s'))
              (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
              (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)) end in
      let f'_ = raiseFor ((k + 1), Gorig, f_, (I.comp (w, I.shift)), sc') in
      ((F.All ((F.Prim (I.Dec (name, V'''))), f'_))
        (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                         G0, {G}GF[..], G |- s : G0, G, GF *)
        (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
        (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
        (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
        (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
        (* G0, {G}GF[..], G |- s : G0, G, GF *)(* G0, {G}GF[..], G |- V' : type *)
        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
        (* Generalize the invariant for Whnf.strengthen --cs *)(* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
        (* G0, {G}GF[..], G |- s : G0, G, GF *)) end
let rec extend =
  begin function
  | (k_, []) -> k_
  | (k_, (d_)::l_) -> extend ((I.Decl (k_, (BV (d_, S.None)))), l_) end
let rec makeFor =
  begin function
  | (k_, w, Head (g_, (f_, s), d)) ->
      let cf =
        collectGlobalSub
          (g_, s, (createEmptyB d), (begin function | (_, k'_) -> k'_ end)) in
    let k = I.ctxLength k_ in
    let k'_ = cf ((I.ctxLength g_), k_) in
    let k' = I.ctxLength k'_ in
    let (GK, BK) = abstractCtx k'_ in
    let _ = if !Global.doubleCheck then begin TypeCheck.typeCheckCtx GK end
      else begin () end in
    let w' = I.comp (w, (I.Shift (k' - k))) in
    let FK = abstractFor (k'_, 0, (f_, s)) in
    let _ = if !Global.doubleCheck then begin FunTypeCheck.isFor (GK, FK) end
      else begin () end in
    let (GK1, GK2) = split (GK, (k' - k)) in (((GK1, (allClo (GK2, FK))))
      (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *))
| (k_, w, Block ((g_, t, d, g2_), AF)) ->
    let k = I.ctxLength k_ in
    let collect =
      collectGlobalSub
        (g_, t, (createEmptyB d), (begin function | (_, k'_) -> k'_ end)) in
    let k'_ = collect ((I.ctxLength g_), k_) in
    let k' = I.ctxLength k'_ in
    let K'' = extend (k'_, g2_) in
    let w' = F.dot1n ((F.listToCtx g2_), (I.comp (w, (I.Shift (k' - k))))) in
    let (GK, f'_) = makeFor (K'', w', AF) in
    let _ =
      if !Global.doubleCheck then begin FunTypeCheck.isFor (GK, f'_) end
      else begin () end in
    let (GK1, GK2) = split (GK, (List.length g2_)) in
    let F'' =
      raiseFor
        (0, GK2, f'_, I.id, (begin function | (w, _) -> F.dot1n (GK2, w) end)) in
    let _ =
      if !Global.doubleCheck then begin FunTypeCheck.isFor (GK1, F'') end
      else begin () end in
    let (GK11, GK12) = split (GK1, (k' - k)) in
    let F''' = allClo (GK12, F'') in
    let _ =
      if !Global.doubleCheck then begin FunTypeCheck.isFor (GK11, F''') end
      else begin () end in
    (((GK11, F'''))(* BUG *)) end
let rec abstractApproxFor =
  begin function
  | Head (g_, _, _) as AF ->
      let (_, f_) = makeFor ((convert g_), I.id, AF) in f_
  | Block ((g_, _, _, _), _) as AF ->
      let (_, f_) = makeFor ((convert g_), I.id, AF) in f_ end
let weaken = weaken
let raiseType = raiseType
let abstractSub = abstractSubAll
let abstractSub' = abstractNew
let abstractApproxFor = abstractApproxFor end
