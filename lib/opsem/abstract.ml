module type ABSTRACTTABLED  =
  sig
    exception Error of string 
    val abstractEVarCtx :
      (CompSyn.dProg_ * IntSyn.exp_ * IntSyn.sub_) ->
        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ *
          TableParam.resEqn_ * IntSyn.sub_)
    val abstractAnswSub : IntSyn.sub_ -> (IntSyn.dctx * IntSyn.sub_)
    val raiseType : (IntSyn.dctx * IntSyn.exp_) -> IntSyn.exp_
  end


module AbstractTabled(AbstractTabled:sig
                                       module Whnf : WHNF
                                       module Unify : UNIFY
                                       module Constraints : CONSTRAINTS
                                       module Subordinate : SUBORDINATE
                                       module Print : PRINT
                                       module Conv : CONV
                                     end) : ABSTRACTTABLED =
  struct
    exception Error of string 
    module I = IntSyn
    module C = CompSyn
    type duplicates_ =
      | AV of (I.exp_ * int) 
      | FGN of int 
    type seenIn =
      | TypeLabel 
      | Body 
    type existVars_ =
      | EV of I.exp_ 
    let rec lengthSub =
      begin function | Shift n -> 0 | Dot (e_, s) -> (+) 1 lengthSub s end
    let rec compose' =
      begin function
      | (IntSyn.Null, g_) -> g_
      | (Decl (g'_, d_), g_) -> IntSyn.Decl ((compose' (g'_, g_)), d_) end
  let rec isId =
    begin function
    | Shift n -> n = 0
    | Dot (Idx n, s') as s -> isId' (s, 0)
    | Dot (I.Undef, s') as s -> isId' (s, 0)
    | Dot (Exp _, s) -> false end
let rec isId' =
  begin function
  | (Shift n, k) -> n = k
  | (Dot (Idx i, s), k) -> let k' = k + 1 in (i = k') && (isId' (s, k'))
  | (Dot (I.Undef, s), k) -> isId' (s, (k + 1)) end
let rec equalCtx =
  begin function
  | (I.Null, s, I.Null, s') -> true
  | (Decl (g_, d_), s, Decl (g'_, d'_), s') ->
      (Conv.convDec ((d_, s), (d'_, s'))) &&
        (equalCtx (g_, (I.dot1 s), g'_, (I.dot1 s')))
  | (Decl (g_, d_), s, I.Null, s') -> false
  | (I.Null, s, Decl (g'_, d'_), s') -> false end
let rec eqEVarW arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
  | (_, _) -> false end
let rec eqEVar (x1_) (EV (x2_)) =
  let (X1', s) = Whnf.whnf (x1_, I.id) in
  let (X2', s) = Whnf.whnf (x2_, I.id) in eqEVarW X1' (EV X2')(* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
let rec member' (p_) (k_) =
  let rec exists' =
    begin function
    | I.Null -> None
    | Decl (k'_, (l, EV (y_))) -> if p_ (EV y_) then begin Some l end
        else begin exists' k'_ end end in
exists' k_
let rec member (p_) (k_) =
  let rec exists' =
    begin function
    | I.Null -> None
    | Decl (k'_, (i, y_)) -> if p_ y_ then begin Some i end
        else begin exists' k'_ end end in
exists' k_
let rec update' (p_) (k_) =
  let rec update' =
    begin function
    | I.Null -> I.Null
    | Decl (k'_, (label, y_)) ->
        if p_ y_ then begin I.Decl (k'_, (Body, y_)) end
        else begin I.Decl ((update' k'_), (label, y_)) end end in
update' k_
let rec update (p_) (k_) =
  let rec update' =
    begin function
    | I.Null -> I.Null
    | Decl (k'_, ((label, i), y_)) ->
        if p_ y_ then begin I.Decl (k'_, ((Body, i), y_)) end
        else begin I.Decl ((update' k'_), ((label, i), y_)) end end in
update' k_
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
  | (k, Const _, DP) -> DP | (k, Def _, DP) -> DP | (k, FgnConst _, DP) -> DP
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
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec reverseCtx =
  begin function
  | (I.Null, g_) -> g_
  | (Decl (g_, d_), g'_) -> reverseCtx (g_, (I.Decl (g'_, d_))) end
let rec ctxToEVarSub =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, Dec (_, a_)), s) ->
      let s' = ctxToEVarSub (g_, s) in
      let x_ = IntSyn.newEVar (IntSyn.Null, (I.EClo (a_, s'))) in
      IntSyn.Dot ((IntSyn.Exp x_), s') end
let rec collectExpW =
  begin function
  | (Gss, Gl, (Uni (l_), s), k_, DupVars, flag, d) -> (k_, DupVars)
  | (Gss, Gl, (Pi ((d_, _), v_), s), k_, DupVars, flag, d) ->
      let (k'_, _) = collectDec (Gss, (d_, s), (k_, DupVars), d, false) in
      ((collectExp
          (Gss, (I.Decl (Gl, (I.decSub (d_, s)))), (v_, (I.dot1 s)), k'_,
            DupVars, flag, d))
        (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *))
  | (Gss, Gl, (Root (_, s_), s), k_, DupVars, flag, d) ->
      collectSpine (Gss, Gl, (s_, s), k_, DupVars, flag, d)
  | (Gss, Gl, (Lam (d_, u_), s), k_, DupVars, flag, d) ->
      let (k'_, _) = collectDec (Gss, (d_, s), (k_, DupVars), d, false) in
      collectExp
        (Gss, (I.Decl (Gl, (I.decSub (d_, s)))), (u_, (I.dot1 s)), k'_,
          DupVars, flag, (d + 1))
  | (Gss, Gl, ((EVar (r, GX, v_, cnstrs) as x_), s), k_, DupVars, flag, d) ->
      collectEVar (Gss, Gl, (x_, s), k_, DupVars, flag, d)
  | (Gss, Gl, (FgnExp csfe, s), k_, DupVars, flag, d) ->
      I.FgnExpStd.fold csfe
        (begin function
         | (u_, KD') ->
             let (k'_, Dup) = KD' in
             collectExp (Gss, Gl, (u_, s), k'_, Dup, false, d) end)
      (k_, (I.Decl (DupVars, (FGN d)))) end
let rec collectExp (Gss, Gl, us_, k_, DupVars, flag, d) =
  collectExpW (Gss, Gl, (Whnf.whnf us_), k_, DupVars, flag, d)
let rec collectSpine =
  begin function
  | (Gss, Gl, (I.Nil, _), k_, DupVars, flag, d) -> (k_, DupVars)
  | (Gss, Gl, (SClo (s_, s'), s), k_, DupVars, flag, d) ->
      collectSpine (Gss, Gl, (s_, (I.comp (s', s))), k_, DupVars, flag, d)
  | (Gss, Gl, (App (u_, s_), s), k_, DupVars, flag, d) ->
      let (k'_, DupVars') =
        collectExp (Gss, Gl, (u_, s), k_, DupVars, flag, d) in
      collectSpine (Gss, Gl, (s_, s), k'_, DupVars', flag, d) end
let rec collectEVarFapStr
  (Gss, Gl, ((x'_, v'_), w), ((EVar (r, GX, v_, cnstrs) as x_), s), k_,
   DupVars, flag, d)
  =
  ((begin match member' (eqEVar x_) k_ with
    | Some label ->
        ((if flag
          then
            begin collectSub
                    (Gss, Gl, s, k_, (I.Decl (DupVars, (AV (x_, d)))), flag,
                      d) end
        else begin collectSub (Gss, Gl, s, k_, DupVars, flag, d) end)
  (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
  (* since X has occurred before, we do not traverse its type V' *))
  | None -> let label = if flag then begin Body end else begin TypeLabel end in
let (k'_, DupVars') =
  collectExp ((I.Null, I.id), I.Null, (v'_, I.id), k_, DupVars, false, d) in
((collectSub
    (Gss, Gl, (I.comp (w, s)), (I.Decl (k'_, (label, (EV x'_)))), DupVars',
      flag, d))
  (*          val V' = raiseType (GX, V)  inefficient! *)) end)
(* we have seen X before *))
let rec collectEVarNFapStr
  (Gss, Gl, ((x'_, v'_), w), ((EVar (r, GX, v_, cnstrs) as x_), s), k_,
   DupVars, flag, d)
  =
  ((begin match member' (eqEVar x_) k_ with
    | Some label ->
        ((if flag
          then
            begin collectSub
                    (Gss, Gl, s, k_, (I.Decl (DupVars, (AV (x_, d)))), flag,
                      d) end
        else begin collectSub (Gss, Gl, s, k_, DupVars, flag, d) end)
  (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*))
  | None -> let label = if flag then begin Body end else begin TypeLabel end in
let (k'_, DupVars') =
  collectExp ((I.Null, I.id), I.Null, (v'_, I.id), k_, DupVars, false, d) in
((if flag
  then
    begin collectSub
            (Gss, Gl, (I.comp (w, s)), (I.Decl (k'_, (label, (EV x'_)))),
              (I.Decl (DupVars', (AV (x'_, d)))), flag, d) end
  else begin
    collectSub
      (Gss, Gl, (I.comp (w, s)), (I.Decl (k'_, (label, (EV x'_)))), DupVars',
        flag, d) end)
(* val V' = raiseType (GX, V)  inefficient! *)) end)
(* we have seen X before, i.e. it was already strengthened *))
let rec collectEVarStr
  (((gs_, ss) as Gss), Gl, ((EVar (r, GX, v_, cnstrs) as x_), s), k_,
   DupVars, flag, d)
  =
  let w = Subordinate.weaken (GX, (I.targetFam v_)) in
  let iw = Whnf.invert w in
  let GX' = Whnf.strengthen (iw, GX) in
  let EVar (r', _, _, _) as x'_ = I.newEVar (GX', (I.EClo (v_, iw))) in
  let _ = Unify.instantiateEVar (r, (I.EClo (x'_, w)), []) in
  let v'_ = raiseType (GX', (I.EClo (v_, iw))) in
  ((if isId (I.comp (w, (I.comp (ss, s))))
    then
      begin collectEVarFapStr
              (Gss, Gl, ((x'_, v'_), w), (x_, s), k_, DupVars, flag, d) end
    else begin
      collectEVarNFapStr
        (Gss, Gl, ((x'_, v'_), w), (x_, s), k_, DupVars, flag, d) end)
    (* equalCtx (Gs, I.id, GX', s) *)(* fully applied *)
    (* not fully applied *)(* ? *))
let rec collectEVarFap
  (Gss, Gl, ((EVar (r, GX, v_, cnstrs) as x_), s), k_, DupVars, flag, d) =
  ((begin match member (eqEVar x_) k_ with
    | Some label ->
        ((if flag
          then
            begin collectSub
                    (Gss, Gl, s, k_, (I.Decl (DupVars, (AV (x_, d)))), flag,
                      d) end
        else begin collectSub (Gss, Gl, s, k_, DupVars, flag, d) end)
  (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
  (* since X has occurred before, we do not traverse its type V' *))
  | None -> let label = if flag then begin Body end else begin TypeLabel end in
let v'_ = raiseType (GX, v_) in
let (k'_, DupVars') =
  collectExp ((I.Null, I.id), I.Null, (v'_, I.id), k_, DupVars, false, d) in
((collectSub
    (Gss, Gl, s, (I.Decl (k'_, (label, (EV x_)))), DupVars', flag, d))
  (* val _ = checkEmpty !cnstrs *)(* inefficient! *)) end)
(* we have seen X before *))
let rec collectEVarNFap
  (Gss, Gl, ((EVar (r, GX, v_, cnstrs) as x_), s), k_, DupVars, flag, d) =
  begin match member' (eqEVar x_) k_ with
  | Some label ->
      ((if flag
        then
          begin collectSub
                  (Gss, Gl, s, k_, (I.Decl (DupVars, (AV (x_, d)))), flag, d) end
      else begin collectSub (Gss, Gl, s, k_, DupVars, flag, d) end)
  (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *))
  | None -> let label = if flag then begin Body end else begin TypeLabel end in
let v'_ = raiseType (GX, v_) in
let (k'_, DupVars') =
  collectExp ((I.Null, I.id), I.Null, (v'_, I.id), k_, DupVars, false, d) in
((if flag
  then
    begin collectSub
            (Gss, Gl, s, (I.Decl (k'_, (label, (EV x_)))),
              (I.Decl (DupVars, (AV (x_, d)))), flag, d) end
  else begin
    collectSub
      (Gss, Gl, s, (I.Decl (k'_, (label, (EV x_)))), DupVars, flag, d) end)
  (* inefficient! *)) end
let rec collectEVar
  (Gss, Gl, ((EVar (r, GX, v_, cnstrs) as x_), s), k_, DupVars, flag, d) =
  if !TableParam.strengthen
  then begin collectEVarStr (Gss, Gl, (x_, s), k_, DupVars, flag, d) end
  else begin
    ((if isId s
      then begin collectEVarFap (Gss, Gl, (x_, s), k_, DupVars, flag, d) end
    else begin collectEVarNFap (Gss, Gl, (x_, s), k_, DupVars, flag, d) end)
  (* equalCtx (compose'(Gl, G), s, GX, s)  *)(* X is fully applied *)
  (* X is not fully applied *)) end
let rec collectDec (Gss, (Dec (_, v_), s), (k_, DupVars), d, flag) =
  let (k'_, DupVars') =
    collectExp (Gss, I.Null, (v_, s), k_, DupVars, flag, d) in
  (((k'_, DupVars'))
    (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*))
let rec collectSub =
  begin function
  | (Gss, Gl, Shift _, k_, DupVars, flag, d) -> (k_, DupVars)
  | (Gss, Gl, Dot (Idx _, s), k_, DupVars, flag, d) ->
      collectSub (Gss, Gl, s, k_, DupVars, flag, d)
  | (Gss, Gl, Dot (Exp (EVar ({ contents = Some (u_) }, _, _, _) as x_), s),
     k_, DupVars, flag, d) ->
      let u'_ = Whnf.normalize (u_, I.id) in
      let (k'_, DupVars') =
        collectExp (Gss, Gl, (u'_, I.id), k_, DupVars, flag, d) in
      ((collectSub (Gss, Gl, s, k'_, DupVars', flag, d))
        (* inefficient? *))
  | (Gss, Gl, Dot (Exp (AVar { contents = Some (u'_) } as u_), s), k_,
     DupVars, flag, d) ->
      let (k'_, DupVars') =
        collectExp (Gss, Gl, (u'_, I.id), k_, DupVars, flag, d) in
      collectSub (Gss, Gl, s, k'_, DupVars', flag, d)
  | (Gss, Gl, Dot (Exp (EClo (u'_, s')), s), k_, DupVars, flag, d) ->
      let u_ = Whnf.normalize (u'_, s') in
      let (k'_, DupVars') =
        collectExp (Gss, Gl, (u_, I.id), k_, DupVars, flag, d) in
      ((collectSub (Gss, Gl, s, k'_, DupVars', flag, d))
        (* inefficient? *))
  | (Gss, Gl, Dot (Exp (u_), s), k_, DupVars, flag, d) ->
      let (k'_, DupVars') =
        collectExp (Gss, Gl, (u_, I.id), k_, DupVars, flag, d) in
      collectSub (Gss, Gl, s, k'_, DupVars', flag, d)
  | (Gss, Gl, Dot (I.Undef, s), k_, DupVars, flag, d) ->
      collectSub (Gss, Gl, s, k_, DupVars, flag, d) end
let rec collectCtx =
  begin function
  | (Gss, DProg (I.Null, I.Null), (k_, DupVars), d) -> (k_, DupVars)
  | (Gss, DProg (Decl (g_, d_), Decl (dPool, C.Parameter)), (k_, DupVars), d)
      ->
      let (k'_, DupVars') =
        collectCtx (Gss, (C.DProg (g_, dPool)), (k_, DupVars), (d - 1)) in
      collectDec (Gss, (d_, I.id), (k'_, DupVars'), (d - 1), false)
  | (Gss, DProg (Decl (g_, d_), Decl (dPool, Dec (r, s, Ha))), (k_, DupVars),
     d) ->
      let (k'_, DupVars') =
        collectCtx (Gss, (C.DProg (g_, dPool)), (k_, DupVars), (d - 1)) in
      collectDec (Gss, (d_, I.id), (k'_, DupVars'), (d - 1), false) end
let rec abstractExpW =
  begin function
  | (flag, gs_, posEA, Vars, Gl, total, depth, ((Uni (l_) as u_), s), eqn) ->
      (posEA, Vars, u_, eqn)
  | (flag, gs_, posEA, Vars, Gl, total, depth, (Pi ((d_, p_), v_), s), eqn)
      ->
      let (posEA', Vars', d_, _) =
        abstractDec (gs_, posEA, Vars, Gl, total, depth, (d_, s), None) in
      let (posEA'', Vars'', v'_, eqn2) =
        abstractExp
          (flag, gs_, posEA', Vars', Gl, total, (depth + 1),
            (v_, (I.dot1 s)), eqn) in
      (posEA'', Vars'', (piDepend ((d_, p_), v'_)), eqn2)
  | (flag, gs_, posEA, Vars, Gl, total, depth, (Root (h_, s_), s), eqn) ->
      let (posEA', Vars', s_, eqn') =
        abstractSpine
          (flag, gs_, posEA, Vars, Gl, total, depth, (s_, s), eqn) in
      (posEA', Vars', (I.Root (h_, s_)), eqn')
  | (flag, gs_, posEA, Vars, Gl, total, depth, (Lam (d_, u_), s), eqn) ->
      let (posEA', Vars', d'_, _) =
        abstractDec (gs_, posEA, Vars, Gl, total, depth, (d_, s), None) in
      let (posEA'', Vars'', u'_, eqn2) =
        abstractExp
          (flag, gs_, posEA', Vars', (I.Decl (Gl, d'_)), total, (depth + 1),
            (u_, (I.dot1 s)), eqn) in
      (posEA'', Vars'', (I.Lam (d'_, u'_)), eqn2)
  | (flag, ((Gss, ss) as gs_), ((epos, apos) as posEA), Vars, Gl, total,
     depth, ((EVar (_, GX, VX, _) as x_), s), eqn) ->
      ((if isId (I.comp (ss, s))
        then
          begin abstractEVarFap
                  (flag, gs_, posEA, Vars, Gl, total, depth, (x_, s), eqn) end
      else begin
        abstractEVarNFap
          (flag, gs_, posEA, Vars, Gl, total, depth, (x_, s), eqn) end)
  (* X is fully applied *)(* s =/= id, i.e. X is not fully applied *)) end
(* X is possibly strengthened ! *)
let rec abstractExp (flag, gs_, posEA, Vars, Gl, total, depth, us_, eqn) =
  abstractExpW
    (flag, gs_, posEA, Vars, Gl, total, depth, (Whnf.whnf us_), eqn)
let rec abstractEVarFap
  (flag, gs_, ((epos, apos) as posEA), Vars, Gl, total, depth, (x_, s), eqn)
  =
  ((begin match member (eqEVar x_) Vars with
    | Some (label, i) ->
        ((if flag
          then
            begin (begin match label with
                   | Body ->
                       let BV = I.BVar (apos + depth) in
                       let BV' = I.BVar (i + depth) in
                       let BV1 = I.BVar (apos + depth) in
                       let (posEA', Vars', s_, eqn1) =
                         abstractSub
                           (flag, gs_, (epos, (apos - 1)), Vars, Gl, total,
                             depth, s, I.Nil, eqn) in
                       (posEA', Vars', (I.Root (BV, I.Nil)),
                         (TableParam.Unify
                            (Gl, (I.Root (BV', s_)), (I.Root (BV1, I.Nil)),
                              eqn1)))
                   | TypeLabel ->
                       let Vars' = update (eqEVar x_) Vars in
                       let (posEA', Vars'', s_, eqn1) =
                         abstractSub
                           (flag, gs_, (epos, apos), Vars', Gl, total, depth,
                             s, I.Nil, eqn) in
                       (posEA', Vars'', (I.Root ((I.BVar (i + depth)), s_)),
                         eqn1) end) end
    else begin
      (let (posEA', Vars', s_, eqn1) =
         abstractSub
           (flag, gs_, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn) in
       (posEA', Vars', (I.Root ((I.BVar (i + depth)), s_)), eqn1)) end)
  (* enforce linearization *)(* do not enforce linearization -- used for type labels *))
| None -> let label = if flag then begin Body end else begin TypeLabel end in
let BV = I.BVar (epos + depth) in
let pos = ((epos - 1), apos) in
let (posEA', Vars', s_, eqn1) =
abstractSub
  (flag, gs_, pos, (I.Decl (Vars, ((label, epos), (EV x_)))), Gl, total,
    depth, s, I.Nil, eqn) in
(posEA', Vars', (I.Root (BV, s_)), eqn1) end)
(* we have seen X before *)(* we see X for the first time *))
let rec abstractEVarNFap
  (flag, gs_, ((epos, apos) as posEA), Vars, Gl, total, depth, (x_, s), eqn)
  =
  ((begin match member (eqEVar x_) Vars with
    | Some (label, i) ->
        ((if flag
          then
            begin let BV = I.BVar (apos + depth) in
                  let BV' = I.BVar (i + depth) in
                  let BV1 = I.BVar (apos + depth) in
                  let (posEA', Vars', s_, eqn1) =
                    abstractSub
                      (flag, gs_, (epos, (apos - 1)), Vars, Gl, total, depth,
                        s, I.Nil, eqn) in
                  (posEA', Vars', (I.Root (BV, I.Nil)),
                    (TableParam.Unify
                       (Gl, (I.Root (BV', s_)), (I.Root (BV1, I.Nil)), eqn1))) end
        else begin
          (let (posEA', Vars', s_, eqn1) =
             abstractSub
               (flag, gs_, (epos, apos), Vars, Gl, total, depth, s, I.Nil,
                 eqn) in
           (posEA', Vars', (I.Root ((I.BVar (i + depth)), s_)), eqn1)) end)
  (* enforce linearization *)(* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
  (* do not enforce linearization -- used for type labels *))
  | None ->
      ((if flag
        then
          begin let label = if flag then begin Body end
                  else begin TypeLabel end in
      let BV = I.BVar (apos + depth) in
      let BV' = I.BVar (epos + depth) in
      let BV1 = I.BVar (apos + depth) in
      let (posEA', Vars', s_, eqn1) =
        abstractSub
          (flag, gs_, ((epos - 1), (apos - 1)),
            (I.Decl (Vars, ((label, epos), (EV x_)))), Gl, total, depth, s,
            I.Nil, eqn) in
      (posEA', Vars', (I.Root (BV, I.Nil)),
        (TableParam.Unify
           (Gl, (I.Root (BV', s_)), (I.Root (BV1, I.Nil)), eqn1))) end
else begin
  (let (posEA', Vars', s_, eqn1) =
     abstractSub
       (flag, gs_, ((epos - 1), apos),
         (I.Decl (Vars, ((TypeLabel, epos), (EV x_)))), Gl, total, depth, s,
         I.Nil, eqn) in
   (posEA', Vars', (I.Root ((I.BVar (epos + depth)), s_)), eqn1)) end)
(* enforce linearization since X is not fully applied *)
(* do not enforce linearization -- used for type labels *)) end)
(* we have seen X before *)(* we have not seen X before *))
let rec abstractSub =
  begin function
  | (flag, gs_, posEA, Vars, Gl, total, depth, Shift k, s_, eqn) ->
      ((if k < depth
        then
          begin abstractSub
                  (flag, gs_, posEA, Vars, Gl, total, depth,
                    (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), s_, eqn) end
      else begin (posEA, Vars, s_, eqn) end)
  (* k = depth *))
  | (flag, gs_, posEA, Vars, Gl, total, depth, Dot (Idx k, s), s_, eqn) ->
      abstractSub
        (flag, gs_, posEA, Vars, Gl, total, depth, s,
          (I.App ((I.Root ((I.BVar k), I.Nil)), s_)), eqn)
  | (flag, gs_, posEA, Vars, Gl, total, depth, Dot (Exp (u_), s), s_, eqn) ->
      let (posEA', Vars', u'_, eqn') =
        abstractExp
          (flag, gs_, posEA, Vars, Gl, total, depth, (u_, I.id), eqn) in
      abstractSub
        (flag, gs_, posEA', Vars', Gl, total, depth, s, (I.App (u'_, s_)),
          eqn') end
let rec abstractSpine =
  begin function
  | (flag, gs_, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn) ->
      (posEA, Vars, I.Nil, eqn)
  | (flag, gs_, posEA, Vars, Gl, total, depth, (SClo (s_, s'), s), eqn) ->
      abstractSpine
        (flag, gs_, posEA, Vars, Gl, total, depth, (s_, (I.comp (s', s))),
          eqn)
  | (flag, gs_, posEA, Vars, Gl, total, depth, (App (u_, s_), s), eqn) ->
      let (posEA', Vars', u'_, eqn') =
        abstractExp (flag, gs_, posEA, Vars, Gl, total, depth, (u_, s), eqn) in
      let (posEA'', Vars'', s'_, eqn'') =
        abstractSpine
          (flag, gs_, posEA', Vars', Gl, total, depth, (s_, s), eqn') in
      (posEA'', Vars'', (I.App (u'_, s'_)), eqn'') end
let rec abstractSub' =
  begin function
  | (flag, gs_, epos, Vars, total, Shift k) ->
      if k < 0 then begin raise (Error "Substitution out of range\n") end
      else begin (epos, Vars, (I.Shift (k + total))) end
  | (flag, gs_, epos, Vars, total, Dot (Idx k, s)) ->
      let (epos', Vars', s') = abstractSub' (flag, gs_, epos, Vars, total, s) in
      (epos', Vars', (I.Dot ((I.Idx k), s')))
  | (flag, gs_, epos, Vars, total, Dot (Exp (u_), s)) ->
      let ((ep, _), Vars', u'_, _) =
        abstractExp
          (false, gs_, (epos, 0), Vars, I.Null, total, 0, (u_, I.id),
            TableParam.Trivial) in
      let (epos'', Vars'', s') =
        abstractSub' (flag, gs_, ep, Vars', total, s) in
      (epos'', Vars'', (I.Dot ((I.Exp u'_), s'))) end
let rec abstractDec =
  begin function
  | (gs_, posEA, Vars, Gl, total, depth, (Dec (x, v_), s), None) ->
      let (posEA', Vars', v'_, eqn) =
        abstractExp
          (false, gs_, posEA, Vars, Gl, total, depth, (v_, s),
            TableParam.Trivial) in
      (((posEA', Vars', (I.Dec (x, v'_)), eqn))
        (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*))
  | (gs_, posEA, Vars, Gl, total, depth, (Dec (x, v_), s), Some eqn) ->
      let (posEA', Vars', v'_, eqn') =
        abstractExp (true, gs_, posEA, Vars, Gl, total, depth, (v_, s), eqn) in
      (((posEA', Vars', (I.Dec (x, v'_)), eqn'))
        (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)) end
let rec abstractCtx' =
  begin function
  | (gs_, epos, Vars, total, depth, DProg (I.Null, I.Null), g'_, eqn) ->
      (epos, Vars, g'_, eqn)
  | (gs_, epos, Vars, total, depth, DProg
     (Decl (g_, d_), Decl (dPool, C.Parameter)), g'_, eqn) ->
      let d = IntSyn.ctxLength g_ in
      let ((epos', _), Vars', d'_, _) =
        abstractDec
          (gs_, (epos, total), Vars, I.Null, total, (depth - 1), (d_, I.id),
            None) in
      abstractCtx'
        (gs_, epos', Vars', total, (depth - 1), (C.DProg (g_, dPool)),
          (I.Decl (g'_, d'_)), eqn)
  | (gs_, epos, Vars, total, depth, DProg (Decl (g_, d_), Decl (dPool, _)),
     g'_, eqn) ->
      let d = IntSyn.ctxLength g_ in
      let ((epos', _), Vars', d'_, _) =
        abstractDec
          (gs_, (epos, total), Vars, I.Null, total, (depth - 1), (d_, I.id),
            None) in
      abstractCtx'
        (gs_, epos', Vars', total, (depth - 1), (C.DProg (g_, dPool)),
          (I.Decl (g'_, d'_)), eqn) end
let rec abstractCtx (gs_, epos, Vars, total, depth, dProg) =
  abstractCtx'
    (gs_, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)
let rec makeEVarCtx =
  begin function
  | (gs_, Vars, DEVars, I.Null, total) -> DEVars
  | (gs_, Vars, DEVars, Decl (k'_, (_, EV (EVar (_, GX, VX, _) as e_))),
     total) ->
      let v'_ = raiseType (GX, VX) in
      let (_, Vars', V'', _) =
        abstractExp
          (false, gs_, (0, 0), Vars, I.Null, 0, (total - 1), (v'_, I.id),
            TableParam.Trivial) in
      let DEVars' = makeEVarCtx (gs_, Vars', DEVars, k'_, (total - 1)) in
      let DEVars'' = I.Decl (DEVars', (I.Dec (None, V''))) in DEVars'' end
let rec makeAVarCtx (Vars, DupVars) =
  let rec avarCtx =
    begin function
    | (Vars, I.Null, k) -> I.Null
    | (Vars, Decl
       (k'_, AV ((EVar ({ contents = None }, GX, VX, _) as e_), d)), k) ->
        I.Decl
          ((avarCtx (Vars, k'_, (k + 1))),
            (I.ADec
               ((Some
                   ((^) (((^) "AVar " Int.toString k) ^ "--") Int.toString d)),
                 d)))
    | (Vars, Decl (k'_, AV ((EVar (_, GX, VX, _) as e_), d)), k) ->
        I.Decl
          ((avarCtx (Vars, k'_, (k + 1))),
            (I.ADec
               ((Some
                   ((^) (((^) "AVar " Int.toString k) ^ "--") Int.toString d)),
                 d))) end in
avarCtx (Vars, DupVars, 0)
let rec lowerEVar' =
  begin function
  | (x_, g_, (Pi ((d'_, _), v'_), s')) ->
      let D'' = I.decSub (d'_, s') in
      let (x'_, u_) =
        lowerEVar' (x_, (I.Decl (g_, D'')), (Whnf.whnf (v'_, (I.dot1 s')))) in
      (x'_, (I.Lam (D'', u_)))
  | (x_, g_, vs'_) -> let x'_ = x_ in (x'_, x'_) end
let rec lowerEVar1 =
  begin function
  | (x_, EVar (r, g_, _, _), ((Pi _ as v_), s)) ->
      let (x'_, u_) = lowerEVar' (x_, g_, (v_, s)) in
      I.EVar ((ref (Some u_)), I.Null, v_, (ref []))
  | (_, x_, _) -> x_ end
let rec lowerEVar =
  begin function
  | (e_, (EVar (r, g_, v_, { contents = [] }) as x_)) ->
      lowerEVar1 (e_, x_, (Whnf.whnf (v_, I.id)))
  | (e_, EVar _) ->
      raise
        (Error
           "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified") end
(* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
(* It is not clear if this case can happen *)
let rec evarsToSub =
  begin function
  | (I.Null, s) -> s
  | (Decl
     (k'_, (_, EV (EVar (({ contents = None } as i_), GX, VX, cnstr) as e_))),
     s) ->
      let v'_ = raiseType (GX, VX) in
      let x_ =
        lowerEVar1
          (e_, (I.EVar (i_, I.Null, v'_, cnstr)), (Whnf.whnf (v'_, I.id))) in
      let s' = evarsToSub (k'_, s) in ((I.Dot ((I.Exp x_), s'))
        (* redundant ? *)) end
let rec avarsToSub =
  begin function
  | (I.Null, s) -> s
  | (Decl (Vars', AV ((EVar (i_, GX, VX, cnstr) as e_), d)), s) ->
      let s' = avarsToSub (Vars', s) in
      let AVar r as x'_ = I.newAVar () in
      I.Dot ((I.Exp (I.EClo (x'_, (I.Shift (- d))))), s') end
let rec abstractEVarCtx ((DProg (g_, dPool) as dp), p, s) =
  let (gs_, ss, d) =
    if !TableParam.strengthen
    then
      begin let w' = Subordinate.weaken (g_, (I.targetFam p)) in
            let iw = Whnf.invert w' in
            let g'_ = Whnf.strengthen (iw, g_) in
            let d' = I.ctxLength g'_ in (g'_, iw, d') end
    else begin (g_, I.id, (I.ctxLength g_)) end in
let (k_, DupVars) = collectCtx ((gs_, ss), dp, (I.Null, I.Null), d) in
let (k'_, DupVars') =
  collectExp ((gs_, ss), I.Null, (p, s), k_, DupVars, true, d) in
let epos = I.ctxLength k'_ in
let apos = I.ctxLength DupVars' in
let total = epos + apos in
let (epos', Vars', g'_, eqn) =
  abstractCtx ((gs_, ss), epos, I.Null, total, d, dp) in
let (((posEA'', Vars'', u'_, eqn'))(* = 0 *)) =
  abstractExp
    (true, (gs_, ss), (epos', total), Vars', I.Null, total, d, (p, s), eqn) in
let DAVars = makeAVarCtx (Vars'', DupVars') in
let DEVars =
  makeEVarCtx ((((gs_, ss), Vars'', I.Null, Vars'', 0))
    (* depth *)) in
let s' = avarsToSub (DupVars', I.id) in
let s'' = evarsToSub (Vars'', s') in
let G'' = reverseCtx (g'_, I.Null) in
((if !TableParam.strengthen
  then
    begin let w' = Subordinate.weaken (G'', (I.targetFam u'_)) in
          let iw = Whnf.invert w' in
          let gs'_ = Whnf.strengthen (iw, G'') in
          (gs'_, DAVars, DEVars, u'_, eqn', s'') end
  else begin (G'', DAVars, DEVars, u'_, eqn', s'') end)
  (* K ||- G i.e. K contains all EVars in G *)(* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
  (* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
  (* abstract over existential variables in p[s] and linearize the expression *)
  (* note: depth will become negative during makeEVarCtx *))
let abstractEVarCtx = abstractEVarCtx
let abstractAnswSub =
  begin function
  | s ->
      let (k_, _) =
        collectSub ((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0) in
      let epos = I.ctxLength k_ in
      let (((_, Vars, s'))(*0 *)) =
        abstractSub' (((false, (I.Null, I.id), epos, I.Null, epos, s))
          (* total *)) in
      let DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars, 0) in
      let s1' = ctxToEVarSub (DEVars, I.id) in (((DEVars, s'))
        (* no linearization for answer substitution *)) end
let raiseType = begin function | (g_, u_) -> raiseType (g_, u_) end end
