module type CONV  =
  sig
    val conv : (IntSyn.eclo * IntSyn.eclo) -> bool
    val convDec :
      ((IntSyn.dec_ * IntSyn.sub_) * (IntSyn.dec_ * IntSyn.sub_)) -> bool
    val convSub : (IntSyn.sub_ * IntSyn.sub_) -> bool
  end


module Conv(Conv:sig module Whnf : WHNF end) : CONV =
  struct
    open IntSyn
    let rec eqUni =
      begin function
      | (Type, Type) -> true
      | (Kind, Kind) -> true
      | _ -> false end
    let rec convExpW =
      begin function
      | ((Uni (l1_), _), (Uni (l2_), _)) -> eqUni (l1_, l2_)
      | (((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_)) ->
          (((begin match (h1_, h2_) with
             | (BVar k1, BVar k2) ->
                 (k1 = k2) && (convSpine ((s1_, s1), (s2_, s2)))
             | (Const c1, Const c2) ->
                 (c1 = c2) && (convSpine ((s1_, s1), (s2_, s2)))
             | (Skonst c1, Skonst c2) ->
                 (c1 = c2) && (convSpine ((s1_, s1), (s2_, s2)))
             | (Proj (Bidx v1, i1), Proj (Bidx v2, i2)) ->
                 (v1 = v2) &&
                   ((i1 = i2) && (convSpine ((s1_, s1), (s2_, s2))))
             | (FVar (n1, _, s1'), FVar (n2, _, s2')) ->
                 (n1 = n2) && (convSpine ((s1_, s1), (s2_, s2)))
             | (FgnConst (cs1, cD1), FgnConst (cs2, cD2)) ->
                 (cs1 = cs2) &&
                   (((=) (conDecName cD1) conDecName cD2) &&
                      (convSpine ((s1_, s1), (s2_, s2))))
             | (Def d1, Def d2) ->
                 ((d1 = d2) && (convSpine ((s1_, s1), (s2_, s2)))) ||
                   (convExpW ((Whnf.expandDef us1_), (Whnf.expandDef us2_)))
             | (Def d1, _) -> convExpW ((Whnf.expandDef us1_), us2_)
             | (_, Def d2) -> convExpW (us1_, (Whnf.expandDef us2_))
             | _ -> false end))
      (* s1' = s2' = ^|G| *)(* they must have the same string representation *)
      (* because of strict *))
      | ((Pi (DP1, v1_), s1), (Pi (DP2, v2_), s2)) ->
          (convDecP ((DP1, s1), (DP2, s2))) &&
            (convExp ((v1_, (dot1 s1)), (v2_, (dot1 s2))))
      | (((Pi _, _) as us1_), ((Root (Def _, _), _) as us2_)) ->
          convExpW (us1_, (Whnf.expandDef us2_))
      | (((Root (Def _, _), _) as us1_), ((Pi _, _) as us2_)) ->
          convExpW ((Whnf.expandDef us1_), us2_)
      | ((Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2)) ->
          convExp ((u1_, (dot1 s1)), (u2_, (dot1 s2)))
      | ((Lam (d1_, u1_), s1), (u2_, s2)) ->
          convExp
            ((u1_, (dot1 s1)),
              ((Redex
                  ((EClo (u2_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | ((u1_, s1), (Lam (d2_, u2_), s2)) ->
          convExp
            (((Redex
                 ((EClo (u1_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
               (dot1 s1)), (u2_, (dot1 s2)))
      | ((FgnExp csfe1, s1), us2_) ->
          FgnExpStd.EqualTo.apply csfe1 (EClo us2_)
      | (us1_, (FgnExp csfe2, s2)) ->
          FgnExpStd.EqualTo.apply csfe2 (EClo us1_)
      | ((EVar (r1, _, _, _), s1), (EVar (r2, _, _, _), s2)) ->
          (r1 = r2) && (convSub (s1, s2))
      | _ -> false end(* Note that under Head, why is NSDef never used?? *)
  (* ABP -- 2/18/03 Added missing case*)(* s2 = id *)
  (* s1 = id *)(* G |- D1[s1] = D2[s2] by typing invariant *)
  (* order of calls critical to establish convSpine invariant *)
  (* s1 = s2 = id by whnf invariant *)
let rec convExp (us1_, us2_) = convExpW ((Whnf.whnf us1_), (Whnf.whnf us2_))
let rec convSpine =
  begin function
  | ((Nil, _), (Nil, _)) -> true
  | ((App (u1_, s1_), s1), (App (u2_, s2_), s2)) ->
      (convExp ((u1_, s1), (u2_, s2))) && (convSpine ((s1_, s1), (s2_, s2)))
  | ((SClo (s1_, s1'), s1), ss2_) ->
      convSpine ((s1_, (comp (s1', s1))), ss2_)
  | (ss1_, (SClo (s2_, s2'), s2)) ->
      convSpine (ss1_, (s2_, (comp (s2', s2))))
  | (_, _) -> false end
let rec convSub =
  begin function
  | (Shift n, Shift m) -> true
  | (Shift n, (Dot _ as s2)) ->
      convSub ((Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
  | ((Dot _ as s1), Shift m) ->
      convSub (s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
  | (Dot (Ft1, s1), Dot (Ft2, s2)) ->
      ((begin match (Ft1, Ft2) with
        | (Idx n1, Idx n2) -> n1 = n2
        | (Exp (u1_), Exp (u2_)) -> convExp ((u1_, id), (u2_, id))
        | (Block (Bidx k1), Block (Bidx k2)) -> k1 = k2
        | (Exp (u1_), Idx n2) ->
            convExp ((u1_, id), ((Root ((BVar n2), Nil)), id))
        | (Idx n1, Exp (u2_)) ->
            convExp (((Root ((BVar n1), Nil)), id), (u2_, id))
        | (Undef, Undef) -> true
        | _ -> false end)
      (* other block cases don't matter -cs 2/18/03 *)) &&
      (convSub (s1, s2)) end(* n = m by invariants *)
let rec convDec =
  begin function
  | ((Dec (_, v1_), s1), (Dec (_, v2_), s2)) ->
      convExp ((v1_, s1), (v2_, s2))
  | ((BDec (_, (c1, s1)), t1), (BDec (_, (c2, s2)), t2)) ->
      (c1 = c2) && (convSub ((comp (s1, t1)), (comp (s2, t2)))) end
let rec convDecP (((d1_, p1_), s1), ((d2_, p2_), s2)) =
  convDec ((d1_, s1), (d2_, s2))
let conv = convExp
let convDec = convDec
let convSub = convSub end
