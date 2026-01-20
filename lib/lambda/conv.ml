
module type CONV  =
  sig
    val conv : IntSyn.eclo -> IntSyn.eclo -> bool
    val convDec :
      (IntSyn.__Dec * IntSyn.__Sub) -> (IntSyn.__Dec * IntSyn.__Sub) -> bool
    val convSub : IntSyn.__Sub -> IntSyn.__Sub -> bool
  end;;




module Conv(Conv:sig module Whnf : WHNF end) : CONV =
  struct
    open IntSyn
    let rec eqUni __0__ __1__ =
      match (__0__, __1__) with
      | (Type, Type) -> true__
      | (Kind, Kind) -> true__
      | _ -> false__
    let rec convExpW __2__ __3__ =
      match (__2__, __3__) with
      | ((Uni (__L1), _), (Uni (__L2), _)) -> eqUni (__L1, __L2)
      | (((Root (__H1, __S1), s1) as Us1), ((Root (__H2, __S2), s2) as Us2))
          ->
          (((match (__H1, __H2) with
             | (BVar k1, BVar k2) ->
                 (k1 = k2) && (convSpine ((__S1, s1), (__S2, s2)))
             | (Const c1, Const c2) ->
                 (c1 = c2) && (convSpine ((__S1, s1), (__S2, s2)))
             | (Skonst c1, Skonst c2) ->
                 (c1 = c2) && (convSpine ((__S1, s1), (__S2, s2)))
             | (Proj (Bidx v1, i1), Proj (Bidx v2, i2)) ->
                 (v1 = v2) &&
                   ((i1 = i2) && (convSpine ((__S1, s1), (__S2, s2))))
             | (FVar (n1, _, s1'), FVar (n2, _, s2')) ->
                 (n1 = n2) && (convSpine ((__S1, s1), (__S2, s2)))
             | (FgnConst (cs1, cD1), FgnConst (cs2, cD2)) ->
                 (cs1 = cs2) &&
                   (((=) (conDecName cD1) conDecName cD2) &&
                      (convSpine ((__S1, s1), (__S2, s2))))
             | (Def d1, Def d2) ->
                 ((d1 = d2) && (convSpine ((__S1, s1), (__S2, s2)))) ||
                   (convExpW ((Whnf.expandDef __Us1), (Whnf.expandDef __Us2)))
             | (Def d1, _) -> convExpW ((Whnf.expandDef __Us1), __Us2)
             | (_, Def d2) -> convExpW (__Us1, (Whnf.expandDef __Us2))
             | _ -> false__))
          (* s1' = s2' = ^|G| *)(* they must have the same string representation *)
          (* because of strict *))
      | ((Pi (DP1, __V1), s1), (Pi (DP2, __V2), s2)) ->
          (convDecP ((DP1, s1), (DP2, s2))) &&
            (convExp ((__V1, (dot1 s1)), (__V2, (dot1 s2))))
      | (((Pi _, _) as Us1), ((Root (Def _, _), _) as Us2)) ->
          convExpW (__Us1, (Whnf.expandDef __Us2))
      | (((Root (Def _, _), _) as Us1), ((Pi _, _) as Us2)) ->
          convExpW ((Whnf.expandDef __Us1), __Us2)
      | ((Lam (__D1, __U1), s1), (Lam (__D2, __U2), s2)) ->
          convExp ((__U1, (dot1 s1)), (__U2, (dot1 s2)))
      | ((Lam (__D1, __U1), s1), (__U2, s2)) ->
          convExp
            ((__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | ((__U1, s1), (Lam (__D2, __U2), s2)) ->
          convExp
            (((Redex
                 ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
               (dot1 s1)), (__U2, (dot1 s2)))
      | ((FgnExp csfe1, s1), __Us2) ->
          FgnExpStd.EqualTo.apply csfe1 (EClo __Us2)
      | (__Us1, (FgnExp csfe2, s2)) ->
          FgnExpStd.EqualTo.apply csfe2 (EClo __Us1)
      | ((EVar (r1, _, _, _), s1), (EVar (r2, _, _, _), s2)) ->
          (r1 = r2) && (convSub (s1, s2))
      | _ -> false__(* Note that under Head, why is NSDef never used?? *)
      (* ABP -- 2/18/03 Added missing case*)(* s2 = id *)
      (* s1 = id *)(* G |- D1[s1] = D2[s2] by typing invariant *)
      (* order of calls critical to establish convSpine invariant *)
      (* s1 = s2 = id by whnf invariant *)
    let rec convExp (__Us1) (__Us2) =
      convExpW ((Whnf.whnf __Us1), (Whnf.whnf __Us2))
    let rec convSpine __4__ __5__ =
      match (__4__, __5__) with
      | ((Nil, _), (Nil, _)) -> true__
      | ((App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (convExp ((__U1, s1), (__U2, s2))) &&
            (convSpine ((__S1, s1), (__S2, s2)))
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          convSpine ((__S1, (comp (s1', s1))), __Ss2)
      | (__Ss1, (SClo (__S2, s2'), s2)) ->
          convSpine (__Ss1, (__S2, (comp (s2', s2))))
      | (_, _) -> false__
    let rec convSub __6__ __7__ =
      match (__6__, __7__) with
      | (Shift n, Shift m) -> true__
      | (Shift n, (Dot _ as s2)) ->
          convSub ((Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | ((Dot _ as s1), Shift m) ->
          convSub (s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) -> n1 = n2
            | (Exp (__U1), Exp (__U2)) -> convExp ((__U1, id), (__U2, id))
            | (Block (Bidx k1), Block (Bidx k2)) -> k1 = k2
            | (Exp (__U1), Idx n2) ->
                convExp ((__U1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (__U2)) ->
                convExp (((Root ((BVar n1), Nil)), id), (__U2, id))
            | (Undef, Undef) -> true__
            | _ -> false__)
            (* other block cases don't matter -cs 2/18/03 *))
            && (convSub (s1, s2))(* n = m by invariants *)
    let rec convDec __8__ __9__ =
      match (__8__, __9__) with
      | ((Dec (_, __V1), s1), (Dec (_, __V2), s2)) ->
          convExp ((__V1, s1), (__V2, s2))
      | ((BDec (_, (c1, s1)), t1), (BDec (_, (c2, s2)), t2)) ->
          (c1 = c2) && (convSub ((comp (s1, t1)), (comp (s2, t2))))
    let rec convDecP ((__D1, __P1), s1) ((__D2, __P2), s2) =
      convDec ((__D1, s1), (__D2, s2))
    let conv = convExp
    let convDec = convDec
    let convSub = convSub
  end ;;
