module type UNIFY  =
  sig
    type nonrec unifTrail
    val suspend : unit -> unifTrail
    val resume : unifTrail -> unit
    val reset : unit -> unit
    val mark : unit -> unit
    val unwind : unit -> unit
    val instantiateEVar :
      (IntSyn.exp_ option ref * IntSyn.exp_ * IntSyn.cnstr list) -> unit
    val instantiateLVar : (IntSyn.block_ option ref * IntSyn.block_) -> unit
    val resetAwakenCnstrs : unit -> unit
    val nextCnstr : unit -> IntSyn.cnstr option
    val addConstraint : (IntSyn.cnstr list ref * IntSyn.cnstr) -> unit
    val solveConstraint : IntSyn.cnstr -> unit
    val delay : (IntSyn.eclo * IntSyn.cnstr) -> unit
    val intersection : (IntSyn.sub_ * IntSyn.sub_) -> IntSyn.sub_
    exception Unify of string 
    val unify : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val unifyW : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val unifyBlock : (IntSyn.dctx * IntSyn.block_ * IntSyn.block_) -> unit
    val unifySub : (IntSyn.dctx * IntSyn.sub_ * IntSyn.sub_) -> unit
    val invertible :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.sub_ * IntSyn.exp_ option ref) ->
        bool
    val invertSub :
      (IntSyn.dctx * IntSyn.sub_ * IntSyn.sub_ * IntSyn.exp_ option ref) ->
        IntSyn.sub_
    val unifiable : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    val unifiable' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> string option
  end


module Unify(Unify:sig module Whnf : WHNF module Trail : TRAIL end) : UNIFY =
  struct
    exception Unify of string 
    exception NotInvertible 
    open IntSyn
    type action_ =
      | Instantiate of exp_ option ref 
      | InstantiateBlock of block_ option ref 
      | Add of cnstr list ref 
      | Solve of (cnstr * cnstr_) 
    type cAction_ =
      | BindCnstr of (cnstr_ ref * cnstr_) 
    type fAction_ =
      | BindExp of (exp_ option ref * exp_ option) 
      | BindBlock of (block_ option ref * block_ option) 
      | BindAdd of (cnstr list ref * cAction_ list) 
      | FSolve of (cnstr_ ref * cnstr_ * cnstr_) 
    type nonrec unifTrail = fAction_ Trail.trail
    let globalTrail = (Trail.trail () : action_ Trail.trail)
    let rec copyCnstr =
      begin function
      | [] -> []
      | refC::clist -> (::) (BindCnstr (refC, !refC)) copyCnstr clist end
    let rec copy =
      begin function
      | Instantiate refU -> BindExp (refU, !refU)
      | InstantiateBlock refB -> BindBlock (refB, !refB)
      | Add ({ contents = Cnstrs } as cnstrs) ->
          BindAdd (cnstrs, (copyCnstr !cnstrs))
      | Solve (cnstr, Cnstr) -> FSolve (cnstr, Cnstr, !cnstr) end
  let rec resetCnstr =
    begin function
    | [] -> []
    | (BindCnstr (refC, Cnstr))::l_ ->
        (begin refC := Cnstr; refC :: (resetCnstr l_) end) end
let rec reset =
  begin function
  | BindExp (refU, u_) -> (begin refU := u_; Instantiate refU end)
  | BindBlock (refB, b_) -> (begin refB := b_; InstantiateBlock refB end)
  | BindAdd (cnstrs, CActions) ->
      (begin (:=) cnstrs resetCnstr CActions; Add cnstrs end)
| FSolve (refCnstr, Cnstr, Cnstr') ->
    (begin refCnstr := Cnstr'; Solve (refCnstr, Cnstr) end) end
let rec suspend () = Trail.suspend (globalTrail, copy)
let rec resume trail = Trail.resume (trail, globalTrail, reset)
let rec undo =
  begin function
  | Instantiate refU -> refU := None
  | InstantiateBlock refB -> refB := None
  | Add ({ contents = cnstr::cnstrL } as cnstrs) -> cnstrs := cnstrL
  | Solve (cnstr, Cnstr) -> cnstr := Cnstr end
let rec reset () = Trail.reset globalTrail
let rec mark () = Trail.mark globalTrail
let rec unwind () = Trail.unwind (globalTrail, undo)
let rec addConstraint (cnstrs, cnstr) =
  begin (cnstrs := cnstr) :: !cnstrs; Trail.log (globalTrail, (Add cnstrs)) end
let rec solveConstraint ({ contents = Cnstr } as cnstr) =
  begin cnstr := Solved; Trail.log (globalTrail, (Solve (cnstr, Cnstr))) end
let rec delayExpW =
  begin function
  | (((Uni (l_) as u_), s1), _) -> ()
  | ((Pi ((d_, p_), u_), s), cnstr) ->
      (begin delayDec ((d_, s), cnstr); delayExp ((u_, (dot1 s)), cnstr) end)
  | ((Root (h_, s_), s), cnstr) ->
      (begin delayHead (h_, cnstr); delaySpine ((s_, s), cnstr) end)
  | ((Lam (d_, u_), s), cnstr) ->
      (begin delayDec ((d_, s), cnstr); delayExp ((u_, (dot1 s)), cnstr) end)
| ((EVar (g_, r, v_, cnstrs), s), cnstr) -> addConstraint (cnstrs, cnstr)
| ((FgnExp csfe, s), cnstr) ->
    FgnExpStd.App.apply csfe
      (begin function | u_ -> delayExp ((u_, s), cnstr) end) end(* s = id *)
let rec delayExp (us_, cnstr) = delayExpW ((Whnf.whnf us_), cnstr)
let rec delayHead =
  begin function
  | (FVar (x, v_, s'), cnstr) -> delayExp ((v_, id), cnstr)
  | (h_, _) -> () end
let rec delaySpine =
  begin function
  | ((Nil, s), cnstr) -> ()
  | ((App (u_, s_), s), cnstr) ->
      (begin delayExp ((u_, s), cnstr); delaySpine ((s_, s), cnstr) end)
  | ((SClo (s_, s'), s), cnstr) -> delaySpine ((s_, (comp (s', s))), cnstr) end
let rec delayDec ((Dec (name, v_), s), cnstr) = delayExp ((v_, s), cnstr)
let awakenCnstrs = (ref [] : cnstr list ref)
let rec resetAwakenCnstrs () = awakenCnstrs := []
let rec nextCnstr () =
  begin match !awakenCnstrs with
  | [] -> None
  | cnstr::cnstrL -> (begin awakenCnstrs := cnstrL; Some cnstr end) end
let rec instantiateEVar (refU, v_, cnstrL) =
  begin (:=) refU Some v_;
  Trail.log (globalTrail, (Instantiate refU));
  (!) ((@) (awakenCnstrs := cnstrL)) awakenCnstrs end
let rec instantiateLVar (refB, b_) =
  begin (:=) refB Some b_; Trail.log (globalTrail, (InstantiateBlock refB)) end
let rec intersection =
  begin function
  | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
      if k1 = k2 then begin dot1 (intersection (s1, s2)) end
      else begin comp ((intersection (s1, s2)), shift) end
  | ((Dot _ as s1), Shift n2) ->
      intersection (s1, (Dot ((Idx (n2 + 1)), (Shift (n2 + 1)))))
  | (Shift n1, (Dot _ as s2)) ->
      intersection ((Dot ((Idx (n1 + 1)), (Shift (n1 + 1)))), s2)
  | (Shift _, Shift _) -> id end
let rec weakenSub =
  begin function
  | (g_, Shift n, ss) ->
      if (<) n ctxLength g_
      then begin weakenSub (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss) end
      else begin id end
  | (g_, Dot (Idx n, s'), ss) ->
      (begin match bvarSub (n, ss) with
       | Undef -> comp ((weakenSub (g_, s', ss)), shift)
       | Idx _ -> dot1 (weakenSub (g_, s', ss)) end)
| (g_, Dot (Undef, s'), ss) -> comp ((weakenSub (g_, s', ss)), shift) end
(* no other cases, ss is strsub *)
let rec invertExp (g_, us_, ss, rOccur) =
  invertExpW (g_, (Whnf.whnf us_), ss, rOccur)
let rec invertExpW =
  begin function
  | (g_, ((Uni _ as u_), s), _, _) -> u_
  | (g_, (Pi ((d_, p_), v_), s), ss, rOccur) ->
      Pi
        (((invertDec (g_, (d_, s), ss, rOccur)), p_),
          (invertExp
             ((Decl (g_, (decSub (d_, s)))), (v_, (dot1 s)), (dot1 ss),
               rOccur)))
  | (g_, (Lam (d_, v_), s), ss, rOccur) ->
      Lam
        ((invertDec (g_, (d_, s), ss, rOccur)),
          (invertExp
             ((Decl (g_, (decSub (d_, s)))), (v_, (dot1 s)), (dot1 ss),
               rOccur)))
  | (g_, (((Root (h_, s_), s))(* = id *)), ss, rOccur) ->
      Root
        ((invertHead (g_, h_, ss, rOccur)),
          (invertSpine (g_, (s_, s), ss, rOccur)))
  | (g_, ((EVar (r, GX, v_, cnstrs) as x_), s), ss, rOccur) ->
      if rOccur = r then begin raise NotInvertible end
      else begin
        ((if Whnf.isPatSub s
          then
            begin (let w = weakenSub (g_, s, ss) in
                   if Whnf.isId w then begin EClo (x_, (comp (s, ss))) end
                     else begin raise NotInvertible end) end
  else begin EClo (x_, (invertSub (g_, s, ss, rOccur))) end)
  (* s not patsub *)(* invertExp may raise NotInvertible *)) end
| (g_, (FgnExp csfe, s), ss, rOccur) ->
    FgnExpStd.Map.apply csfe
      (begin function | u_ -> invertExp (g_, (u_, s), ss, rOccur) end) end
let rec invertDec (g_, (Dec (name, v_), s), ss, rOccur) =
  Dec (name, (invertExp (g_, (v_, s), ss, rOccur)))
let rec invertSpine =
  begin function
  | (g_, (Nil, s), ss, rOccur) -> Nil
  | (g_, (App (u_, s_), s), ss, rOccur) ->
      App
        ((invertExp (g_, (u_, s), ss, rOccur)),
          (invertSpine (g_, (s_, s), ss, rOccur)))
  | (g_, (SClo (s_, s'), s), ss, rOccur) ->
      invertSpine (g_, (s_, (comp (s', s))), ss, rOccur) end
let rec invertHead =
  begin function
  | (g_, BVar k, ss, rOccur) ->
      (begin match bvarSub (k, ss) with
       | Undef -> raise NotInvertible
       | Idx k' -> BVar k' end)
  | (g_, (Const _ as h_), ss, rOccur) -> h_
  | (g_, Proj ((Bidx k as b_), i), ss, rOccur) ->
      (begin match blockSub (b_, ss) with | Bidx k' -> Proj ((Bidx k'), i) end)
  | (g_, (Proj (LVar (r, sk, (l, t)), i) as h_), ss, rOccur) ->
      (begin invertSub (g_, t, id, rOccur); h_ end)
| (g_, (Skonst _ as h_), ss, rOccur) -> h_
| (g_, (Def _ as h_), ss, rOccur) -> h_
| (g_, FVar (x, v_, s'), ss, rOccur) ->
    (((begin invertExp (g_, (v_, id), id, rOccur);
       FVar (x, v_, (comp (s', ss))) end))
(* why G here? -fp !!! *))
| (g_, (FgnConst _ as h_), ss, rOccur) -> h_ end(* perform occurs-check for r only *)
(* V does not to be pruned, since . |- V : type and s' = ^k *)(* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)(* Sat Dec  8 13:39:41 2001 -fp !!! *)
(* so we perform only the occurs-check here as for FVars *)
(* claim: LVar does not need to be pruned since . |- t : Gsome *)
(* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
let rec invertSub =
  begin function
  | (g_, (Shift n as s), ss, rOccur) ->
      if (<) n ctxLength g_
      then
        begin invertSub
                (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur) end
      else begin comp (s, ss) end
  | (g_, Dot (Idx n, s'), ss, rOccur) ->
      (begin match bvarSub (n, ss) with
       | Undef -> raise NotInvertible
       | Ft -> Dot (Ft, (invertSub (g_, s', ss, rOccur))) end)
| (g_, Dot (Exp (u_), s'), ss, rOccur) ->
    Dot
      ((Exp (invertExp (g_, (u_, id), ss, rOccur))),
        (invertSub (g_, s', ss, rOccur))) end(* below my raise NotInvertible *)
(* must be defined *)
let rec pruneExp (g_, us_, ss, rOccur) =
  pruneExpW (g_, (Whnf.whnf us_), ss, rOccur)
let rec pruneExpW =
  begin function
  | (g_, ((Uni _ as u_), s), _, _) -> u_
  | (g_, (Pi ((d_, p_), v_), s), ss, rOccur) ->
      Pi
        (((pruneDec (g_, (d_, s), ss, rOccur)), p_),
          (pruneExp
             ((Decl (g_, (decSub (d_, s)))), (v_, (dot1 s)), (dot1 ss),
               rOccur)))
  | (g_, (Lam (d_, v_), s), ss, rOccur) ->
      Lam
        ((pruneDec (g_, (d_, s), ss, rOccur)),
          (pruneExp
             ((Decl (g_, (decSub (d_, s)))), (v_, (dot1 s)), (dot1 ss),
               rOccur)))
  | (g_, (((Root (h_, s_), s))(* = id *)), ss, rOccur) ->
      Root
        ((pruneHead (g_, h_, ss, rOccur)),
          (pruneSpine (g_, (s_, s), ss, rOccur)))
  | (g_, ((EVar (r, GX, v_, cnstrs) as x_), s), ss, rOccur) ->
      if rOccur = r then begin raise (Unify "Variable occurrence") end
      else begin
        ((if Whnf.isPatSub s
          then
            begin (let w = weakenSub (g_, s, ss) in
                   if Whnf.isId w then begin EClo (x_, (comp (s, ss))) end
                     else begin
                       (let wi = Whnf.invert w in
                        let v'_ = pruneExp (GX, (v_, id), wi, rOccur) in
                        let GY = pruneCtx (wi, GX, rOccur) in
                        let y_ = newEVar (GY, v'_) in
                        let Yw = EClo (y_, w) in
                        let _ = instantiateEVar (r, Yw, !cnstrs) in
                        ((EClo (Yw, (comp (s, ss))))
                          (* val V' = EClo (V, wi) *)
                          (* val GY = Whnf.strengthen (wi, GX) *)
                          (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
                          (* could optimize by checking for identity subst *))) end) end
  else begin
    (begin try EClo (x_, (invertSub (g_, s, ss, rOccur)))
     with
     | NotInvertible ->
         let GY = pruneCtx (ss, g_, rOccur) in
         let v'_ = pruneExp (g_, (v_, s), ss, rOccur) in
         let y_ = newEVar (GY, v'_) in
         let _ =
           addConstraint
             (cnstrs,
               (ref (Eqn (g_, (EClo (x_, s)), (EClo (y_, (Whnf.invert ss))))))) in
         ((y_)
           (* val GY = Whnf.strengthen (ss, G) *)(* shortcuts possible by invariants on G? *)
           (* prune or invert??? *)(* val V' = EClo (V, comp (s, ss)) *)
           (* prune or invert??? *)) end) end)
(* s not patsub *)) end
| (g_, (FgnExp csfe, s), ss, rOccur) ->
    FgnExpStd.Map.apply csfe
      (begin function | u_ -> pruneExp (g_, (u_, s), ss, rOccur) end)
| (g_, ((AVar _ as x_), s), ss, rOccur) -> raise (Unify "Left-over AVar") end
(* this case should never happen! *)
let rec pruneDec =
  begin function
  | (g_, (Dec (name, v_), s), ss, rOccur) ->
      Dec (name, (pruneExp (g_, (v_, s), ss, rOccur)))
  | (g_, (NDec x, _), _, _) -> NDec x end
let rec pruneSpine =
  begin function
  | (g_, (Nil, s), ss, rOccur) -> Nil
  | (g_, (App (u_, s_), s), ss, rOccur) ->
      App
        ((pruneExp (g_, (u_, s), ss, rOccur)),
          (pruneSpine (g_, (s_, s), ss, rOccur)))
  | (g_, (SClo (s_, s'), s), ss, rOccur) ->
      pruneSpine (g_, (s_, (comp (s', s))), ss, rOccur) end
let rec pruneHead =
  begin function
  | (g_, BVar k, ss, rOccur) ->
      (begin match bvarSub (k, ss) with
       | Undef -> raise (Unify "Parameter dependency")
       | Idx k' -> BVar k' end)
  | (g_, (Const _ as h_), ss, rOccur) -> h_
  | (g_, Proj ((Bidx k as b_), i), ss, rOccur) ->
      (begin match blockSub (b_, ss) with | Bidx k' -> Proj ((Bidx k'), i) end)
  | (g_, (Proj (LVar (r, sk, (l, t)), i) as h_), ss, rOccur) ->
      (begin pruneSub (g_, t, id, rOccur); h_ end)
| (g_, (Skonst _ as h_), ss, rOccur) -> h_
| (g_, (Def _ as h_), ss, rOccur) -> h_
| (g_, FVar (x, v_, s'), ss, rOccur) ->
    (((begin pruneExp (g_, (v_, id), id, rOccur);
       FVar (x, v_, (comp (s', ss))) end))
(* why G here? -fp !!! *))
| (g_, (FgnConst _ as h_), ss, rOccur) -> h_ end(* perform occurs-check for r only *)
(* V does not to be pruned, since . |- V : type and s' = ^k *)(* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)(* Sat Dec  8 13:39:41 2001 -fp !!! *)
(* so we perform only the occurs-check here as for FVars *)
(* claim: LVar does not need to be pruned since . |- t : Gsome *)
(* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
let rec pruneSub =
  begin function
  | (g_, (Shift n as s), ss, rOccur) ->
      if (<) n ctxLength g_
      then
        begin pruneSub
                (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur) end
      else begin comp (s, ss) end
  | (g_, Dot (Idx n, s'), ss, rOccur) ->
      (begin match bvarSub (n, ss) with
       | Undef -> raise (Unify "Not prunable")
       | Ft -> Dot (Ft, (pruneSub (g_, s', ss, rOccur))) end)
| (g_, Dot (Exp (u_), s'), ss, rOccur) ->
    Dot
      ((Exp (pruneExp (g_, (u_, id), ss, rOccur))),
        (pruneSub (g_, s', ss, rOccur))) end(* below my raise Unify *)
(* must be defined *)
let rec pruneCtx =
  begin function
  | (Shift n, Null, rOccur) -> Null
  | (Dot (Idx k, t), Decl (g_, d_), rOccur) ->
      let t' = comp (t, invShift) in
      let d'_ = pruneDec (g_, (d_, id), t', rOccur) in
      Decl ((pruneCtx (t', g_, rOccur)), d'_)
  | (Dot (Undef, t), Decl (g_, d), rOccur) -> pruneCtx (t, g_, rOccur)
  | (Shift n, g_, rOccur) ->
      pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), g_, rOccur) end
let rec unifyExpW =
  begin function
  | (g_, ((FgnExp csfe1, _) as us1_), us2_) ->
      (begin match FgnExpStd.UnifyWith.apply csfe1 (g_, (EClo us2_)) with
       | Succeed residualL ->
           let rec execResidual =
             begin function
             | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                 let w'_ = pruneExp (g_, (w_, id), ss, r) in
                 instantiateEVar (r, w'_, !cnstrs)
             | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr) end in
         List.app execResidual residualL
      | Fail -> raise (Unify "Foreign Expression Mismatch") end)
  | (g_, us1_, ((FgnExp csfe2, _) as us2_)) ->
      (begin match FgnExpStd.UnifyWith.apply csfe2 (g_, (EClo us1_)) with
       | Succeed opL ->
           let rec execOp =
             begin function
             | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                 let w'_ = pruneExp (g_, (w_, id), ss, r) in
                 instantiateEVar (r, w'_, !cnstrs)
             | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr) end in
         List.app execOp opL
      | Fail -> raise (Unify "Foreign Expression Mismatch") end)
| (g_, (Uni (l1_), _), (Uni (l2_), _)) -> ()
| (g_, ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_)) ->
    (((begin match (h1_, h2_) with
       | (BVar k1, BVar k2) ->
           if k1 = k2 then begin unifySpine (g_, (s1_, s1), (s2_, s2)) end
           else begin raise (Unify "Bound variable clash") end
| (Const c1, Const c2) ->
    if c1 = c2 then begin unifySpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Unify "Constant clash") end
| (Proj (b1, i1), Proj (b2, i2)) ->
    if i1 = i2
    then
      begin (begin unifyBlock (g_, b1, b2);
             unifySpine (g_, (s1_, s1), (s2_, s2)) end) end
else begin raise (Unify "Global parameter clash") end
| (Skonst c1, Skonst c2) ->
    if c1 = c2 then begin unifySpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Unify "Skolem constant clash") end
| (FVar (n1, _, _), FVar (n2, _, _)) ->
    if n1 = n2 then begin unifySpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Unify "Free variable clash") end
| (Def d1, Def d2) ->
    ((if d1 = d2 then begin unifySpine (g_, (s1_, s1), (s2_, s2)) end
    else begin unifyDefDefW (g_, us1_, us2_) end)
(* because of strict *)(*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *))
| (Def d1, Const c2) ->
    (((begin match defAncestor d1 with
       | Anc (_, _, None) -> unifyExpW (g_, (Whnf.expandDef us1_), us2_)
       | Anc (_, _, Some c1) ->
           if c1 = c2
           then begin unifyExpW (g_, (Whnf.expandDef us1_), us2_) end
           else begin raise (Unify "Constant clash") end end))
(* conservative *))
| (Const c1, Def d2) ->
    (((begin match defAncestor d2 with
       | Anc (_, _, None) -> unifyExpW (g_, us1_, (Whnf.expandDef us2_))
       | Anc (_, _, Some c2) ->
           if c1 = c2
           then begin unifyExpW (g_, us1_, (Whnf.expandDef us2_)) end
           else begin raise (Unify "Constant clash") end end))
(* conservative *))
| (Def d1, BVar k2) -> raise (Unify "Head mismatch")
| (BVar k1, Def d2) -> raise (Unify "Head mismatch")
| (Def d1, _) -> unifyExpW (g_, (Whnf.expandDef us1_), us2_)
| (_, Def d2) -> unifyExpW (g_, us1_, (Whnf.expandDef us2_))
| (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
   (cs2, ConDec (n2, _, _, _, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin () end
    else begin raise (Unify "Foreign Constant clash") end
| (FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)), FgnConst
   (cs2, ConDef (n2, _, _, v_, w2_, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin () end
    else begin unifyExp (g_, (w1_, s1), (w2_, s2)) end
| (FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _) ->
    unifyExp (g_, (w1_, s1), us2_)
| (_, FgnConst (_, ConDef (_, _, _, w2_, _, _, _))) ->
    unifyExp (g_, us1_, (w2_, s2)) | _ -> raise (Unify "Head mismatch") end))
(* four new cases for defined constants *)(* due to strictness! *)
(* due to strictness! *)(* next two cases for def/fgn, fgn/def *)
(* we require unique string representation of external constants *))
| (g_, (Pi ((d1_, _), u1_), s1), (Pi ((d2_, _), u2_), s2)) ->
    (begin unifyDec (g_, (d1_, s1), (d2_, s2));
     unifyExp
       ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2))) end)
| (g_, ((Pi (_, _), _) as us1_), ((Root (Def _, _), _) as us2_)) ->
    unifyExpW (g_, us1_, (Whnf.expandDef us2_))
| (g_, ((Root (Def _, _), _) as us1_), ((Pi (_, _), _) as us2_)) ->
    unifyExpW (g_, (Whnf.expandDef us1_), us2_)
| (g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2)) ->
    unifyExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2)))
| (g_, (Lam (d1_, u1_), s1), (u2_, s2)) ->
    unifyExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)),
        ((Redex ((EClo (u2_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s2)))
| (g_, (u1_, s1), (Lam (d2_, u2_), s2)) ->
    unifyExp
      ((Decl (g_, (decSub (d2_, s2)))),
        ((Redex ((EClo (u1_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s1)), (u2_, (dot1 s2)))
| (g_, (((EVar (r1, g1_, v1_, cnstrs1) as u1_), s1) as us1_),
   (((EVar (r2, g2_, v2_, cnstrs2) as u2_), s2) as us2_)) ->
    if r1 = r2
    then
      begin (if Whnf.isPatSub s1
             then
               begin (if Whnf.isPatSub s2
                      then
                        begin let s' = intersection (s1, s2) in
                              (((if Whnf.isId s' then begin () end
                                else begin
                                  (let ss' = Whnf.invert s' in
                                   let V1' = EClo (v1_, ss') in
                                   let G1' = Whnf.strengthen (ss', g1_) in
                                   ((instantiateEVar
                                       (r1,
                                         (EClo ((newEVar (G1', V1')), s')),
                                         !cnstrs1))
                                     (* invertExp ((V1, id), s', ref NONE) *))) end))
                      (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
                      (* X[s] = X[s] *)(* compute ss' directly? *)
                      (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)) end
      else begin
        addConstraint (cnstrs2, (ref (Eqn (g_, (EClo us2_), (EClo us1_))))) end) end
else begin
  addConstraint (cnstrs1, (ref (Eqn (g_, (EClo us1_), (EClo us2_))))) end) end
else begin
  if Whnf.isPatSub s1
  then
    begin (let ss1 = Whnf.invert s1 in
           let U2' = pruneExp (g_, us2_, ss1, r1) in
           ((instantiateEVar (r1, U2', !cnstrs1))
             (* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
             (* invertExpW (Us2, s1, ref NONE) *))) end
  else begin
    if Whnf.isPatSub s2
    then
      begin (let ss2 = Whnf.invert s2 in
             let U1' = pruneExp (g_, us1_, ss2, r2) in
             ((instantiateEVar (r2, U1', !cnstrs2))
               (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
               (* invertExpW (Us1, s2, ref NONE) *))) end
    else begin
      (let cnstr = ref (Eqn (g_, (EClo us1_), (EClo us2_))) in
       addConstraint (cnstrs1, cnstr)) end end end
| (g_, ((EVar (r, GX, v_, cnstrs), s) as us1_), ((u2_, s2) as us2_)) ->
    if Whnf.isPatSub s
    then
      begin let ss = Whnf.invert s in
            let U2' = pruneExp (g_, us2_, ss, r) in
            ((instantiateEVar (r, U2', !cnstrs))
              (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
              (* invertExpW (Us2, s, r) *)) end
    else begin
      addConstraint (cnstrs, (ref (Eqn (g_, (EClo us1_), (EClo us2_))))) end
| (g_, ((u1_, s1) as us1_), ((EVar (r, GX, v_, cnstrs), s) as us2_)) ->
    if Whnf.isPatSub s
    then
      begin let ss = Whnf.invert s in
            let U1' = pruneExp (g_, us1_, ss, r) in
            ((instantiateEVar (r, U1', !cnstrs))
              (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
              (* invertExpW (Us1, s, r) *)) end
    else begin
      addConstraint (cnstrs, (ref (Eqn (g_, (EClo us1_), (EClo us2_))))) end
| (g_, us1_, us2_) -> raise (Unify "Expression clash") end(* postpone, if s1 or s2 are not patsub *)
(* same reasoning holds as above *)(* Cannot occur if expressions are eta expanded *)
(* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
(* ETA: can't occur if eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
(* order of calls critical to establish unifySpine invariant *)(* s1 = s2 = id by whnf *)
(* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)(* L1 = L2 = type, by invariant *)
let rec unifyExp (g_, ((e1_, s1) as us1_), ((e2_, s2) as us2_)) =
  unifyExpW (g_, (Whnf.whnf us1_), (Whnf.whnf us2_))
let rec unifyDefDefW
  (g_, ((Root (Def d1, s1_), s1) as us1_),
   ((Root (Def d2, s2_), s2) as us2_))
  =
  let Anc (_, h1, c1Opt) = defAncestor d1 in
  let Anc (_, h2, c2Opt) = defAncestor d2 in
  let _ =
    begin match (c1Opt, c2Opt) with
    | (Some c1, Some c2) ->
        if c1 <> c2
        then begin raise (Unify "Irreconcilable defined constant clash") end
        else begin () end
    | _ -> () end in
((begin match Int.compare (h1, h2) with
  | EQUAL -> unifyExpW (g_, (Whnf.expandDef us1_), (Whnf.expandDef us2_))
  | LESS -> unifyExpW (g_, us1_, (Whnf.expandDef us2_))
  | GREATER -> unifyExpW (g_, (Whnf.expandDef us1_), us2_) end)
  (* conservative *))(*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
let rec unifySpine =
  begin function
  | (g_, (Nil, _), (Nil, _)) -> ()
  | (g_, (SClo (s1_, s1'), s1), ss_) ->
      unifySpine (g_, (s1_, (comp (s1', s1))), ss_)
  | (g_, ss_, (SClo (s2_, s2'), s2)) ->
      unifySpine (g_, ss_, (s2_, (comp (s2', s2))))
  | (g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2)) ->
      (begin unifyExp (g_, (u1_, s1), (u2_, s2));
       unifySpine (g_, (s1_, s1), (s2_, s2)) end) end
let rec unifyDec (g_, (Dec (_, v1_), s1), (Dec (_, v2_), s2)) =
  unifyExp (g_, (v1_, s1), (v2_, s2))
let rec unifySub =
  begin function
  | (g_, Shift n1, Shift n2) -> ()
  | (g_, Shift n, (Dot _ as s2)) ->
      unifySub (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
  | (g_, (Dot _ as s1), Shift m) ->
      unifySub (g_, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
  | (g_, Dot (Ft1, s1), Dot (Ft2, s2)) ->
      (((begin (begin match (Ft1, Ft2) with
                | (Idx n1, Idx n2) ->
                    if n1 <> n2
                    then begin raise (Error "SOME variables mismatch") end
                    else begin () end
      | (Exp (u1_), Exp (u2_)) -> unifyExp (g_, (u1_, id), (u2_, id))
      | (Exp (u1_), Idx n2) ->
          unifyExp (g_, (u1_, id), ((Root ((BVar n2), Nil)), id))
      | (Idx n1, Exp (u2_)) ->
          unifyExp (g_, ((Root ((BVar n1), Nil)), id), (u2_, id)) end);
  unifySub (g_, s1, s2) end))
(*         | (Undef, Undef) =>
           | _ => false *)
(* not possible because of invariant? -cs *)) end(* by invariant *)
let rec unifyBlock =
  begin function
  | (g_, LVar ({ contents = Some (b1_) }, s, _), b2_) ->
      unifyBlock (g_, (blockSub (b1_, s)), b2_)
  | (g_, b1_, LVar ({ contents = Some (b2_) }, s, _)) ->
      unifyBlock (g_, b1_, (blockSub (b2_, s)))
  | (g_, b1_, b2_) -> unifyBlockW (g_, b1_, b2_) end
let rec unifyBlockW =
  begin function
  | (g_, LVar (r1, (Shift k1 as s1), (l1, t1)), LVar
     (r2, (Shift k2 as s2), (l2, t2))) ->
      if l1 <> l2 then begin raise (Unify "Label clash") end
      else begin if r1 = r2 then begin () end
        else begin
          (((begin unifySub (g_, (comp (t1, s1)), (comp (t2, s2)));
             if k1 < k2
             then
               begin instantiateLVar
                       (r1, (LVar (r2, (Shift (k2 - k1)), (l2, t2)))) end
             else begin
               instantiateLVar (r2, (LVar (r1, (Shift (k1 - k2)), (l1, t1)))) end end))
  (* Sat Dec  7 22:04:31 2002 -fp *)(* was: unifySub (G, t1, t2)  Jul 22 2010 *)) end end
| (g_, LVar (r1, s1, (l1, t1)), b2_) ->
    instantiateLVar (r1, (blockSub (b2_, (Whnf.invert s1))))
| (g_, b1_, LVar (r2, s2, (l2, t2))) ->
    instantiateLVar (r2, (blockSub (b1_, (Whnf.invert s2))))
| (g_, Bidx n1, Bidx n2) ->
    if n1 <> n2 then begin raise (Unify "Block index clash") end
    else begin () end end(* Sat Dec  8 11:49:16 2001 -fp !!! *)(* How can the next case arise? *)
(* -- ABP *)(*      | unifyBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP *)
(* -- ABP *)(* -- ABP *)
let rec unify1W (g_, us1_, us2_) =
  begin unifyExpW (g_, us1_, us2_); awakeCnstr (nextCnstr ()) end
let rec unify1 (g_, us1_, us2_) =
  begin unifyExp (g_, us1_, us2_); awakeCnstr (nextCnstr ()) end
let rec awakeCnstr =
  begin function
  | None -> ()
  | Some { contents = Solved } -> awakeCnstr (nextCnstr ())
  | Some ({ contents = Eqn (g_, u1_, u2_) } as cnstr) ->
      (begin solveConstraint cnstr; unify1 (g_, (u1_, id), (u2_, id)) end)
  | Some { contents = FgnCnstr csfc } ->
      if FgnCnstrStd.Awake.apply csfc () then begin () end
      else begin raise (Unify "Foreign constraint violated") end end
let rec unifyW (g_, us1_, us2_) =
  begin resetAwakenCnstrs (); unify1W (g_, us1_, us2_) end
let rec unify (g_, us1_, us2_) =
  begin resetAwakenCnstrs (); unify1 (g_, us1_, us2_) end
type nonrec unifTrail = unifTrail
let reset = reset
let mark = mark
let unwind = unwind
let suspend = suspend
let resume = resume
let delay = delayExp
let instantiateEVar = instantiateEVar
let instantiateLVar = instantiateLVar
let resetAwakenCnstrs = resetAwakenCnstrs
let nextCnstr = nextCnstr
let addConstraint = addConstraint
let solveConstraint = solveConstraint
let intersection = intersection
let unifyW = unifyW
let unify = unify
let unifySub = unifySub
let unifyBlock = unifyBlock
let rec invertible (g_, us_, ss, rOccur) =
  begin try begin invertExp (g_, us_, ss, rOccur); true end
  with | NotInvertible -> false end
let invertSub = invertSub
let rec unifiable (g_, us1_, us2_) =
  begin try begin unify (g_, us1_, us2_); true end with | Unify msg -> false end
let rec unifiable' (g_, us1_, us2_) =
  begin try begin unify (g_, us1_, us2_); None end
  with | Unify msg -> Some msg end end
