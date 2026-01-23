module type MATCH  =
  sig
    exception Match of string 
    val match_ : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val matchW : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val matchBlock : (IntSyn.dctx * IntSyn.block_ * IntSyn.block_) -> unit
    val matchSub : (IntSyn.dctx * IntSyn.sub_ * IntSyn.sub_) -> unit
    val instance : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    val instance' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> string option
  end


module Match(Match:sig
                     module Whnf : WHNF
                     module Unify : UNIFY
                     module Trail : TRAIL
                   end) : MATCH =
  struct
    exception Match of string 
    exception NotInvertible 
    open IntSyn
    let delayExp = Unify.delay
    let rec weakenSub =
      begin function
      | (g_, Shift n, ss) ->
          if (<) n ctxLength g_
          then
            begin weakenSub (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss) end
          else begin id end
      | (g_, Dot (Idx n, s'), ss) ->
          (begin match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (g_, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (g_, s', ss)) end)
    | (g_, Dot (Undef, s'), ss) -> comp ((weakenSub (g_, s', ss)), shift) end
(* no other cases, ss is strsub *)
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
      if rOccur = r then begin raise (Match "Variable occurrence") end
      else begin
        ((if Whnf.isPatSub s
          then
            begin (let w = weakenSub (g_, s, ss) in
                   ((if Whnf.isId w then begin EClo (x_, (comp (s, ss))) end
                     else begin
                       raise
                         (Match
                            "Invertible Substitution does not necessarily exist\n") end)
          (* let
                     val wi = Whnf.invert w
                      val V' = EClo (V, wi) *)
          (* val GY = Whnf.strengthen (wi, GX) *)(* shortcut on GY possible by invariant on GX and V[s]? -fp *)
          (* could optimize by checking for identity subst *))) end
  else begin
    (begin try EClo (x_, (Unify.invertSub (g_, s, ss, rOccur)))
     with
     | NotInvertible ->
         let GY = pruneCtx (ss, g_, rOccur) in
         let v'_ = pruneExp (g_, (v_, s), ss, rOccur) in
         let y_ = newEVar (GY, v'_) in
         let _ =
           Unify.addConstraint
             (cnstrs,
               (ref (Eqn (g_, (EClo (x_, s)), (EClo (y_, (Whnf.invert ss))))))) in
         ((y_)
           (* val GY = Whnf.strengthen (ss, G) *)(* shortcuts possible by invariants on G? *)
           (* prune or invert??? *)(* val V' = EClo (V, comp (s, ss)) *)
           (* prune or invert??? *)) end) end)
(* s not patsub *)(* -bp not sure what to do in the non-pattern case *)) end
| (g_, (FgnExp csfe, s), ss, rOccur) ->
    FgnExpStd.Map.apply csfe
      (begin function | u_ -> pruneExp (g_, (u_, s), ss, rOccur) end)
| (g_, ((AVar _ as x_), s), ss, rOccur) -> raise (Match "Left-over AVar") end
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
       | Undef -> raise (Match "Parameter dependency")
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
       | Undef -> raise (Match "Not prunable")
       | Ft -> Dot (Ft, (pruneSub (g_, s', ss, rOccur))) end)
| (g_, Dot (Exp (u_), s'), ss, rOccur) ->
    Dot
      ((Exp (pruneExp (g_, (u_, id), ss, rOccur))),
        (pruneSub (g_, s', ss, rOccur))) end(* below my raise Match *)
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
let rec matchExpW =
  begin function
  | (g_, ((FgnExp csfe1, _) as us1_), us2_) ->
      (begin match FgnExpStd.UnifyWith.apply csfe1 (g_, (EClo us2_)) with
       | Succeed residualL ->
           let rec execResidual =
             begin function
             | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                 let w'_ = pruneExp (g_, (w_, id), ss, r) in
                 Unify.instantiateEVar (r, w'_, !cnstrs)
             | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr) end in
         List.app execResidual residualL
      | Fail -> raise (Match "Foreign Expression Mismatch") end)
  | (g_, us1_, ((FgnExp csfe2, _) as us2_)) ->
      (begin match FgnExpStd.UnifyWith.apply csfe2 (g_, (EClo us1_)) with
       | Succeed opL ->
           let rec execOp =
             begin function
             | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                 let w'_ = pruneExp (g_, (w_, id), ss, r) in
                 Unify.instantiateEVar (r, w'_, !cnstrs)
             | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr) end in
         List.app execOp opL
      | Fail -> raise (Match "Foreign Expression Mismatch") end)
| (g_, (Uni (l1_), _), (Uni (l2_), _)) -> ()
| (g_, ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_)) ->
    (((begin match (h1_, h2_) with
       | (BVar k1, BVar k2) ->
           if k1 = k2 then begin matchSpine (g_, (s1_, s1), (s2_, s2)) end
           else begin raise (Match "Bound variable clash") end
| (Const c1, Const c2) ->
    if c1 = c2 then begin matchSpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Match "Constant clash") end
| (Proj (b1, i1), Proj (b2, i2)) ->
    if i1 = i2
    then
      begin (begin matchBlock (g_, b1, b2);
             matchSpine (g_, (s1_, s1), (s2_, s2)) end) end
else begin raise (Match "Global parameter clash") end
| (Skonst c1, Skonst c2) ->
    if c1 = c2 then begin matchSpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Match "Skolem constant clash") end
| (FVar (n1, _, _), FVar (n2, _, _)) ->
    if n1 = n2 then begin matchSpine (g_, (s1_, s1), (s2_, s2)) end
    else begin raise (Match "Free variable clash") end
| (Def d1, Def d2) ->
    ((if d1 = d2 then begin matchSpine (g_, (s1_, s1), (s2_, s2)) end
    else begin matchDefDefW (g_, us1_, us2_) end)
(* because of strict *)(*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *))
| (Def d1, Const c2) ->
    (((begin match defAncestor d1 with
       | Anc (_, _, None) -> matchExpW (g_, (Whnf.expandDef us1_), us2_)
       | Anc (_, _, Some c1) ->
           if c1 = c2
           then begin matchExpW (g_, (Whnf.expandDef us1_), us2_) end
           else begin raise (Match "Constant clash") end end))
(* conservative *))
| (Const c1, Def d2) ->
    (((begin match defAncestor d2 with
       | Anc (_, _, None) -> matchExpW (g_, us1_, (Whnf.expandDef us2_))
       | Anc (_, _, Some c2) ->
           if c1 = c2
           then begin matchExpW (g_, us1_, (Whnf.expandDef us2_)) end
           else begin raise (Match "Constant clash") end end))
(* conservative *))
| (Def d1, BVar k2) -> raise (Match "Head mismatch")
| (BVar k1, Def d2) -> raise (Match "Head mismatch")
| (Def d1, _) -> matchExpW (g_, (Whnf.expandDef us1_), us2_)
| (_, Def d2) -> matchExpW (g_, us1_, (Whnf.expandDef us2_))
| (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
   (cs2, ConDec (n2, _, _, _, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin () end
    else begin raise (Match "Foreign Constant clash") end
| (FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)), FgnConst
   (cs2, ConDef (n2, _, _, v_, w2_, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin () end
    else begin matchExp (g_, (w1_, s1), (w2_, s2)) end
| (FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _) ->
    matchExp (g_, (w1_, s1), us2_)
| (_, FgnConst (_, ConDef (_, _, _, w2_, _, _, _))) ->
    matchExp (g_, us1_, (w2_, s2)) | _ -> raise (Match "Head mismatch") end))
(* four new cases for defined constants *)(* due to strictness! *)
(* due to strictness! *)(* next two cases for def/fgn, fgn/def *)
(* we require unique string representation of external constants *))
| (g_, (Pi ((d1_, _), u1_), s1), (Pi ((d2_, _), u2_), s2)) ->
    (begin matchDec (g_, (d1_, s1), (d2_, s2));
     matchExp
       ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2))) end)
| (g_, ((Pi (_, _), _) as us1_), ((Root (Def _, _), _) as us2_)) ->
    matchExpW (g_, us1_, (Whnf.expandDef us2_))
| (g_, ((Root (Def _, _), _) as us1_), ((Pi (_, _), _) as us2_)) ->
    matchExpW (g_, (Whnf.expandDef us1_), us2_)
| (g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2)) ->
    matchExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2)))
| (g_, (Lam (d1_, u1_), s1), (u2_, s2)) ->
    matchExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)),
        ((Redex ((EClo (u2_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s2)))
| (g_, (u1_, s1), (Lam (d2_, u2_), s2)) ->
    matchExp
      ((Decl (g_, (decSub (d2_, s2)))),
        ((Redex ((EClo (u1_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s1)), (u2_, (dot1 s2)))
| (g_, ((EVar (r, GX, v_, cnstrs), s) as us1_), ((u2_, s2) as us2_)) ->
    if Whnf.isPatSub s
    then
      begin let ss = Whnf.invert s in
            let U2' = pruneExp (g_, us2_, ss, r) in
            ((Unify.instantiateEVar (r, U2', !cnstrs))
              (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
              (* invertExpW (Us2, s, r) *)) end
    else begin
      Unify.addConstraint
        (cnstrs, (ref (Eqn (g_, (EClo us1_), (EClo us2_))))) end
| (g_, us1_, us2_) -> raise (Match "Expression clash") end(* invertExpW (Us1, s, r) *)
(*      | matchExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val U1' = pruneExp (G, Us1, ss, r)
          in
             instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
(* invertExpW (Us1, s2, ref NONE) *)(* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
(* invertExpW (Us2, s1, ref NONE) *)(* Unify.instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
(* invertExp ((V1, id), s', ref NONE) *)(* X[s] = X[s] *)
(* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
(* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
(* compute ss' directly? *)(*      | matchExpW (G, Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                   Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub *)
(* same reasoning holds as above *)(* Cannot occur if expressions are eta expanded *)
(* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
(* ETA: can't occur if eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
(* order of calls critical to establish matchSpine invariant *)(* s1 = s2 = id by whnf *)
(* matchUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)(* L1 = L2 = type, by invariant *)
let rec matchExp (g_, ((e1_, s1) as us1_), ((e2_, s2) as us2_)) =
  matchExpW (g_, (Whnf.whnf us1_), (Whnf.whnf us2_))
let rec matchDefDefW
  (g_, ((Root (Def d1, s1_), s1) as us1_),
   ((Root (Def d2, s2_), s2) as us2_))
  =
  let Anc (_, h1, c1Opt) = defAncestor d1 in
  let Anc (_, h2, c2Opt) = defAncestor d2 in
  let _ =
    begin match (c1Opt, c2Opt) with
    | (Some c1, Some c2) ->
        if c1 <> c2
        then begin raise (Match "Irreconcilable defined constant clash") end
        else begin () end
    | _ -> () end in
((begin match Int.compare (h1, h2) with
  | EQUAL -> matchExpW (g_, (Whnf.expandDef us1_), (Whnf.expandDef us2_))
  | LESS -> matchExpW (g_, us1_, (Whnf.expandDef us2_))
  | GREATER -> matchExpW (g_, (Whnf.expandDef us1_), us2_) end)
  (* conservative *))(*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
let rec matchSpine =
  begin function
  | (g_, (Nil, _), (Nil, _)) -> ()
  | (g_, (SClo (s1_, s1'), s1), ss_) ->
      matchSpine (g_, (s1_, (comp (s1', s1))), ss_)
  | (g_, ss_, (SClo (s2_, s2'), s2)) ->
      matchSpine (g_, ss_, (s2_, (comp (s2', s2))))
  | (g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2)) ->
      (begin matchExp (g_, (u1_, s1), (u2_, s2));
       matchSpine (g_, (s1_, s1), (s2_, s2)) end) end
let rec matchDec (g_, (Dec (_, v1_), s1), (Dec (_, v2_), s2)) =
  matchExp (g_, (v1_, s1), (v2_, s2))
let rec matchSub =
  begin function
  | (g_, Shift n1, Shift n2) -> ()
  | (g_, Shift n, (Dot _ as s2)) ->
      matchSub (g_, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
  | (g_, (Dot _ as s1), Shift m) ->
      matchSub (g_, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
  | (g_, Dot (Ft1, s1), Dot (Ft2, s2)) ->
      (((begin (begin match (Ft1, Ft2) with
                | (Idx n1, Idx n2) ->
                    if n1 <> n2
                    then begin raise (Error "SOME variables mismatch") end
                    else begin () end
      | (Exp (u1_), Exp (u2_)) -> matchExp (g_, (u1_, id), (u2_, id))
      | (Exp (u1_), Idx n2) ->
          matchExp (g_, (u1_, id), ((Root ((BVar n2), Nil)), id))
      | (Idx n1, Exp (u2_)) ->
          matchExp (g_, ((Root ((BVar n1), Nil)), id), (u2_, id)) end);
  matchSub (g_, s1, s2) end))
(*         | (Undef, Undef) =>
           | _ => false *)
(* not possible because of invariant? -cs *)) end(* by invariant *)
let rec matchBlock =
  begin function
  | (g_, LVar ({ contents = Some (b1_) }, s, _), b2_) ->
      matchBlock (g_, (blockSub (b1_, s)), b2_)
  | (g_, b1_, LVar ({ contents = Some (b2_) }, s, _)) ->
      matchBlock (g_, b1_, (blockSub (b2_, s)))
  | (g_, b1_, b2_) -> matchBlockW (g_, b1_, b2_) end
let rec matchBlockW =
  begin function
  | (g_, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2))) ->
      if l1 <> l2 then begin raise (Match "Label clash") end
      else begin if r1 = r2 then begin () end
        else begin
          (((begin matchSub (g_, t1, t2);
             if k1 <> k2 then begin raise Bind end
             else begin () end;
        (let ss = Whnf.invert (Shift k1) in
         let t2' = pruneSub (g_, t2, ss, (ref None)) in
         ((Unify.instantiateLVar (r1, (LVar (r2, (Shift 0), (l2, t2')))))
           (* hack! *)(* 0 = k2-k1 *))) end))
  (* Sat Dec  7 22:04:31 2002 -fp *)(* invariant? always k1 = k2? *)
  (* prune t2? Sat Dec  7 22:09:53 2002 *)(*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)) end end
| (g_, LVar (r1, s1, (l1, t1)), b2_) ->
    (begin (:=) r1 Some (blockSub (b2_, (Whnf.invert s1))); () end)
| (g_, b1_, LVar (r2, s2, (l2, t2))) ->
    (begin (:=) r2 Some (blockSub (b1_, (Whnf.invert s2))); () end)
| (g_, Bidx n1, Bidx n2) ->
    if n1 <> n2 then begin raise (Match "Block index clash") end
    else begin () end end(* Sat Dec  8 11:49:16 2001 -fp !!! *)(* How can the next case arise? *)
(* -- ABP *)(*      | matchBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP *)
(* -- ABP *)(* -- ABP *)
let rec match1W (g_, us1_, us2_) =
  begin matchExpW (g_, us1_, us2_); awakeCnstr (Unify.nextCnstr ()) end
let rec match1 (g_, us1_, us2_) =
  begin matchExp (g_, us1_, us2_); awakeCnstr (Unify.nextCnstr ()) end
let rec awakeCnstr =
  begin function
  | None -> ()
  | Some { contents = Solved } -> awakeCnstr (Unify.nextCnstr ())
  | Some ({ contents = Eqn (g_, u1_, u2_) } as cnstr) ->
      (begin Unify.solveConstraint cnstr; match1 (g_, (u1_, id), (u2_, id)) end)
  | Some { contents = FgnCnstr csfc } ->
      if FgnCnstrStd.Awake.apply csfc () then begin () end
      else begin raise (Match "Foreign constraint violated") end end
let rec matchW (g_, us1_, us2_) =
  begin Unify.resetAwakenCnstrs (); match1W (g_, us1_, us2_) end
let rec match_ (g_, us1_, us2_) =
  begin Unify.resetAwakenCnstrs (); match1 (g_, us1_, us2_) end
let matchW = matchW
let match_ = match_
let matchSub = matchSub
let matchBlock = matchBlock
let rec instance (g_, us1_, us2_) =
  begin try begin match_ (g_, us1_, us2_); true end with | Match msg -> false end
let rec instance' (g_, us1_, us2_) =
  begin try begin match_ (g_, us1_, us2_); None end
  with | Match msg -> Some msg end end
