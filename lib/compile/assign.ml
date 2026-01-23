module type ASSIGN  =
  sig
    val assignable :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> IntSyn.cnstr_ list option
    val solveCnstr : IntSyn.cnstr_ list -> bool
    val unifiable : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    val instance : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    val firstConstArg : (IntSyn.exp_ * IntSyn.sub_) -> IntSyn.cid option
  end


module Assign(Assign:sig
                       module Whnf : WHNF
                       module Unify : UNIFY
                       module Print : PRINT
                     end) : ASSIGN =
  struct
    exception Assignment of string 
    open IntSyn
    let rec assignExpW =
      begin function
      | (g_, (Uni (l1_), _), (Uni (l2_), _), cnstr) -> cnstr
      | (g_, ((Root (h1_, s1_), s1) as us1_),
         ((Root (h2_, s2_), s2) as us2_), cnstr) ->
          (((begin match (h1_, h2_) with
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then begin assignSpine (g_, (s1_, s1), (s2_, s2), cnstr) end
                 else begin raise (Assignment "Constant clash") end
      | (BVar k1, BVar k2) ->
          if k1 = k2
          then begin assignSpine (g_, (s1_, s1), (s2_, s2), cnstr) end
          else begin raise (Assignment "Bound variable clash") end
      | (Skonst c1, Skonst c2) ->
          if c1 = c2
          then begin assignSpine (g_, (s1_, s1), (s2_, s2), cnstr) end
          else begin raise (Assignment "Skolem constant clash") end
    | (Def d1, Def d2) ->
        ((if d1 = d2
          then begin assignSpine (g_, (s1_, s1), (s2_, s2), cnstr) end
        else begin
          assignExp (g_, (Whnf.expandDef us1_), (Whnf.expandDef us2_), cnstr) end)
  (* because of strict *))
| (Def d1, _) -> assignExp (g_, (Whnf.expandDef us1_), us2_, cnstr)
| (_, Def d2) -> assignExp (g_, us1_, (Whnf.expandDef us2_), cnstr)
| (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
   (cs2, ConDec (n2, _, _, _, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin cnstr end
    else begin raise (Assignment "Foreign Constant clash") end
| (FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)), FgnConst
   (cs2, ConDef (n2, _, _, v_, w2_, _, _))) ->
    if (cs1 = cs2) && (n1 = n2) then begin cnstr end
    else begin assignExp (g_, (w1_, s1), (w2_, s2), cnstr) end
| (FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _) ->
    assignExp (g_, (w1_, s1), us2_, cnstr)
| (_, FgnConst (_, ConDef (_, _, _, w2_, _, _, _))) ->
    assignExp (g_, us1_, (w2_, s2), cnstr)
| _ -> raise (Assignment "Head mismatch ") end))
(* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
(* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
(* we require unique string representation of external constants *))
| (g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2), cnstr) ->
    assignExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2)),
        cnstr)
| (g_, (u1_, s1), (Lam (d2_, u2_), s2), cnstr) ->
    assignExp
      ((Decl (g_, (decSub (d2_, s2)))),
        ((Redex ((EClo (u1_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s1)), (u2_, (dot1 s2)), cnstr)
| (g_, (Pi (((Dec (_, v1_) as d1_), _), u1_), s1),
   (Pi (((Dec (_, v2_) as d2_), _), u2_), s2), cnstr) ->
    let cnstr' = assignExp (g_, (v1_, s1), (v2_, s2), cnstr) in
    assignExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)), (u2_, (dot1 s2)),
        cnstr')
| (g_, ((u_, s1) as us1_), ((EVar (r2, _, _, _), s2) as us2_), cnstr) ->
    (begin (:=) r2 Some (EClo us1_); cnstr end)
| (g_, ((u_, s1) as us1_), ((AVar r2, s2) as us2_), cnstr) ->
    (begin (:=) r2 Some (EClo us1_); cnstr end)
| (g_, (Lam (d1_, u1_), s1), (u2_, s2), cnstr) ->
    assignExp
      ((Decl (g_, (decSub (d1_, s1)))), (u1_, (dot1 s1)),
        ((Redex ((EClo (u2_, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
          (dot1 s2)), cnstr)
| (g_, us1_, ((EClo (u_, s'), s) as us2_), cnstr) ->
    assignExp (g_, us1_, (u_, (comp (s', s))), cnstr)
| (g_, ((EVar (r, _, v_, Cnstr), s) as us1_), us2_, cnstr) ->
    (Eqn (g_, (EClo us1_), (EClo us2_))) :: cnstr
| (g_, ((EClo (u_, s'), s) as us1_), us2_, cnstr) ->
    assignExp (g_, (u_, (comp (s', s))), us2_, cnstr)
| (g_, ((FgnExp (_, fe), _) as us1_), us2_, cnstr) ->
    (Eqn (g_, (EClo us1_), (EClo us2_))) :: cnstr
| (g_, us1_, ((FgnExp (_, fe), _) as us2_), cnstr) ->
    (Eqn (g_, (EClo us1_), (EClo us2_))) :: cnstr end(* by invariant Us2 cannot contain any FgnExp *)
(* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
(* ETA: can't occur if eta expanded *)(* don't trail, because AVars never survive local scope *)
(* s2 = id *)(* Tue Apr  2 10:23:19 2002 -bp -fp *)
(* don't trail, because EVar has been created since most recent choice point *)
(* s2 = id *)(* same reasoning holds as above *)
(* Cannot occur if expressions are eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
(* L1 = L2 by invariant *)
let rec assignSpine =
  begin function
  | (g_, (Nil, _), (Nil, _), cnstr) -> cnstr
  | (g_, (SClo (s1_, s1'), s1), ss_, cnstr) ->
      assignSpine (g_, (s1_, (comp (s1', s1))), ss_, cnstr)
  | (g_, ss_, (SClo (s2_, s2'), s2), cnstr) ->
      assignSpine (g_, ss_, (s2_, (comp (s2', s2))), cnstr)
  | (g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2), cnstr) ->
      let cnstr' = assignExp (g_, (u1_, s1), (u2_, s2), cnstr) in
      assignSpine (g_, (s1_, s1), (s2_, s2), cnstr') end
let rec assignExp (g_, us1_, ((u2_, s2) as us2_), cnstr) =
  assignExpW (g_, (Whnf.whnf us1_), (Whnf.whnf us2_), cnstr)
let rec solveCnstr =
  begin function
  | [] -> true
  | (Eqn (g_, u1_, u2_))::Cnstr ->
      (Unify.unifiable (g_, (u1_, id), (u2_, id))) && (solveCnstr Cnstr) end
let rec printSub =
  begin function
  | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
  | Dot (Idx n, s) ->
      (begin print (((^) "Idx " Int.toString n) ^ " . "); printSub s end)
  | Dot (Exp (EVar (_, _, _, _)), s) ->
      (begin print "Exp (EVar _ ). "; printSub s end)
  | Dot (Exp (AVar _), s) -> (begin print "Exp (AVar _ ). "; printSub s end)
| Dot (Exp (EClo (AVar _, _)), s) ->
    (begin print "Exp (AVar _ ). "; printSub s end)
| Dot (Exp (EClo (_, _)), s) ->
    (begin print "Exp (EClo _ ). "; printSub s end)
| Dot (Exp _, s) -> (begin print "Exp (_ ). "; printSub s end)
| Dot (Undef, s) -> (begin print "Undef . "; printSub s end) end
let rec unifyW =
  begin function
  | (g_, ((AVar ({ contents = None } as r) as xs1_), s), us2_) ->
      (:=) r Some (EClo us2_)
  | (g_, xs1_, us2_) -> Unify.unifyW (g_, xs1_, us2_) end(* Xs1 should not contain any uninstantiated AVar anymore *)
(* s = id *)
let rec unify (g_, xs1_, us2_) =
  unifyW (g_, (Whnf.whnf xs1_), (Whnf.whnf us2_))
let rec matchW =
  begin function
  | (g_, ((AVar ({ contents = None } as r) as xs1_), s), us2_) ->
      (:=) r Some (EClo us2_)
  | (g_, xs1_, us2_) -> Match.matchW (g_, xs1_, us2_) end(* Xs1 should not contain any uninstantiated AVar anymore *)
(* s = id *)
let rec match_ (g_, xs1_, us2_) =
  matchW (g_, (Whnf.whnf xs1_), (Whnf.whnf us2_))
let solveCnstr = solveCnstr
let rec unifiable (g_, us1_, us2_) =
  begin try begin unify (g_, us1_, us2_); true end with | Unify msg -> false end
let rec instance (g_, us1_, us2_) =
  begin try begin match_ (g_, us1_, us2_); true end with | Match msg -> false end
let rec assignable (g_, us1_, Uts2) =
  begin try Some (assignExp (g_, us1_, Uts2, []))
  with | Assignment msg -> None end
let rec firstConstArg ((Root ((Const c as h), s_) as a_), s) =
  let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
  let rec constExp (u_, s) = constExpW (Whnf.whnf (u_, s))
  and constExpW =
    begin function
    | (Lam (d_, u_), s) -> constExp (u_, s)
    | (Root ((Const cid as h_), s_), s) -> Some cid
    | (_, _) -> None end in
  let rec ithElem =
    begin function
    | (k, (App (u_, s_), s)) -> if k = i then begin constExp (u_, s) end
        else begin ithElem ((k + 1), (s_, s)) end
    | (k, (IntSyn.Nil, s)) -> None end in
((ithElem (0, (s_, s)))
  (* #implicit arguments to predicate *)(* other cases cannot occur during compilation *))
end
