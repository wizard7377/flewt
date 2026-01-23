module type SUBTREE  =
  sig
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.exp_) RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.dec_ IntSyn.ctx_ * (typeLabel * IntSyn.exp_)) RBSet.ordSet
    type cGoal_ =
      | CGoals of (CompSyn.auxGoal_ * IntSyn.cid * CompSyn.conjunction_ *
      int) 
    type assSub_ =
      | Assign of (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_) 
    type nonrec assSubsts = assSub_ RBSet.ordSet
    type cnstr_ =
      | Eqn of (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ * IntSyn.exp_) 
    type tree_ =
      | Leaf of (normalSubsts * IntSyn.dec_ IntSyn.ctx_ * cGoal_) 
      | Node of (normalSubsts * tree_ RBSet.ordSet) 
    val indexArray : (int ref * tree_ ref) Array.array
    val sProgReset : unit -> unit
    val sProgInstall :
      (IntSyn.cid * CompSyn.compHead_ * CompSyn.conjunction_) -> unit
    val matchSig :
      (IntSyn.cid * IntSyn.dec_ IntSyn.ctx_ * IntSyn.eclo *
        (((CompSyn.conjunction_ * IntSyn.sub_) * IntSyn.cid) -> unit)) ->
        unit
  end


module SubTree(SubTree:sig
                         module Whnf : WHNF
                         module Unify : UNIFY
                         module Print : PRINT
                         module CPrint : CPRINT
                         module Formatter : FORMATTER
                         module Names : NAMES
                         module CSManager : CS_MANAGER
                       end) : SUBTREE =
  struct
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.exp_) RBSet.ordSet
    type assSub_ =
      | Assign of (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_) 
    type nonrec assSubsts = assSub_ RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.dec_ IntSyn.ctx_ * (typeLabel * IntSyn.exp_)) RBSet.ordSet
    type cnstr_ =
      | Eqn of (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ * IntSyn.exp_) 
    type nonrec cnstrSubsts = IntSyn.exp_ RBSet.ordSet
    type cGoal_ =
      | CGoals of (CompSyn.auxGoal_ * IntSyn.cid * CompSyn.conjunction_ *
      int) 
    type genType =
      | Top 
      | Regular 
    type tree_ =
      | Leaf of (normalSubsts * IntSyn.dec_ IntSyn.ctx_ * cGoal_) 
      | Node of (normalSubsts * tree_ RBSet.ordSet) 
    type nonrec candidate =
      (assSubsts * normalSubsts * cnstrSubsts * cnstr_ * IntSyn.dec_
        IntSyn.ctx_ * cGoal_)
    let (nid : unit -> normalSubsts) = RBSet.new_
    let (assignSubId : unit -> assSubsts) = RBSet.new_
    let (cnstrSubId : unit -> cnstrSubsts) = RBSet.new_
    let (querySubId : unit -> querySubsts) = RBSet.new_
    let rec isId s = RBSet.isEmpty s
    let rec makeTree () = ref (Node ((nid ()), (RBSet.new_ ())))
    let rec noChildren (c_) = RBSet.isEmpty c_
    let indexArray =
      Array.tabulate
        (Global.maxCid, (begin function | i -> ((ref 0), (makeTree ())) end))
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    exception Error of string 
    exception Assignment of string 
    exception Generalization of string 
    let rec cidFromHead = begin function | Const c -> c | Def c -> c end
  let rec dotn =
    begin function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s)) end
let rec compose' =
  begin function
  | (IntSyn.Null, g_) -> g_
  | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose' (g_, g'_)), d_) end
let rec shift =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Lam (d_, v_))) end
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
| Dot (IntSyn.Undef, s) -> (begin print "Undef . "; printSub s end) end
let nctr = ref 1
let rec newNVar () = begin ((!) ((:=) nctr) nctr) + 1; I.NVar !nctr end
let rec eqHeads =
  begin function
  | (Const k, Const k') -> k = k'
  | (BVar k, BVar k') -> k = k'
  | (Def k, Def k') -> k = k'
  | (_, _) -> false end
let rec compatible (label, t_, u_, rho_t, rho_u) =
  let rec genExp =
    begin function
    | (label, b, (NVar n as t_), (Root (h_, s_) as u_)) ->
        (begin S.insert rho_u (n, (label, u_)); t_ end)
    | (label, b, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
        if eqHeads (h1_, h2_)
        then begin I.Root (h1_, (genSpine (label, b, s1_, s2_))) end
        else begin
          (begin match b with
           | Regular ->
               (begin S.insert rho_t ((!nctr + 1), (label, t_));
                S.insert rho_u ((!nctr + 1), (label, u_));
                newNVar () end)
          | _ -> raise (Generalization "Should never happen!") end) end
  | (label, b, Lam ((Dec (n_, a1_) as d1_), t1_), Lam
     ((Dec (_, a2_) as d2_), u2_)) ->
      I.Lam
        ((I.Dec (n_, (genExp (TypeLabel, Regular, a1_, a2_)))),
          (genExp (label, b, t1_, u2_)))
  | (label, b, Pi (((d1_, I.No) as DD1), e1_), Pi
     (((d2_, I.No) as DD2), e2_)) ->
      I.Pi
        (((genDec (TypeLabel, Regular, d1_, d2_)), I.No),
          (genExp (label, b, e1_, e2_)))
  | (label, b, Pi (((d1_, I.Maybe) as DD1), e1_), Pi
     (((d2_, I.Maybe) as DD2), e2_)) ->
      I.Pi
        (((genDec (TypeLabel, Regular, d1_, d2_)), I.Maybe),
          (genExp (label, b, e1_, e2_)))
  | (label, b, Pi (((d1_, I.Meta) as DD1), e1_), Pi
     (((d2_, I.Meta) as DD2), e2_)) ->
      I.Pi
        (((genDec (TypeLabel, Regular, d1_, d2_)), I.Meta),
          (genExp (label, b, e1_, e2_)))
  | (label, b, t_, u_) ->
      raise
        (Generalization "Cases where U= EVar or EClo should never happen!") end
(* NOTE: by invariant A1 =/= A2 *)(* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *)
(* = S.existsOpt (fn U' => equalTerm (U, U')) *)
and genSpine =
  begin function
  | (label, b, I.Nil, I.Nil) -> I.Nil
  | (label, b, App (t_, s1_), App (u_, s2_)) ->
      I.App ((genExp (label, b, t_, u_)), (genSpine (label, b, s1_, s2_))) end
and genDec (label, b, Dec (n_, e1_), Dec (n'_, e2_)) =
  I.Dec (n_, (genExp (label, b, e1_, e2_))) in
let rec genTop =
begin function
| (label, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
    if eqHeads (h1_, h2_)
    then begin I.Root (h1_, (genSpine (label, Regular, s1_, s2_))) end
    else begin raise (Generalization "Top-level function symbol not shared") end
| (label, Lam ((Dec (n_, a1_) as d1_), t1_), Lam
   ((Dec (_, a2_) as d2_), u2_)) ->
    I.Lam
      ((I.Dec (n_, (genExp (label, Regular, a1_, a2_)))),
        (genTop (label, t1_, u2_)))
| (_, _, _) -> raise (Generalization "Top-level function symbol not shared") end
(* by invariant A1 =/= A2 *) in
begin try Some (genTop (label, t_, u_)) with | Generalization msg -> None end
let rec compatibleSub (nsub_t, nsub_e) =
  let (sg, rho_t, rho_e) = ((nid ()), (nid ()), (nid ())) in
  let _ =
    S.forall nsub_e
      (begin function
       | (nv, (l', e_)) ->
           (((begin match S.lookup nsub_t nv with
              | Some (l, t_) ->
                  if l = l'
                  then
                    begin (begin match compatible (l, t_, e_, rho_t, rho_e)
                                 with
                           | None ->
                               (begin S.insert rho_t (nv, (l, t_));
                                S.insert rho_e (nv, (l, e_)) end)
                    | Some (t'_) -> S.insert sg (nv, (l, t'_)) end) end
           else begin raise (Generalization "Labels don't agree\n") end
    | None -> S.insert rho_e (nv, (l', e_)) end))
    (* by invariant d = d'
                                     therefore T and E have the same approximate type A *)) end) in
((if isId sg then begin None end else begin Some (sg, rho_t, rho_e) end)
(* by invariant rho_t = empty, since nsub_t <= nsub_e *))
let rec mkNode =
  begin function
  | (Node (_, Children), sg, rho1, ((g_, RC) as GR), rho2) ->
      let c = S.new_ () in
      (begin S.insertList c
               [(1, (Node (rho1, Children))); (2, (Leaf (rho2, g_, RC)))];
       Node (sg, c) end)
  | (Leaf (_, g1_, RC1), sg, rho1, ((g2_, RC2) as GR), rho2) ->
      let c = S.new_ () in
      (begin S.insertList c
               [(1, (Leaf (rho1, g1_, RC1))); (2, (Leaf (rho2, g2_, RC2)))];
       Node (sg, c) end) end
let rec compareChild
  (children, (n, child), nsub_t, nsub_e, ((G_clause2, Res_clause2) as GR)) =
  begin match compatibleSub (nsub_t, nsub_e) with
  | None ->
      S.insert children ((n + 1), (Leaf (nsub_e, G_clause2, Res_clause2)))
  | Some (sg, rho1, rho2) ->
      if isId rho1
      then
        begin (((if isId rho2
                 then
                   begin S.insertShadow children
                           (n, (mkNode (child, sg, rho1, GR, rho2))) end
        else begin S.insertShadow children (n, (insert (child, rho2, GR))) end))
      (* sg = nsub_t = nsub_e *)(* sg = nsub_t and nsub_e = sg o rho2 *)) end
  else begin
    S.insertShadow children (n, (mkNode (child, sg, rho1, GR, rho2))) end end
let rec insert =
  begin function
  | ((Leaf (nsub_t, G_clause1, r1_) as n_), nsub_e, ((G_clause2, r2_) as GR))
      ->
      (begin match compatibleSub (nsub_t, nsub_e) with
       | None -> raise (Error "Leaf is not compatible substitution r")
       | Some (sg, rho1, rho2) -> mkNode (n_, sg, rho1, GR, rho2) end)
  | ((Node (_, children) as n_), nsub_e, ((G_clause2, RC) as GR)) ->
      ((if noChildren children
        then
          begin (begin S.insert children (1, (Leaf (nsub_e, G_clause2, RC)));
                 n_ end) end
  else begin
    (begin match S.last children with
     | (n, (Node (nsub_t, children') as child)) ->
         (begin compareChild (children, (n, child), nsub_t, nsub_e, GR); n_ end)
    | (n, (Leaf (nsub_t, g1_, RC1) as child)) ->
        (begin compareChild (children, (n, child), nsub_t, nsub_e, GR); n_ end) end) end)
(* initial *)) end
let rec normalizeNExp =
  begin function
  | (NVar n, csub) ->
      let a_ = I.newAVar () in (begin S.insert csub (n, a_); a_ end)
  | (Root (h_, s_), nsub) -> I.Root (h_, (normalizeNSpine (s_, nsub)))
  | (Lam (d_, u_), nsub) ->
      I.Lam ((normalizeNDec (d_, nsub)), (normalizeNExp (u_, nsub)))
  | (Pi ((d_, p_), u_), nsub) ->
      I.Pi (((normalizeNDec (d_, nsub)), p_), (normalizeNExp (u_, nsub))) end
(* cannot happen -bp *)
let rec normalizeNSpine =
  begin function
  | (I.Nil, _) -> I.Nil
  | (App (u_, s_), nsub) ->
      I.App ((normalizeNExp (u_, nsub)), (normalizeNSpine (s_, nsub))) end
let rec normalizeNDec (Dec (n_, e_), nsub) =
  I.Dec (n_, (normalizeNExp (e_, nsub)))
let rec assign (nvaronly, Glocal_u1, us1_, u2_, nsub_goal, asub, csub, cnstr)
  =
  let depth = I.ctxLength Glocal_u1 in
  let rec assignHead
    (nvaronly, depth, Glocal_u1, ((Root (h1_, s1_), s1) as us1_),
     (Root (h2_, s2_) as u2_), cnstr)
    =
    ((begin match (h1_, h2_) with
      | (Const c1, Const c2) ->
          if c1 = c2
          then
            begin assignSpine
                    (nvaronly, depth, Glocal_u1, (s1_, s1), s2_, cnstr) end
          else begin raise (Assignment "Constant clash") end
  | (Skonst c1, Skonst c2) ->
      if c1 = c2
      then
        begin assignSpine (nvaronly, depth, Glocal_u1, (s1_, s1), s2_, cnstr) end
      else begin raise (Assignment "Skolem constant clash") end
    | (Def d1, _) ->
        assignExp
          (nvaronly, depth, Glocal_u1, (Whnf.expandDef us1_), u2_, cnstr)
    | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
       (cs2, ConDec (n2, _, _, _, _, _))) ->
        if (cs1 = cs2) && (n1 = n2) then begin cnstr end
        else begin raise (Assignment "Foreign Constant clash") end
  | (FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)), FgnConst
     (cs2, ConDef (n2, _, _, v_, w2_, _, _))) ->
      if (cs1 = cs2) && (n1 = n2) then begin cnstr end
      else begin
        assignExp (nvaronly, depth, Glocal_u1, (w1_, s1), w2_, cnstr) end
| (FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _) ->
    assignExp (nvaronly, depth, Glocal_u1, (w1_, s1), u2_, cnstr)
| (_, FgnConst (_, ConDef (_, _, _, w2_, _, _, _))) ->
    assignExp (nvaronly, depth, Glocal_u1, us1_, w2_, cnstr)
| (_, _) -> raise (Assignment "Head mismatch ") end)
(* we require unique string representation of external constants *))
and assignExpW =
  begin function
  | (nvaronly, depth, Glocal_u1, (Uni (l1_), s1), Uni (l2_), cnstr) -> cnstr
  | (nvaronly, depth, Glocal_u1, us1_, NVar n, cnstr) ->
      (begin S.insert nsub_goal (n, (Glocal_u1, (nvaronly, (I.EClo us1_))));
       cnstr end)
  | (Body, depth, Glocal_u1, ((Root (h1_, s1_), s1) as us1_),
     (Root (h2_, s2_) as u2_), cnstr) ->
      (begin match h2_ with
       | BVar k2 ->
           ((if k2 > depth
             then
               begin (begin S.insert asub
                              (((-) k2 I.ctxLength Glocal_u1),
                                (Assign (Glocal_u1, (I.EClo us1_))));
                      cnstr end) end
       else begin
         (begin match h1_ with
          | BVar k1 ->
              if k1 = k2
              then
                begin assignSpine
                        (Body, depth, Glocal_u1, (s1_, s1), s2_, cnstr) end
              else begin raise (Assignment "Bound variable clash") end
       | _ -> raise (Assignment "Head mismatch") end) end)
(* BVar(k2) stands for an existential variable *)(* S2 is an etaSpine by invariant *))
| _ -> assignHead (Body, depth, Glocal_u1, us1_, u2_, cnstr) end)
| (TypeLabel, depth, Glocal_u1, ((Root (h1_, s1_), s1) as us1_),
   (Root (h2_, s2_) as u2_), cnstr) ->
    (begin match h2_ with
     | BVar k2 -> ((if k2 > depth then begin cnstr end
         else begin
           (begin match h1_ with
            | BVar k1 ->
                if k1 = k2
                then
                  begin assignSpine
                          (TypeLabel, depth, Glocal_u1, (s1_, s1), s2_,
                            cnstr) end
                else begin raise (Assignment "Bound variable clash") end
         | _ -> raise (Assignment "Head mismatch") end) end)
(* BVar(k2) stands for an existential variable *)(* then by invariant, it must have been already instantiated *))
| _ -> assignHead (TypeLabel, depth, Glocal_u1, us1_, u2_, cnstr) end)
| (nvaronly, depth, Glocal_u1, us1_, (Root (BVar k2, s_) as u2_), cnstr) ->
    ((if k2 > depth
      then
        begin (begin match nvaronly with
               | TypeLabel -> cnstr
               | Body ->
                   (begin S.insert asub
                            ((k2 - depth),
                              (Assign (Glocal_u1, (I.EClo us1_))));
                    cnstr end) end) end
else begin
  (begin match nvaronly with
   | TypeLabel -> cnstr
   | Body ->
       (begin match us1_ with
        | (EVar (r, _, v_, Cnstr), s) ->
            let U2' = normalizeNExp (u2_, csub) in
            (Eqn (Glocal_u1, (I.EClo us1_), U2')) :: cnstr
        | (EClo (u_, s'), s) ->
            assignExp
              (Body, depth, Glocal_u1, (u_, (I.comp (s', s))), u2_, cnstr)
        | (FgnExp (_, ops), _) ->
            let U2' = normalizeNExp (u2_, csub) in
            (Eqn (Glocal_u1, (I.EClo us1_), U2')) :: cnstr end) end) end)
(* BVar(k2) stands for an existential variable *)(* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
(* Glocal_u1 |- Us1 *))
| (nvaronly, depth, Glocal_u1, (Lam ((Dec (_, a1_) as d1_), u1_), s1), Lam
   ((Dec (_, a2_) as d2_), u2_), cnstr) ->
    let cnstr' =
      assignExp (TypeLabel, depth, Glocal_u1, (a1_, s1), a2_, cnstr) in
    ((assignExp
        (nvaronly, (depth + 1), (I.Decl (Glocal_u1, (I.decSub (d1_, s1)))),
          (u1_, (I.dot1 s1)), u2_, cnstr'))
      (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *))
| (nvaronly, depth, Glocal_u1, (Pi (((Dec (_, a1_) as d1_), _), u1_), s1), Pi
   (((Dec (_, a2_) as d2_), _), u2_), cnstr) ->
    let cnstr' =
      assignExp (TypeLabel, depth, Glocal_u1, (a1_, s1), a2_, cnstr) in
    ((assignExp
        (nvaronly, (depth + 1), (I.Decl (Glocal_u1, (I.decSub (d1_, s1)))),
          (u1_, (I.dot1 s1)), u2_, cnstr'))
      (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *))
| (nvaronly, depth, Glocal_u1, ((EVar (r, _, v_, Cnstr), s) as us1_), u2_,
   cnstr) ->
    let U2' = normalizeNExp (u2_, csub) in
    (Eqn (Glocal_u1, (I.EClo us1_), U2')) :: cnstr
| (nvaronly, depth, Glocal_u1, ((EClo (u_, s'), s) as us1_), u2_, cnstr) ->
    assignExp
      (nvaronly, depth, Glocal_u1, (u_, (I.comp (s', s))), u2_, cnstr)
| (nvaronly, depth, Glocal_u1, ((FgnExp (_, ops), _) as us1_), u2_, cnstr) ->
    let U2' = normalizeNExp (u2_, csub) in
    (Eqn (Glocal_u1, (I.EClo us1_), U2')) :: cnstr
| (nvaronly, depth, Glocal_u1, us1_, (FgnExp (_, ops) as u2_), cnstr) ->
    (Eqn (Glocal_u1, (I.EClo us1_), u2_)) :: cnstr end(* by invariant Us2 cannot contain any FgnExp *)
(* generate cnstr substitution for all nvars occurring in U2 *)(* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)
(* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
(* D1[s1] = D2[s2]  by invariant *)(* D1[s1] = D2[s2]  by invariant *)
(* by invariant Us2 cannot contain any FgnExp *)(* here spine associated with k2 might not be Nil ? *)
(* L1 = L2 by invariant *)
and assignSpine =
  begin function
  | (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) -> cnstr
  | (nvaronly, depth, Glocal_u1, (SClo (s1_, s1'), s1), s_, cnstr) ->
      assignSpine
        (nvaronly, depth, Glocal_u1, (s1_, (I.comp (s1', s1))), s_, cnstr)
  | (nvaronly, depth, Glocal_u1, (App (u1_, s1_), s1), App (u2_, s2_), cnstr)
      ->
      let cnstr' =
        assignExp (nvaronly, depth, Glocal_u1, (u1_, s1), u2_, cnstr) in
      ((assignSpine (nvaronly, depth, Glocal_u1, (s1_, s1), s2_, cnstr'))
        (* nsub_goal, asub may be destructively updated *)) end
and assignExp (nvaronly, depth, Glocal_u1, us1_, u2_, cnstr) =
  assignExpW (nvaronly, depth, Glocal_u1, (Whnf.whnf us1_), u2_, cnstr) in
((assignExp (nvaronly, depth, Glocal_u1, us1_, u2_, cnstr))
(*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
           Cannot occur if expressions are eta expanded *)
(*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
       ETA: can't occur if eta expanded *)
(* same reasoning holds as above *))
let rec assignableLazy
  (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
  let nsub_query' = querySubId () in
  let cref = ref cnstr in
  let rec assign' (nsub_query, nsub) =
    let (nsub_query_left, nsub_left1) =
      S.differenceModulo nsub_query nsub
        (begin function
         | (Glocal_u, (l, u_)) ->
             (begin function
              | (l', t_) ->
                  (:=) cref assign
                    (((l, Glocal_u, (u_, I.id), t_, nsub_query', assignSub,
                        cnstrSub, !cref))
                    (* = l' *)) end) end) in
  let nsub_left' =
    S.update nsub_left1
      (begin function | (l, u_) -> (l, (normalizeNExp (u_, cnstrSub))) end) in
  Some
    ((S.union nsub_query_left nsub_query'),
      ((S.union nsub_left nsub_left'), cnstrSub), !cref) in
begin try assign' (nsub_query, nsub) with | Assignment msg -> None end
let rec assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
  let nsub_query' = querySubId () in
  let cref = ref cnstr in
  let rec assign' (nsub_query, nsub) =
    let (nsub_query_left, nsub_left) =
      S.differenceModulo nsub_query nsub
        (begin function
         | (Glocal_u, (l, u_)) ->
             (begin function
              | (l', t_) ->
                  (:=) cref assign
                    (((l', Glocal_u, (u_, I.id), t_, nsub_query', assignSub,
                        cnstrSub, !cref))
                    (* = l *)) end) end) in
  let _ =
    S.forall nsub_left
      (begin function
       | (nv, (nvaronly, u_)) ->
           (begin match S.lookup cnstrSub nv with
            | None -> raise (Error "Left-over nsubstitution")
            | Some (AVar (a_)) -> (:=) a_ Some (normalizeNExp (u_, cnstrSub)) end) end) in
  ((Some ((S.union nsub_query_left nsub_query'), cnstrSub, !cref))
    (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
    (* cnstr[rsub] *)(* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)) in
begin try assign' (nsub_query, nsub) with | Assignment msg -> None end
let rec unifyW =
  begin function
  | (g_, ((AVar ({ contents = None } as r) as x_), Shift 0), us2_) ->
      (:=) r Some (I.EClo us2_)
  | (g_, ((AVar ({ contents = None } as r) as x_), s), ((u_, s2) as us2_)) ->
      (begin print "unifyW -- not s = Id\n";
       print (((^) "Us2 = " Print.expToString (g_, (I.EClo us2_))) ^ "\n");
       (:=) r Some (I.EClo us2_) end)
  | (g_, xs1_, us2_) -> Unify.unifyW (g_, xs1_, us2_) end(* Xs1 should not contain any uninstantiated AVar anymore *)
let rec unify (g_, xs1_, us2_) =
  unifyW (g_, (Whnf.whnf xs1_), (Whnf.whnf us2_))
let rec unifiable (g_, us1_, us2_) =
  begin try begin unify (g_, us1_, us2_); true end with | Unify msg -> false end
let rec ctxToExplicitSub =
  begin function
  | (i, Gquery, I.Null, asub) -> I.id
  | (i, Gquery, Decl (Gclause, Dec (_, a_)), asub) ->
      let s = ctxToExplicitSub ((i + 1), Gquery, Gclause, asub) in
      let EVar (x'_, _, _, _) as u'_ = I.newEVar (Gquery, (I.EClo (a_, s))) in
      (begin (begin match S.lookup asub i with
              | None -> ()
              | Some (Assign (Glocal_u, u_)) ->
                  (:=) x'_ Some (raiseType (Glocal_u, u_)) end);
        I.Dot ((I.Exp u'_), s) end)
  | (i, Gquery, Decl (Gclause, ADec (_, d)), asub) ->
      let AVar (x'_) as u'_ = I.newAVar () in
      (((begin (begin match S.lookup asub i with
                | None -> ()
                | Some (Assign (Glocal_u, u_)) -> (:=) x'_ Some u_ end);
        I.Dot
          ((I.Exp (I.EClo (u'_, (I.Shift (- d))))),
            (ctxToExplicitSub ((i + 1), Gquery, Gclause, asub))) end))
  (* d = I.ctxLength Glocal_u *)) end
let rec solveAuxG =
  begin function
  | (C.Trivial, s, Gquery) -> true
  | (UnifyEq (Glocal, e1, n_, eqns), s, Gquery) ->
      let g_ = compose' (Glocal, Gquery) in
      let s' = shift (Glocal, s) in
      if unifiable (g_, (n_, s'), (e1, s'))
      then begin solveAuxG (eqns, s, Gquery) end else begin false end end
(* succeed *)
let rec solveCnstr =
  begin function
  | (Gquery, Gclause, [], s) -> true
  | (Gquery, Gclause, (Eqn (Glocal, u1_, u2_))::Cnstr, s) ->
      (Unify.unifiable
         ((compose' (Gquery, Glocal)), (u1_, I.id),
           (u2_, (shift (Glocal, s)))))
        && (solveCnstr (Gquery, Gclause, Cnstr, s)) end
let rec solveResiduals
  (Gquery, Gclause, CGoals (AuxG, cid, ConjGoals, i), asub, cnstr', sc) =
  let s = ctxToExplicitSub (1, Gquery, Gclause, asub) in
  let success =
    (solveAuxG (AuxG, s, Gquery)) &&
      (solveCnstr (Gquery, Gclause, cnstr', s)) in
  if success
  then begin sc ((((ConjGoals, s), cid))(* B *)) end
    else begin () end
let rec ithChild (CGoals (_, _, _, i), n) = i = n
let rec retrieveChild (num, Child, nsub_query, assignSub, cnstr, Gquery, sc)
  =
  let rec retrieve =
    begin function
    | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub,
       cnstr) ->
        (((begin match assignableEager
                         (nsub, nsub_query, assignSub, cnstrSub, cnstr)
                 with
           | None -> ()
           | Some (nsub_query', cnstrSub', cnstr') ->
               ((if isId nsub_query'
                 then
                   begin (if ithChild (Residuals, !num)
                          then
                            begin solveResiduals
                                    (Gquery, Gclause, Residuals, assignSub,
                                      cnstr', sc) end
                   else begin
                     CSManager.trail
                       (begin function
                        | () ->
                            solveResiduals
                              (Gquery, Gclause, Residuals, assignSub, cnstr',
                                sc) end) end) end
    else begin raise (Error "Left-over normal substitutions!") end)
    (* cnstrSub' = empty? by invariant *)(* LCO optimization *)) end))
(* destructively updates assignSub, might initiate backtracking  *))
| (Node (nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) ->
    (((begin match assignableEager
                     (nsub, nsub_query, assignSub, cnstrSub, cnstr)
             with
       | None -> ()
       | Some (nsub_query', cnstrSub', cnstr') ->
           S.forall Children
             (begin function
              | (n, Child) ->
                  retrieve
                    (Child, nsub_query', (S.copy assignSub),
                      (S.copy cnstrSub'), cnstr') end) end))
(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
(* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)) end in
retrieve (Child, nsub_query, assignSub, (cnstrSubId ()), cnstr)
let rec retrieval (n, (Node (s, Children) as STree), g_, r, sc) =
  let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
  begin S.insert nsub_query (1, (I.Null, (Body, r)));
  S.forall Children
    (begin function
     | (_, c_) -> retrieveChild (n, c_, nsub_query, assignSub, [], g_, sc) end) end
(* s = id *)
let rec retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet) =
  let i = ref 0 in
  let rec retrieve =
    begin function
    | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub,
       (nsub_left, cnstrSub), cnstr) ->
        (((begin match assignableLazy
                         (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                           cnstr)
                 with
           | None -> ()
           | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
               ((if isId nsub_query'
                 then
                   begin (begin ((!) ((:=) i) i) + 1;
                          S.insert candSet
                            (!i,
                              (assignSub, nsub_left', cnstrSub', cnstr',
                                Gclause, Residuals));
                          () end) end
           else begin raise (Error "Left-over normal substitutions!") end)
    (* LCO optimization *)) end))
    (* destructively updates assignSub, might initiate backtracking  *))
  | (Node (nsub, Children), nsub_query, assignSub, (nsub_left, cnstrSub),
     cnstr) ->
      (((begin match assignableLazy
                       (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                         cnstr)
               with
         | None -> ()
         | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
             S.forall Children
               (begin function
                | (n, Child) ->
                    retrieve
                      (Child, nsub_query', (S.copy assignSub),
                        ((S.copy nsub_left'), (S.copy cnstrSub')), cnstr') end) end))
  (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
  (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)) end in
retrieve (Child, nsub_query, assignSub, ((nid ()), (cnstrSubId ())), cnstr)
let rec retrieveCandidates (n, (Node (s, Children) as STree), Gquery, r, sc)
  =
  let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
  let candSet = S.new_ () in
  let rec solveCandidate (i, candSet) =
    begin match S.lookup candSet i with
    | None -> ((())
        (* print "No candidate left anymore\n" ;*))
    | Some
        (((assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals))
        (* CGoals(AuxG, cid, ConjGoals, i) *)) ->
        (begin CSManager.trail
                 (begin function
                  | () ->
                      (begin S.forall nsub_left
                               (begin function
                                | (nv, (l, u_)) ->
                                    (begin match S.lookup cnstrSub nv with
                                     | None ->
                                         raise
                                           (Error "Left-over nsubstitution")
                                     | Some (AVar (a_)) -> (:=) a_ Some u_ end) end);
                  solveResiduals
                    (Gquery, Gclause, Residuals, assignSub, cnstr, sc) end) end);
    solveCandidate ((((i + 1), candSet))
      (* sc = (fn S => (O::S)) *)) end) end in
((begin S.insert nsub_query (1, (I.Null, (Body, r)));
S.forall Children
  (begin function
   | (_, c_) -> retrieveAll (n, c_, nsub_query, assignSub, [], candSet) end);
solveCandidate (1, candSet) end)
(* execute one by one all candidates : here ! *))(* s = id *)
let rec matchSig (a, g_, ((Root (Ha, s_), s) as ps), sc) =
  let (n, Tree) = Array.sub (indexArray, a) in
  ((retrieveCandidates (n, !Tree, g_, (I.EClo ps), sc))
    (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *))
let rec matchSigIt (a, g_, ((Root (Ha, s_), s) as ps), sc) =
  let (n, Tree) = Array.sub (indexArray, a) in
  retrieval (n, !Tree, g_, (I.EClo ps), sc)
let rec sProgReset () =
  begin nctr := 1;
  Array.modify
    (begin function
     | (n, Tree) ->
         (begin n := 0; (!) ((:=) Tree) (makeTree ()); (n, Tree) end) end)
  indexArray end
let rec sProgInstall (a, Head (e_, g_, Eqs, cid), r_) =
  let (n, Tree) = Array.sub (indexArray, a) in
  let nsub_goal = S.new_ () in
  begin S.insert nsub_goal (1, (Body, e_));
  (:=) Tree insert
    (!Tree, nsub_goal, (g_, (CGoals (Eqs, cid, r_, (!n + 1)))));
  ((!) ((:=) n) n) + 1 end
let sProgReset = sProgReset
let sProgInstall = sProgInstall
let matchSig = matchSigIt end
