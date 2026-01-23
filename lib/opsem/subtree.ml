module type MEMOTABLE  =
  sig
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ *
        TableParam.resEqn_) -> TableParam.callCheckResult
    val answerCheck :
      (IntSyn.sub_ * TableParam.answer * CompSyn.pskeleton) ->
        TableParam.answState
    val reset : unit -> unit
    val updateTable : unit -> bool
    val tableSize : unit -> int
  end


module MemoTable(MemoTable:sig
                             module Conv : CONV
                             module Whnf : WHNF
                             module AbstractTabled : ABSTRACTTABLED
                             module Print : PRINT
                           end) : MEMOTABLE =
  struct
    module AbstractTabled = AbstractTabled
    type nonrec normalSubsts = IntSyn.exp_ RBSet.ordSet
    type nonrec exSubsts = IntSyn.exp_ RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new_
    let aid = TableParam.aid
    let (existId : unit -> normalSubsts) = RBSet.new_
    let rec isId s = RBSet.isEmpty s
    type nonrec ctx = (int * IntSyn.dec_) list ref
    let rec emptyCtx () = (ref [] : ctx)
    let rec copy (l_) = (ref !l_ : ctx)
    let rec delete (x, (l_ : ctx)) =
      let rec del =
        begin function
        | (x, [], l_) -> None
        | (x, ((y, e_) as h_)::l_, l'_) ->
            if x = y then begin Some ((y, e_), ((rev l'_) @ l_)) end
            else begin del (x, l_, (h_ :: l'_)) end end in
  begin match del (x, !l_, []) with
  | None -> None
  | Some ((y, e_), l'_) -> (begin l_ := l'_; Some (y, e_) end) end
let rec member (x, (l_ : ctx)) =
  let rec memb =
    begin function
    | (x, []) -> None
    | (x, ((y, e_)::l_ as h_)) -> if x = y then begin Some (y, e_) end
        else begin memb (x, l_) end end in
memb (x, !l_)
let rec insertList (e_, l_) = begin l_ := (e_ :: !l_); l_ end
let rec ctxToEVarSub =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, Dec (_, a_)), s) ->
      let s' = ctxToEVarSub (g_, s) in
      let x_ = IntSyn.newEVar (IntSyn.Null, (IntSyn.EClo (a_, s'))) in
      IntSyn.Dot ((IntSyn.Exp x_), s') end
type tree_ =
  | Leaf of ((ctx * normalSubsts) *
  ((((((int * int))(* #G *)(* #EVar *)) *
      IntSyn.dctx * TableParam.resEqn_ * TableParam.answer * int *
      TableParam.status_))(* G *))
  list ref) 
  | Node of ((ctx * normalSubsts) * tree_ ref list) 
let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
let rec noChildren (c_) = c_ = []
type retrieval_ =
  | Variant of IntSyn.exp_ 
  | NotCompatible 
type compSub_ =
  | SplitSub of ((((ctx * normalSubsts))(* sigma *)) *
  (((ctx * normalSubsts))(* rho1 *)) *
  (((ctx * normalSubsts))(* rho2 *))) 
  | VariantSub of
  (((ctx * normalSubsts))(* normalSubsts * *)(* rho2 *))
  
  | NoCompatibleSub 
let indexArray =
  Array.tabulate
    (Global.maxCid, (begin function | i -> ((ref 0), (makeTree ())) end))
exception Error of string 
module I = IntSyn
module C = CompSyn
module S = RBSet
module A = AbstractTabled
module T = TableParam
exception Assignment of string 
exception Generalization of string 
exception DifferentSpines 
let rec emptyAnswer () = T.emptyAnsw ()
let (answList : TableParam.answer list ref) = ref []
let added = ref false
type nonrec nvar = int
type nonrec bvar = int
type nonrec bdepth = int
let rec cidFromHead = begin function | Const c -> c | Def c -> c end
let rec dotn =
  begin function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s)) end
let rec compose =
  begin function
  | (IntSyn.Null, g_) -> g_
  | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose (g_, g'_)), d_) end
let rec shift =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec raiseType =
  begin function
  | (I.Null, u_) -> u_
  | (Decl (g_, d_), u_) -> raiseType (g_, (I.Lam (d_, u_))) end
let rec ctxToAVarSub =
  begin function
  | (g'_, I.Null, s) -> s
  | (g'_, Decl (d_, Dec (_, a_)), s) ->
      let EVar (r, _, _, cnstr) as e_ = I.newEVar (I.Null, a_) in
      I.Dot ((I.Exp e_), (ctxToAVarSub (g'_, d_, s)))
  | (g'_, Decl (d_, ADec (_, d)), s) ->
      let x_ = I.newAVar () in
      I.Dot
        ((I.Exp (I.EClo (x_, (I.Shift (- d))))), (ctxToAVarSub (g'_, d_, s))) end
let rec solveEqn' =
  begin function
  | ((T.Trivial, s), g_) -> true
  | ((Unify (((g'_, e1, n_, eqns))(* evar *)), s), g_) ->
      let G'' = compose (g'_, g_) in
      let s' = shift (g'_, s) in
      (Assign.unifiable (G'', (n_, s'), (e1, s'))) &&
        (solveEqn' ((eqns, s), g_)) end
let nctr = ref 1
let rec newNVar () = begin ((!) ((:=) nctr) nctr) + 1; I.NVar !nctr end
let rec equalDec =
  begin function
  | (Dec (_, u_), Dec (_, u'_)) -> Conv.conv ((u_, I.id), (u'_, I.id))
  | (ADec (_, d), ADec (_, d')) -> d = d'
  | (_, _) -> false end
let rec equalCtx =
  begin function
  | (I.Null, s, I.Null, s') -> true
  | (Decl (g_, d_), s, Decl (g'_, d'_), s') ->
      (Conv.convDec ((d_, s), (d'_, s'))) &&
        (equalCtx (g_, (I.dot1 s), g'_, (I.dot1 s')))
  | (_, _, _, _) -> false end
let rec equalEqn =
  begin function
  | (T.Trivial, T.Trivial) -> true
  | (Unify (g_, x_, n_, eqn), Unify (g'_, x'_, n'_, eqn')) ->
      (equalCtx (g_, I.id, g'_, I.id)) &&
        ((Conv.conv ((x_, I.id), (x'_, I.id))) &&
           ((Conv.conv ((n_, I.id), (n'_, I.id))) && (equalEqn (eqn, eqn'))))
  | (_, _) -> false end
let rec equalSub =
  begin function
  | (Shift k, Shift k') -> k = k'
  | (Dot (f_, s_), Dot (f'_, s'_)) ->
      (equalFront (f_, f'_)) && (equalSub (s_, s'_))
  | (Dot (f_, s_), Shift k) -> false
  | (Shift k, Dot (f_, s_)) -> false end
let rec equalFront =
  begin function
  | (Idx n, Idx n') -> n = n'
  | (Exp (u_), Exp (v_)) -> Conv.conv ((u_, I.id), (v_, I.id))
  | (I.Undef, I.Undef) -> true end
let rec equalSub1 (Dot (ms, s), Dot (ms', s')) = equalSub (s, s')
let rec equalCtx' =
  begin function
  | (I.Null, I.Null) -> true
  | (Decl (Dk, Dec (_, a_)), Decl (d1_, Dec (_, a1_))) ->
      (Conv.conv ((a_, I.id), (a1_, I.id))) && (equalCtx' (Dk, d1_))
  | (Decl (Dk, ADec (_, d')), Decl (d1_, ADec (_, d))) ->
      (d = d') && (equalCtx' (Dk, d1_))
  | (_, _) -> false end
let rec compareCtx (g_, g'_) = equalCtx' (g_, g'_)
let rec isExists (d, BVar k, d_) = member ((k - d), d_)
let rec compHeads =
  begin function
  | ((D_1, Const k), (D_2, Const k')) -> k = k'
  | ((D_1, Def k), (D_2, Def k')) -> k = k'
  | ((D_1, BVar k), (D_2, BVar k')) ->
      (begin match isExists (0, (I.BVar k), D_1) with
       | None -> k = k'
       | Some (x, Dec) -> true end)
  | ((D_1, BVar k), (D_2, h2_)) ->
      (begin match isExists (0, (I.BVar k), D_1) with
       | None -> false
       | Some (x, Dec) -> true end)
  | ((D_1, h1_), (D_2, h2_)) -> false end
let rec compatible' ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) =
  let rec genNVar ((rho_t, t_), (rho_u, u_)) =
    begin S.insert rho_t ((!nctr + 1), t_);
    S.insert rho_u ((!nctr + 1), u_);
    newNVar () end in
let rec genRoot =
  begin function
  | (depth, (Root ((Const k as h1_), s1_) as t_),
     (Root (Const k', s2_) as u_)) ->
      if k = k'
      then begin let s'_ = genSpine (depth, s1_, s2_) in I.Root (h1_, s'_) end
      else begin genNVar ((rho_t, t_), (rho_u, u_)) end
| (depth, (Root ((Def k as h1_), s1_) as t_), (Root (Def k', s2_) as u_)) ->
    if k = k'
    then begin let s'_ = genSpine (depth, s1_, s2_) in I.Root (h1_, s'_) end
    else begin genNVar ((rho_t, t_), (rho_u, u_)) end
  | (d, (Root ((BVar k as h1_), s1_) as t_), (Root (BVar k', s2_) as u_)) ->
      ((if (k > d) && (k' > d)
        then
          begin let k1 = k - d in
                let k2 = k' - d in
                (((begin match ((member (k1, D_t)), (member (k2, D_u))) with
                   | (None, None) ->
                       if k1 = k2
                       then
                         begin (begin try
                                        let s'_ = genSpine (d, s1_, s2_) in
                                        I.Root (h1_, s'_)
                                with
                                | DifferentSpine ->
                                    genNVar ((rho_t, t_), (rho_u, u_)) end) end
                   else begin genNVar ((rho_t, t_), (rho_u, u_)) end
          | (Some (x, Dec1), Some (x', Dec2)) ->
              ((if (k1 = k2) && (equalDec (Dec1, Dec2))
                then
                  begin let s'_ = genSpine (d, s1_, s2_) in
                        (((begin delete (x, D_t);
                           delete (x', D_u);
                           insertList ((x, Dec1), ds_);
                           I.Root (h1_, s'_) end))
                  (* this is unecessary -- since existential variables have the same type
                                and need to be fully applied in order, S1 = S2 *)) end
          else begin genNVar ((rho_t, t_), (rho_u, u_)) end)
      (* they refer to the same existential variable *)
      (* variant checking only *))
  | (_, _) -> genNVar ((rho_t, t_), (rho_u, u_)) end))
(* k, k' refer to the existential *)) end
else begin
  if k = k'
  then
    begin (begin try let s'_ = genSpine (d, s1_, s2_) in I.Root (h1_, s'_)
           with | DifferentSpines -> genNVar ((rho_t, t_), (rho_u, u_)) end) end
else begin genNVar ((rho_t, t_), (rho_u, u_)) end end)
(* globally bound variable *)(* locally bound variables *))
| (d, (Root ((BVar k as h1_), s1_) as t_), (Root (Const k', s2_) as u_)) ->
    genNVar ((rho_t, t_), (rho_u, u_))
| (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
    genNVar ((rho_t, t_), (rho_u, u_)) end
and genExp =
  begin function
  | (d, (NVar n as t_), (Root (h_, s_) as u_)) ->
      (begin S.insert rho_u (n, u_); t_ end)
  | (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
      genRoot (d, (I.Root (h1_, s1_)), (I.Root (h2_, s2_)))
  | (d, Lam ((Dec (_, a1_) as d1_), t1_), Lam ((Dec (_, a2_) as d2_), u2_))
      -> let e_ = genExp ((d + 1), t1_, u2_) in I.Lam (d1_, e_)
  | (d, t_, u_) ->
      (begin print "genExp -- falls through?\n";
       genNVar ((rho_t, t_), (rho_u, u_)) end) end(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
(* by invariant A1 = A2 *)
and genSpine =
  begin function
  | (d, I.Nil, I.Nil) -> I.Nil
  | (d, App (t_, s1_), App (u_, s2_)) ->
      let e_ = genExp (d, t_, u_) in
      let s'_ = genSpine (d, s1_, s2_) in I.App (e_, s'_)
  | (d, I.Nil, App (_, _)) -> raise DifferentSpines
  | (d, App (_, _), I.Nil) -> raise DifferentSpines
  | (d, SClo (_, _), _) -> raise DifferentSpines
  | (d, _, SClo (_, _)) -> raise DifferentSpines end in
let e_ = genExp (0, t_, u_) in Variant e_
let rec compatible =
  begin function
  | ((D_t, (Root (h1_, s1_) as t_)), (D_u, (Root (h2_, s2_) as u_)), ds_,
     rho_t, rho_u) ->
      if compHeads ((D_t, h1_), (D_u, h2_))
      then begin compatible' ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) end
      else begin NotCompatible end
  | ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) ->
      compatible' ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) end
let rec compatibleSub ((D_t, nsub_t), (D_u, nsub_u)) =
  let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
  let Dsigma = emptyCtx () in
  let D_r1 = copy D_t in
  let D_r2 = copy D_u in
  let choose = ref (begin function | (match_ : bool) -> () end) in
  let _ =
    S.forall nsub_u
      (begin function
       | (nv, u_) ->
           (((begin match S.lookup nsub_t nv with
              | Some (t_) ->
                  (begin match compatible
                                 ((D_r1, t_), (D_r2, u_), Dsigma, rho_t,
                                   rho_u)
                         with
                   | NotCompatible ->
                       (begin S.insert rho_t (nv, t_);
                        S.insert rho_u (nv, u_) end)
                  | Variant (t'_) ->
                      let restc = !choose in
                      (begin S.insert sigma (nv, t'_);
                       choose :=
                         ((begin function
                           | match_ ->
                               (begin restc match_;
                                if match_ then begin () end
                                else begin () end end) end)) end) end)
    | None -> S.insert rho_u (nv, u_) end))
    (* note by invariant Glocal_e ~ Glocal_t *)(* here Glocal_t will be only approximately correct! *)) end) in
((if isId rho_t
then begin (begin (!) choose true; VariantSub (D_r2, rho_u) end) end
else begin
  (((begin (!) choose false;
     if isId sigma then begin NoCompatibleSub end
     else begin SplitSub ((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)) end end))
(* split -- asub is unchanged *)) end)
(* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
(* by invariant rho_t = empty, since nsub_t <= nsub_u *)
(* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *))
let rec mkLeaf (ds_, GR, n) = Leaf (ds_, GR)
let rec mkNode =
  begin function
  | (Node (_, Children), Dsigma, Drho1, GR, Drho2) ->
      Node
        (Dsigma,
          [ref (Leaf (Drho2, (ref [GR]))); ref (Node (Drho1, Children))])
  | (Leaf (c, GRlist), Dsigma, Drho1, GR2, Drho2) ->
      Node
        (Dsigma,
          [ref (Leaf (Drho2, (ref [GR2]))); ref (Leaf (Drho1, GRlist))]) end
let rec compatibleCtx =
  begin function
  | ((g_, eqn), []) -> None
  | ((g_, eqn), (l', g'_, eqn', answRef', _, status')::GRlist) ->
      if (equalCtx' (g_, g'_)) && (equalEqn (eqn, eqn'))
      then begin Some (l', answRef', status') end
      else begin compatibleCtx ((g_, eqn), GRlist) end end(* we may not need to check that the DAVars are the same *)
let rec compChild =
  begin function
  | ((Leaf ((D_t, nsub_t), GList) as n_), (D_e, nsub_e)) ->
      compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
  | ((Node ((D_t, nsub_t), Children') as n_), (D_e, nsub_e)) ->
      compatibleSub ((D_t, nsub_t), (D_e, nsub_e)) end
let rec findAllCandidates (G_r, children, ds_) =
  let rec findAllCands =
    begin function
    | (G_r, [], (D_u, sub_u), VList, SList) -> (VList, SList)
    | (G_r, x::l_, (D_u, sub_u), VList, SList) ->
        (begin match compChild (!x, (D_u, sub_u)) with
         | NoCompatibleSub ->
             findAllCands (G_r, l_, (D_u, sub_u), VList, SList)
         | SplitSub (Dsigma, Drho1, Drho2) ->
             findAllCands
               (G_r, l_, (D_u, sub_u), VList,
                 ((x, (Dsigma, Drho1, Drho2)) :: SList))
         | VariantSub ((D_r2, rho2) as Drho2) ->
             findAllCands
               (G_r, l_, (D_u, sub_u), ((x, Drho2, I.id) :: VList), SList) end) end in
findAllCands (G_r, children, ds_, [], [])
let rec divergingCtx (stage, g_, GRlistRef) =
  let l = I.ctxLength g_ in
  List.exists
    (begin function
     | ((evar, l), g'_, _, _, stage', _) ->
         (stage = stage') && (l > (I.ctxLength g'_)) end)
    !GRlistRef
let rec eqHeads =
  begin function
  | (Const k, Const k') -> k = k'
  | (BVar k, BVar k') -> k = k'
  | (Def k, Def k') -> k = k'
  | (_, _) -> false end
let rec eqTerm =
  begin function
  | (Root (h2_, s2_), ((Root (h_, s_) as t), rho1)) ->
      if eqHeads (h2_, h_) then begin eqSpine (s2_, (s_, rho1)) end
      else begin false end
  | (t2_, (NVar n, rho1)) ->
      (begin match S.lookup rho1 n with
       | None -> false
       | Some (t1_) -> eqTerm (t2_, (t1_, (nid ()))) end)
| (Lam (d2_, t2_), (Lam (d_, t_), rho1)) -> eqTerm (t2_, (t_, rho1))
| (_, (_, _)) -> false end
let rec eqSpine =
  begin function
  | (I.Nil, (I.Nil, rho1)) -> true
  | (App (t2_, s2_), (App (t_, s_), rho1)) ->
      (eqTerm (t2_, (t_, rho1))) && (eqSpine (s2_, (s_, rho1)))
  | (_, _) -> false end
let rec divergingSub ((ds_, sigma), (Dr1, rho1), (Dr2, rho2)) =
  S.exists rho2
    (begin function
     | (n2, t2) ->
         S.exists sigma
           (begin function | (_, t) -> eqTerm (t2, (t, rho1)) end) end)
let rec insert (Nref, (D_u, nsub_u), GR) =
  let rec insert' =
    begin function
    | ((Leaf ((d_, _), GRlistRef) as n_), (D_u, nsub_u),
       (((evarl, l), G_r, eqn, answRef, stage, status) as GR)) ->
        (begin match compatibleCtx ((G_r, eqn), !GRlistRef) with
         | None ->
             ((if
                 !TableParam.divHeuristic &&
                   (divergingCtx (stage, G_r, GRlistRef))
               then
                 begin (((((begin function
                            | () ->
                                (begin GRlistRef := (GR :: !GRlistRef);
                                 answList := (answRef :: !answList) end) end)),
               (T.DivergingEntry (I.id, answRef))))
             (* ctx are diverging --- force suspension *)) end
        else begin
          (((begin function
             | () ->
                 (begin GRlistRef := (GR :: !GRlistRef);
                  answList := (answRef :: !answList) end) end)),
        (T.NewEntry answRef)) end)
  (* compatible path (variant) -- ctx are different *)
  (* compatible path -- but different ctx! *))
  | Some ((evarl', Glength), answRef', status') ->
      (((((begin function | () -> () end)),
      (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
  (* compatible path -- SAME ctx *)) end)
| ((Node ((d_, sub), children) as n_), (D_u, nsub_u),
   ((l, G_r, eqn, answRef, stage, status) as GR)) ->
    let (VariantCand, SplitCand) =
      findAllCandidates (G_r, children, (D_u, nsub_u)) in
    let rec checkCandidates =
      begin function
      | ([], []) ->
          (((((begin function
               | () ->
                   (begin (:=) Nref Node
                            ((d_, sub),
                              ((ref (Leaf ((D_u, nsub_u), (ref [GR])))) ::
                                 children));
                    answList := (answRef :: !answList) end) end)),
      (T.NewEntry answRef)))
      (* no child is compatible with nsub_u *))
      | ([], (ChildRef, (Dsigma, Drho1, Drho2))::_) ->
          if
            !TableParam.divHeuristic && (divergingSub (Dsigma, Drho1, Drho2))
          then
            begin (((((begin function
                       | () ->
                           (begin (:=) ChildRef mkNode
                                    (!ChildRef, Dsigma, Drho1, GR, Drho2);
                            answList := (answRef :: !answList) end) end)),
          (T.DivergingEntry (I.id, answRef))))
          (* substree divering -- splitting node *)) end
      else begin
        (((((begin function
             | () ->
                 (begin (:=) ChildRef mkNode
                          (!ChildRef, Dsigma, Drho1, GR, Drho2);
                  answList := (answRef :: !answList) end) end)),
      (T.NewEntry answRef)))
    (* split existing node *)) end
| ((ChildRef, Drho2, asub)::[], _) -> insert (ChildRef, Drho2, GR)
| ((ChildRef, Drho2, asub)::l_, SCands) ->
    (begin match insert (ChildRef, Drho2, GR) with
     | (_, NewEntry answRef) -> checkCandidates (l_, SCands)
     | (f, RepeatedEntry (asub, answRef, status)) ->
         (f, (T.RepeatedEntry (asub, answRef, status)))
     | (f, DivergingEntry (asub, answRef)) ->
         (f, (T.DivergingEntry (asub, answRef))) end) end(* there are several "perfect" candidates *)
(* unique "perfect" candidate (left) *)(* split an existing node *) in
checkCandidates (VariantCand, SplitCand) end(* need to compare D and D_u *) in
insert' (!Nref, (D_u, nsub_u), GR)
let rec answCheckVariant (s', answRef, o_) =
  let rec member =
    begin function
    | ((d_, sk), []) -> false
    | ((d_, sk), ((d1_, s1), _)::s_) ->
        if (equalSub (sk, s1)) && (equalCtx' (d_, d1_)) then begin true end
        else begin member ((d_, sk), s_) end end in
let (DEVars, sk) = A.abstractAnswSub s' in
if member ((DEVars, sk), (T.solutions answRef)) then begin T.repeated end
else begin (begin T.addSolution (((DEVars, sk), o_), answRef); T.new_ end) end
let rec reset () =
  begin nctr := 1;
  Array.modify
    (begin function
     | (n, Tree) ->
         (begin n := 0;
          (!) ((:=) Tree) (makeTree ());
          answList := [];
          added := false;
          (n, Tree) end) end)
  indexArray end
let rec makeCtx =
  begin function
  | (n, I.Null, (DEVars : ctx)) -> n
  | (n, Decl (g_, d_), (DEVars : ctx)) ->
      (begin insertList ((n, d_), DEVars); makeCtx ((n + 1), g_, DEVars) end) end
let rec callCheck (a, DAVars, DEVars, g_, u_, eqn, status) =
  let (n, Tree) = Array.sub (indexArray, a) in
  let nsub_goal = S.new_ () in
  let DAEVars = compose (DEVars, DAVars) in
  let d_ = emptyCtx () in
  let n = I.ctxLength g_ in
  let _ = makeCtx ((n + 1), DAEVars, (d_ : ctx)) in
  let l = I.ctxLength DAEVars in
  let _ = S.insert nsub_goal (1, u_) in
  let result =
    insert
      (Tree, (d_, nsub_goal),
        ((l, (n + 1)), g_, eqn, (emptyAnswer ()), !TableParam.stageCtr,
          status)) in
  let esub = ctxToAVarSub (g_, DAEVars, (I.Shift 0)) in
  let _ = if solveEqn' ((eqn, (shift (g_, esub))), g_) then begin () end
    else begin print " failed to solve eqn_query\n" end in
  begin match result with
  | (sf, NewEntry answRef) ->
      (begin sf ();
       added := true;
       if !Global.chatter >= 5 then begin print "\t -- Add goal \n" end
       else begin () end;
  T.NewEntry answRef end)
    | (_, RepeatedEntry (((_, asub) as s), answRef, status)) ->
        (begin if !Global.chatter >= 5
               then begin print "\t -- Suspend goal\n" end
         else begin () end;
    T.RepeatedEntry ((esub, asub), answRef, status) end)
    | (sf, DivergingEntry answRef) ->
        (begin sf ();
         added := true;
         if !Global.chatter >= 5
         then begin print "\t -- Add diverging goal\n" end
         else begin () end;
    T.DivergingEntry answRef end) end
let rec insertIntoTree (a, DAVars, DEVars, g_, u_, eqn, answRef, status) =
  let (n, Tree) = Array.sub (indexArray, a) in
  let nsub_goal = S.new_ () in
  let DAEVars = compose (DEVars, DAVars) in
  let d_ = emptyCtx () in
  let n = I.ctxLength g_ in
  let _ = makeCtx ((n + 1), DAEVars, (d_ : ctx)) in
  let l = I.ctxLength DAEVars in
  let _ = S.insert nsub_goal (1, u_) in
  let result =
    insert
      (Tree, (d_, nsub_goal),
        ((l, (n + 1)), g_, eqn, answRef, !TableParam.stageCtr, status)) in
  begin match result with
  | (sf, NewEntry answRef) ->
      (begin added := true;
       if !Global.chatter >= 5 then begin print "\t -- Add goal \n" end
       else begin () end;
  T.NewEntry answRef end)
    | (_, RepeatedEntry (asub, answRef, status)) ->
        (begin if !Global.chatter >= 5
               then begin print "\t -- Suspend goal\n" end
         else begin () end;
    T.RepeatedEntry (asub, answRef, status) end)
    | (sf, DivergingEntry answRef) ->
        (begin sf ();
         added := true;
         if !Global.chatter >= 5
         then begin print "\t -- Add diverging goal\n" end
         else begin () end;
    T.DivergingEntry answRef end) end
let rec answCheck (s', answRef, o_) = answCheckVariant (s', answRef, o_)
let rec updateTable () =
  let rec update arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | ([], Flag) -> Flag
    | (answRef::AList, Flag) ->
        let l = length (T.solutions answRef) in
        ((if (=) l T.lookup answRef then begin update AList Flag end
          else begin
            (begin T.updateAnswLookup (l, answRef); update AList true end) end)
    (* no new solutions were added in the previous stage *)
    (* new solutions were added *)) end in
let Flag = update !answList false in
let r = Flag || !added in begin added := false; r end
let reset = reset
let callCheck =
  begin function
  | (DAVars, DEVars, g_, u_, eqn, status) ->
      callCheck
        ((cidFromHead (I.targetHead u_)), DAVars, DEVars, g_, u_, eqn,
          status) end
let insertIntoTree =
  begin function
  | (DAVars, DEVars, g_, u_, eqn, answRef, status) ->
      insertIntoTree
        ((cidFromHead (I.targetHead u_)), DAVars, DEVars, g_, u_, eqn,
          answRef, status) end
let answerCheck = answCheck
let updateTable = updateTable
let tableSize = begin function | () -> length !answList end
let rec memberCtx ((g_, v_), g'_) =
  let rec memberCtx' =
    begin function
    | ((g_, v_), I.Null, n) -> None
    | ((g_, v_), Decl (g'_, (Dec (_, v'_) as d'_)), n) ->
        if Conv.conv ((v_, I.id), (v'_, (I.Shift n))) then begin Some d'_ end
        else begin memberCtx' ((g_, v_), g'_, (n + 1)) end end in
memberCtx' ((g_, v_), g'_, 1) end
