module MemoTableInst(MemoTableInst:sig
                                     module Conv : CONV
                                     module Whnf : WHNF
                                     module Match : MATCH
                                     module Assign : ASSIGN
                                     module AbstractTabled : ABSTRACTTABLED
                                     module Print : PRINT
                                   end) : MEMOTABLE =
  struct
    module AbstractTabled = AbstractTabled
    type nonrec normalSubsts =
      (((int * IntSyn.exp_))(* local depth *)) RBSet.ordSet
    type nonrec exSubsts = IntSyn.front_ RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new_
    let (asid : unit -> exSubsts) = RBSet.new_
    let aid = TableParam.aid
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
    | (x, ((y, (Dec (n, u_) as e_))::l_ as h_)) ->
        if x = y then begin Some (y, e_) end else begin memb (x, l_) end
    | (x, ((y, (ADec (n, d) as e_))::l_ as h_)) ->
        if x = y then begin Some (y, e_) end else begin memb (x, l_) end end in
memb (x, !l_)
let rec insertList (e_, l_) = l_ := (e_ :: !l_)
type tree_ =
  | Leaf of ((ctx * normalSubsts) *
  ((((((int * int))(* #G *)(* #EVar *)) *
      ctx * IntSyn.dctx * TableParam.resEqn_ * TableParam.answer * int *
      TableParam.status_))(* G *)(* D *))
  list ref) 
  | Node of ((ctx * normalSubsts) * tree_ ref list) 
let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
let rec noChildren (c_) = c_ = []
type retrieval_ =
  | Variant of (int * IntSyn.exp_) 
  | NotCompatible 
type compSub_ =
  | SplitSub of ((((ctx * normalSubsts))(* sigma *)) *
  (((ctx * normalSubsts))(* rho1 *)) *
  (((ctx * normalSubsts))(* rho2 *))) 
  | InstanceSub of (exSubsts *
  (((ctx * normalSubsts))(* rho2 *))) 
  | VariantSub of (((ctx * normalSubsts))(* rho2 *)) 
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
exception Instance of string 
exception Generalization of string 
exception DifferentSpines 
let rec emptyAnswer () = T.emptyAnsw ()
let (answList : TableParam.answer list ref) = ref []
let added = ref false
type nonrec nvar = int
type nonrec bvar = int
type nonrec bdepth = int
let rec expToS (g_, u_) =
  begin try Print.expToString (g_, u_) with | _ -> " <_ >" end
let rec printSub =
  begin function
  | (g_, Shift n) -> print (((^) "I.Shift " Int.toString n) ^ "\n")
  | (g_, Dot (Idx n, s)) ->
      (begin print (((^) "Idx " Int.toString n) ^ " . "); printSub (g_, s) end)
  | (g_, Dot (Exp (EVar ({ contents = Some (u_) }, _, _, _) as x_), s)) ->
      (begin print (((^) "Exp ( EVar " expToS (g_, x_)) ^ ").");
       printSub (g_, s) end)
  | (g_, Dot (Exp (EVar (_, _, _, _) as x_), s)) ->
      (begin print (((^) "Exp ( EVar  " expToS (g_, x_)) ^ ").");
       printSub (g_, s) end)
| (g_, Dot (Exp (AVar _), s)) ->
    (begin print "Exp (AVar _ ). "; printSub (g_, s) end)
| (g_, Dot (Exp (EClo (AVar { contents = Some (u_) }, s')), s)) ->
    (begin print (((^) "Exp (AVar " expToS (g_, (I.EClo (u_, s')))) ^ ").");
     printSub (g_, s) end)
| (g_, Dot
   (Exp (EClo (EVar ({ contents = Some (u_) }, _, _, _), s') as x_), s)) ->
    (begin print
             (((^) "Exp (EVarClo " expToS (g_, (I.EClo (u_, s')))) ^ ") ");
     printSub (g_, s) end)
| (g_, Dot (Exp (EClo (u_, s') as x_), s)) ->
    (begin print
             (((^) "Exp (EClo " expToS (g_, (Whnf.normalize (u_, s')))) ^
                ") ");
     printSub (g_, s) end)
| (g_, Dot (Exp (e_), s)) ->
    (begin print (((^) "Exp ( " expToS (g_, e_)) ^ " ). "); printSub (g_, s) end)
| (g_, Dot (I.Undef, s)) -> (begin print "Undef . "; printSub (g_, s) end) end
let rec normalizeSub =
  begin function
  | Shift n -> I.Shift n
  | Dot (Exp (EClo (AVar { contents = Some (u_) }, s')), s) ->
      I.Dot ((I.Exp (Whnf.normalize (u_, s'))), (normalizeSub s))
  | Dot (Exp (EClo (EVar ({ contents = Some (u_) }, _, _, _), s')), s) ->
      I.Dot ((I.Exp (Whnf.normalize (u_, s'))), (normalizeSub s))
  | Dot (Exp (u_), s) ->
      I.Dot ((I.Exp (Whnf.normalize (u_, I.id))), (normalizeSub s))
  | Dot (Idx n, s) -> I.Dot ((I.Idx n), (normalizeSub s)) end
let rec etaSpine =
  begin function
  | (I.Nil, n) -> n = 0
  | (App (Root (BVar k, I.Nil), s_), n) ->
      (k = n) && (etaSpine (s_, (n - 1)))
  | (App (a_, s_), n) -> false end
let rec cidFromHead = begin function | Const c -> c | Def c -> c end
let rec dotn =
  begin function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s)) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Lam (d_, v_))) end
let rec compose =
  begin function
  | (IntSyn.Null, g_) -> g_
  | (Decl (g'_, d_), g_) -> IntSyn.Decl ((compose (g'_, g_)), d_) end
let rec shift =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec ctxToEVarSub =
  begin function
  | (I.Null, s) -> s
  | (Decl (g_, Dec (_, a_)), s) ->
      let x_ = I.newEVar (I.Null, a_) in
      I.Dot ((I.Exp x_), (ctxToEVarSub (g_, s))) end
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
let rec assign =
  begin function
  | (((d, (Dec (n, v_) as Dec1), (Root (BVar k, s1_) as e1_), u_, asub))
      (* total as (t, passed)*)) ->
      let EVar (r, _, _, cnstr) as e_ = I.newEVar (I.Null, v_) in
      let x_ =
        lowerEVar1
          (e_, (I.EVar (r, I.Null, v_, cnstr)), (Whnf.whnf (v_, I.id))) in
      let _ = (:=) r Some u_ in S.insert asub ((k - d), (I.Exp x_))
  | (((d, (ADec (n, d') as Dec1), (Root (BVar k, s1_) as e1_), u_, asub))
      (* total as (t, passed)*)) ->
      let AVar r as a_ = I.newAVar () in
      let _ = (:=) r Some u_ in
      let us_ = Whnf.whnf (u_, (I.Shift (- d'))) in
      S.insert asub ((k - d), (I.Exp (I.EClo (a_, (I.Shift (- d')))))) end
(* it is an Avar and d = d' (k-d, AVar(SOME(U)) *)(* it is an evar -- (k-d, EVar (SOME(U), V)) *)
let rec assignExp =
  begin function
  | (fasub, (((r, passed) as ctxTotal), d), (d1_, (Root (h1_, s1_) as u1_)),
     (d2_, (Root (h2_, s2_) as u2_))) ->
      (((begin match (h1_, h2_) with
         | (Const c1, Const c2) ->
             if c1 = c2
             then
               begin assignSpine
                       (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_)) end
             else begin raise (Assignment "Constant clash") end
  | (Def c1, Def c2) ->
      if c1 = c2
      then begin assignSpine (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_)) end
      else begin
        (let U1' = Whnf.normalize (Whnf.expandDef (u1_, I.id)) in
         let U2' = Whnf.normalize (Whnf.expandDef (u2_, I.id)) in
         assignExp (fasub, (ctxTotal, d), (d1_, U1'), (d2_, U2'))) end
  | (Def c1, _) ->
      let U1' = Whnf.normalize (Whnf.expandDef (u1_, I.id)) in
      assignExp (fasub, (ctxTotal, d), (d1_, U1'), (d2_, u2_))
  | (_, Def c2) ->
      let U2' = Whnf.normalize (Whnf.expandDef (u2_, I.id)) in
      assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, U2'))
  | (BVar k1, BVar k2) ->
      ((if k1 <= (r + d)
        then
          begin (((if k2 <= (r + d)
                   then begin (if k2 = k1 then begin fasub end
                     else begin raise (Assignment "BVar clash") end) end
      else begin raise (Assignment "BVar - EVar clash") end))
(* k2 is globally bound *)) end
else begin
  (begin match member (((k1 - d) + passed), d1_) with
   | None -> raise (Assignment "EVar nonexistent")
   | Some (x, Dec) ->
       ((if k2 <= (r + d)
         then begin raise (Assignment "EVar - BVar clash") end
       else begin
         ((if k2 = k1
           then
             begin (begin function
                    | asub ->
                        (begin fasub asub;
                         assign (((d, Dec, u1_, u2_, asub))
                           (* ctxTotal,*)) end) end) end
   else begin
     raise
       (Assignment "EVars are different -- outside of the allowed fragment") end)
(* denote the same evar *)) end)
(* k2 is globally bound *)) end) end)
(* if (k1 - d) >= l *)(* k1 is a globally bound variable *)
(* k1 is an existial variable *))
| (Skonst c1, Skonst c2) ->
    if c1 = c2
    then begin assignSpine (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_)) end
    else begin raise (Assignment "Skolem constant clash") end
| _ -> raise (Assignment "Head mismatch ") end))
(* we do not expand definitions here -- this is very conservative! *)
(* we do not expand definitions here -- this is very conservative! *)
(* we do not expand definitions here -- this is very conservative! *)
(* can this happen ? -- definitions should be already expanded ?*))
| (fasub, (ctxTotal, d), (d1_, Lam (Dec1, u1_)), (d2_, Lam (Dec2, u2_))) ->
    assignExp (fasub, (ctxTotal, (d + 1)), (d1_, u1_), (d2_, u2_))
| (fasub, (ctxTotal, d), (d1_, Pi (((Dec (_, v1_) as Dec1), _), u1_)),
   (d2_, Pi (((Dec (_, v2_) as Dec2), _), u2_))) ->
    let fasub' = assignExp (fasub, (ctxTotal, d), (d1_, v1_), (d2_, v2_)) in
    ((assignExp (fasub', (ctxTotal, (d + 1)), (d1_, u1_), (d2_, u2_)))
      (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *))
| (fasub, (ctxTotal, d), (d1_, EClo (u_, (Shift 0 as s'))), (d2_, u2_)) ->
    assignExp (fasub, (ctxTotal, d), (d1_, u_), (d2_, u2_))
| (fasub, (ctxTotal, d), (d1_, u1_), (d2_, EClo (u_, (Shift 0 as s)))) ->
    assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, u_)) end(* the closure cases should be unnecessary, if everything is in nf *)
(* type labels are ignored *)
let rec assignSpine =
  begin function
  | (fasub, (ctxTotal, d), (d1_, I.Nil), (d2_, I.Nil)) -> fasub
  | (fasub, (ctxTotal, d), (d1_, App (u1_, s1_)), (d2_, App (u2_, s2_))) ->
      let fasub' = assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, u2_)) in
      assignSpine (fasub', (ctxTotal, d), (d1_, s1_), (d2_, s2_)) end
let rec assignCtx =
  begin function
  | (fasub, ctxTotal, (d1_, I.Null), (d2_, I.Null)) -> fasub
  | (fasub, ((r, passed) as ctxTotal), (d1_, Decl (g1_, Dec (_, v1_))),
     (d2_, Decl (g2_, Dec (_, v2_)))) ->
      let fasub' =
        assignExp
          (fasub, (((r - 1), (passed + 1)), 0), (d1_, v1_), (d2_, v2_)) in
      assignCtx (fasub', ((r - 1), (passed + 1)), (d1_, g1_), (d2_, g2_)) end
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
  | (Decl (g_, (Dec (_, a_) as d_)), s, Decl (g'_, (Dec (_, a'_) as d'_)),
     s') ->
      (Conv.convDec ((d_, s), (d'_, s'))) &&
        (equalCtx (g_, (I.dot1 s), g'_, (I.dot1 s')))
  | (_, s, _, s') -> false end
let rec equalEqn =
  begin function
  | (T.Trivial, T.Trivial) -> true
  | (Unify (g_, x_, n_, eqn), Unify (g'_, x'_, n'_, eqn')) ->
      (equalCtx (g_, I.id, g'_, I.id)) &&
        ((Conv.conv ((x_, I.id), (x'_, I.id))) &&
           ((Conv.conv ((n_, I.id), (n'_, I.id))) && (equalEqn (eqn, eqn'))))
  | (_, _) -> false end
let rec equalEqn' =
  begin function
  | (d, (d_, T.Trivial), (d'_, T.Trivial), asub) -> true
  | (d,
     (d_, Unify
      (((g_, (Root (BVar k, s_) as x_), n_, eqn))(* AVar *))),
     (d'_, Unify (((g'_, x'_, n'_, eqn'))(* AVar *))), asub)
      ->
      if
        (equalCtx (g_, I.id, g'_, I.id)) &&
          ((Conv.conv ((x_, I.id), (x'_, I.id))) &&
             (Conv.conv ((n_, I.id), (n'_, I.id))))
      then
        begin let d' = (+) d I.ctxLength g'_ in
              (((begin ((if (k - d') > 0
                         then
                           begin (((begin match member ((k - d'), d'_) with
                                    | None -> ()
                                    | Some (x, Dec) ->
                                        (begin match RBSet.lookup asub
                                                       (k - d')
                                               with
                                         | None ->
                                             (((begin delete (x, d'_);
                                                S.insert asub
                                                  ((k - d'),
                                                    (I.Idx (k - d'))) end))
                                         (* it is not instantiated yet *))
                                        | Some _ -> () end) end))
                (* k refers to an evar *)) end
      else begin
        (begin print "Impossible -- Found BVar instead of EVar\n";
         raise (Error "Impossibe -- Found BVar instead of EVar ") end) end)
  (* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
  (* k refers to a bound variable *));
  equalEqn' (d, (d_, eqn), (d'_, eqn'), asub) end))
(* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)) end
else begin false end
| (d, _, _, asub) -> false end
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
let rec equalCtx' =
  begin function
  | (I.Null, I.Null) -> true
  | (Decl (Dk, Dec (_, a_)), Decl (d1_, Dec (_, a1_))) ->
      (Conv.conv ((a_, I.id), (a1_, I.id))) && (equalCtx' (Dk, d1_))
  | (Decl (Dk, ADec (_, d')), Decl (d1_, ADec (_, d))) ->
      (d = d') && (equalCtx' (Dk, d1_))
  | (_, _) -> false end
let rec instanceCtx (asub, (d1_, g1_), (d2_, g2_)) =
  let d1 = I.ctxLength g1_ in
  let d2 = I.ctxLength g2_ in
  if d1 = d2
  then
    begin begin try
                  let fasub =
                    assignCtx ((begin function | asub -> () end), (d1, 0),
                      (d1_, g1_), (d2_, g2_)) in
                begin fasub asub; true end
  with | Assignment msg -> ((false)(* print msg;*)) end end
  else begin false end
let rec collectEVar (d_, nsub) =
  let d'_ = emptyCtx () in
  let rec collectExp =
    begin function
    | (d, d'_, d_, Lam (_, u_)) -> collectExp ((d + 1), d'_, d_, u_)
    | (d, d'_, d_, Root (Const c, s_)) -> collectSpine (d, d'_, d_, s_)
    | (d, d'_, d_, Root (BVar k, s_)) ->
        (begin match member ((k - d), d_) with
         | None -> collectSpine (d, d'_, d_, s_)
         | Some (x, Dec) ->
             (begin delete ((x - d), d_); insertList (((x - d), Dec), d'_) end) end)
  | (d, d'_, d_, (Root (Def k, s_) as u_)) ->
      let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
      collectExp (d, d'_, d_, u'_) end
  and collectSpine =
    begin function
    | (d, d'_, d_, I.Nil) -> ()
    | (d, d'_, d_, App (u_, s_)) ->
        (begin collectExp (d, d'_, d_, u_); collectSpine (d, d'_, d_, s_) end) end in
begin S.forall nsub
      (begin function | (nv, (du, u_)) -> collectExp (0, d'_, d_, u_) end);
(d'_, d_) end
let rec convAssSub' (g_, idx_k, d_, asub, d, ((evars, avars) as evarsl)) =
  begin match RBSet.lookup asub d with
  | None ->
      (((begin match member (d, d_) with
         | None -> IntSyn.Shift ((evars + avars)(* 0 *))
         | Some (x, Dec (n, v_)) ->
             let s = convAssSub' (g_, (idx_k + 1), d_, asub, (d + 1), evarsl) in
             let EVar (r, _, _, cnstr) as e_ = I.newEVar (I.Null, v_) in
             I.Dot ((I.Exp (I.EClo (e_, (I.Shift (evars + avars))))), s)
         | Some (x, ADec (n, v_)) ->
             (begin print "convAssSub' -- Found an uninstantiated AVAR\n";
              raise (Error "Unassigned AVar -- should never happen\n") end) end))
  (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
  (* should never happen -- all avars should
                     have been assigned! *))
  | Some (Exp (e_) as f_) ->
      let e'_ = Whnf.normalize (e_, I.id) in
      I.Dot
        ((I.Exp e'_),
          (convAssSub' (g_, (idx_k + 1), d_, asub, (d + 1), evarsl))) end
let rec convAssSub (g_, asub, Glength, d'_, evarsl) =
  convAssSub' (g_, 0, d'_, asub, Glength, evarsl)
let rec isExists (d, BVar k, d_) = member ((k - d), d_)
let rec instance ((D_t, (dt, t_)), (D_u, (du, u_)), rho_u, ac) =
  let rec instRoot =
    begin function
    | (depth, (Root ((Const k as h1_), s1_) as t_),
       (Root (Const k', s2_) as u_), ac) ->
        if k = k' then begin instSpine (depth, s1_, s2_, ac) end
        else begin raise (Instance "Constant mismatch\n") end
  | (depth, (Root ((Def k as h1_), s1_) as t_), (Root (Def k', s2_) as u_),
     ac) -> if k = k' then begin instSpine (depth, s1_, s2_, ac) end
      else begin
        (let t'_ = Whnf.normalize (Whnf.expandDef (t_, I.id)) in
         let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
         instExp (depth, t'_, u'_, ac)) end
  | (depth, (Root ((Def k as h1_), s1_) as t_), (Root (h2_, s2_) as u_), ac)
      ->
      let t'_ = Whnf.normalize (Whnf.expandDef (t_, I.id)) in
      instExp (depth, t'_, u_, ac)
  | (d, (Root ((BVar k as h1_), s1_) as t_), (Root (BVar k', s2_) as u_), ac)
      ->
      ((if (k > d) && (k' > d)
        then
          begin let k1 = k - d in
                let k2 = k' - d in
                (((begin match ((member (k1, D_t)), (member (k2, D_u))) with
                   | (None, None) ->
                       ((if k1 = k2
                         then begin instSpine (d, s1_, s2_, ac) end
                       else begin
                         raise (Instance "Bound variable mismatch\n") end)
                  (* both refer to the same globally bound variable in G *))
                  | (Some (x, Dec1), Some (x', Dec2)) ->
                      ((if (k1 = k2) && (equalDec (Dec1, Dec2))
                        then
                          begin let ac' = instSpine (d, s1_, s2_, ac) in
                                let ac'' =
                                  begin function
                                  | asub ->
                                      (((begin ac' asub;
                                         assign (((d, Dec1, t_, u_, asub))
                                           (* ctxTotal,*)) end))
                                  (* S.insert asub (k - d, I.Idx (k-d)) *)) end in
                        ((ac'')
                          (* this is unecessary *)(* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *)) end
          else begin
            (begin function
             | asub ->
                 (begin ac asub;
                  assign (((d, Dec1, t_, u_, asub))
                    (* ctxTotal,*)) end) end) end)
  (* they refer to the same existential variable *)(* instance checking only Sun Oct 27 12:16:10 2002 -bp *))
| (Some (x, (ADec (n, d') as Dec1)), None) ->
    (begin function
     | asub ->
         (begin ac asub;
          assign (((d, Dec1, t_, u_, asub))(* ctxTotal,*)) end) end)
| (Some (x, Dec1), None) ->
    (begin function
     | asub ->
         (begin ac asub;
          assign (((d, Dec1, t_, u_, asub))(* ctxTotal,*)) end) end)
| (_, _) -> raise (Instance "Impossible\n") end))
(* k, k' refer to the existential *)(* instance checking only Sun Oct 27 12:18:53 2002 -bp *)) end
else begin raise (Instance "Bound variable mismatch\n") end)
(* globally bound variable *)(* locally bound variables *))
| (d, (Root ((BVar k as h1_), s1_) as t_), (Root (Const k', s2_) as u_), ac)
    ->
    (begin match isExists (d, (I.BVar k), D_t) with
     | None -> raise (Instance "Impossible\n")
     | Some (x, (ADec (_, _) as Dec1)) ->
         (begin function
          | asub ->
              (begin ac asub;
               assign (((d, Dec1, t_, u_, asub))
                 (* ctxTotal,*)) end) end)
| Some (x, Dec1) ->
    (begin function
     | asub ->
         (begin ac asub;
          assign (((d, Dec1, t_, u_, asub))(* ctxTotal, *)) end) end) end)
| (d, (Root ((BVar k as h1_), s1_) as t_), (Root (Def k', s2_) as u_), ac) ->
    (begin match isExists (d, (I.BVar k), D_t) with
     | None -> raise (Instance "Impossible\n")
     | Some (x, (ADec (_, _) as Dec1)) ->
         (begin function
          | asub ->
              (begin ac asub;
               assign (((d, Dec1, t_, u_, asub))
                 (* ctxTotal,*)) end) end)
| Some (x, Dec1) ->
    (begin function
     | asub ->
         (begin ac asub;
          assign (((d, Dec1, t_, u_, asub))(* ctxTotal, *)) end) end) end)
| (depth, (Root (h1_, s1_) as t_), (Root (Def k', s2_) as u_), ac) ->
    let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
    instExp (depth, t_, u'_, ac)
| (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_), ac) ->
    raise (Instance "Other Cases impossible\n") end(* this case only should happen during instance checking *)
(* this case only should happen during instance checking *)
and instExp =
  begin function
  | (d, (NVar n as t_), (Root (h_, s_) as u_), ac) ->
      (begin S.insert rho_u (n, (d, u_)); ac end)
  | (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_), ac) ->
      instRoot (d, (I.Root (h1_, s1_)), (I.Root (h2_, s2_)), ac)
  | (d, Lam ((Dec (_, a1_) as d1_), t1_), Lam ((Dec (_, a2_) as d2_), u2_),
     ac) -> instExp ((d + 1), t1_, u2_, ac)
  | (d, t_, u_, ac) ->
      (begin print "instExp -- falls through?\n";
       raise (Instance "Impossible\n") end) end(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
(* by invariant A1 = A2 -- actually this invariant may be violated, but we ignore it. *)
and instSpine =
  begin function
  | (d, I.Nil, I.Nil, ac) -> ac
  | (d, App (t_, s1_), App (u_, s2_), ac) ->
      let ac' = instExp (d, t_, u_, ac) in
      let ac'' = instSpine (d, s1_, s2_, ac') in ac''
  | (d, I.Nil, App (_, _), ac) ->
      (begin print
               "Spines are not the same -- (first one is Nil) -- cannot happen!\n";
       raise (Instance "DifferentSpines\n") end)
  | (d, App (_, _), I.Nil, ac) ->
      (begin print
               "Spines are not the same -- second one is Nil -- cannot happen!\n";
       raise (Instance "DifferentSpines\n") end)
| (d, SClo (_, _), _, ac) ->
    (begin print "Spine Closure!(1) -- cannot happen!\n";
     raise (Instance "DifferentSpines\n") end)
| (d, _, SClo (_, _), ac) ->
    (begin print "Spine Closure! (2) -- cannot happen!\n";
     raise (Instance " DifferentSpines\n") end) end in
(((:=) ac instExp (dt, t_, u_, !ac))
(* by invariant dt = du *)(* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *))
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
let rec compatible' ((D_t, (dt, t_)), (D_u, (du, u_)), ds_, rho_t, rho_u) =
  let rec genNVar ((rho_t, t_), (rho_u, u_)) =
    ((begin S.insert rho_t ((!nctr + 1), t_);
      S.insert rho_u ((!nctr + 1), u_);
      newNVar () end)
    (* by invariant dt = du *)) in
let rec genRoot =
  begin function
  | (d, (Root ((Const k as h1_), s1_) as t_), (Root (Const k', s2_) as u_))
      ->
      if k = k'
      then begin let s'_ = genSpine (d, s1_, s2_) in I.Root (h1_, s'_) end
      else begin genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end
| (d, (Root ((Def k as h1_), s1_) as t_), (Root (Def k', s2_) as u_)) ->
    ((if k = k'
      then begin let s'_ = genSpine (d, s1_, s2_) in I.Root (h1_, s'_) end
    else begin genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end)
  (* could expand definitions here ? -bp*))
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
                                    genNVar
                                      ((rho_t, (d, t_)), (rho_u, (d, u_))) end) end
                   else begin genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end
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
          else begin genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end)
      (* they refer to the same existential variable *)
      (* variant checking only *))
  | (_, _) -> genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end))
(* should never happen *)(* k, k' refer to the existential *)) end
else begin
  if k = k'
  then
    begin (begin try let s'_ = genSpine (d, s1_, s2_) in I.Root (h1_, s'_)
           with
           | DifferentSpines -> genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end) end
else begin genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end end)
(* globally bound variable *)(* locally bound variables *))
| (d, (Root ((BVar k as h1_), s1_) as t_), (Root (Const k', s2_) as u_)) ->
    genNVar ((rho_t, (d, t_)), (rho_u, (d, u_)))
| (d, (Root ((BVar k as h1_), s1_) as t_), (Root (Def k', s2_) as u_)) ->
    genNVar ((rho_t, (d, t_)), (rho_u, (d, u_)))
| (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
    genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end
and genExp =
  begin function
  | (d, (NVar n as t_), (Root (h_, s_) as u_)) ->
      (begin S.insert rho_u (n, (d, u_)); t_ end)
  | (d, (Root (h1_, s1_) as t_), (Root (h2_, s2_) as u_)) ->
      genRoot (d, (I.Root (h1_, s1_)), (I.Root (h2_, s2_)))
  | (d, Lam ((Dec (_, a1_) as d1_), t1_), Lam ((Dec (_, a2_) as d2_), u2_))
      -> let e_ = genExp ((d + 1), t1_, u2_) in I.Lam (d1_, e_)
  | (d, t_, u_) ->
      (begin print "genExp -- falls through?\n";
       genNVar ((rho_t, (d, t_)), (rho_u, (d, u_))) end) end(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
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
((Variant (dt, (genExp (dt, t_, u_))))
(* by invariant dt = du *))
let rec compatible =
  begin function
  | ((D_t, ((d1, Root (h1_, s1_)) as t_)),
     (D_u, ((d2, Root (h2_, s2_)) as u_)), ds_, rho_t, rho_u) ->
      if compHeads ((D_t, h1_), (D_u, h2_))
      then begin compatible' ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) end
      else begin NotCompatible end
  | ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) ->
      compatible' ((D_t, t_), (D_u, u_), ds_, rho_t, rho_u) end
let rec compatibleCtx =
  begin function
  | (asub, (Dsq, Gsq, eqn_sq), []) -> None
  | (asub, (Dsq, Gsq, eqn_sq),
     (_, Delta', g'_, eqn', answRef', _, status')::GRlist) ->
      if instanceCtx (asub, (Dsq, Gsq), (Delta', g'_))
      then begin Some ((Delta', g'_, eqn'), answRef', status') end
      else begin compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GRlist) end end
let rec instanceSub ((D_t, nsub_t), (Dsq, squery), asub) =
  let rho_u = nid () in
  let D_r2 = copy Dsq in
  let ac = ref (begin function | (asub : exSubsts) -> () end) in
  ((begin try
            begin S.forall squery
                    (begin function
                     | (nv, (du, u_)) ->
                         (((begin match S.lookup nsub_t nv with
                            | Some (dt, t_) ->
                                instance
                                  ((D_t, (dt, t_)), (D_r2, (du, u_)), rho_u,
                                    ac)
                            | None -> S.insert rho_u (nv, (du, u_)) end))
                     (* note by invariant Glocal_e ~ Glocal_t *)
                     (* [ac]T = U *)(* if U is an instance of T then [ac][rc_u]T = U *)
                     (* once the continuations ac are triggered *)) end);
    (!) ac asub; InstanceSub (asub, (D_r2, rho_u)) end
  with | Instance msg -> NoCompatibleSub end)
(* by invariant rho_t = empty, since nsub_t <= squery *))
let rec instChild =
  begin function
  | ((Leaf ((D_t, nsub_t), GList) as n_), (D_sq, sq), asub) ->
      instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
  | ((Node ((D_t, nsub_t), Children') as n_), (D_sq, sq), asub) ->
      instanceSub ((D_t, nsub_t), (D_sq, sq), asub) end
let rec findAllInst (G_r, children, ds_, asub) =
  let rec findAllCands =
    begin function
    | (G_r, [], (Dsq, sub_u), asub, IList) -> IList
    | (G_r, x::l_, (Dsq, sub_u), asub, IList) ->
        let asub' = S.copy asub in
        (((begin match instChild (!x, (Dsq, sub_u), asub) with
           | NoCompatibleSub ->
               findAllCands (G_r, l_, (Dsq, sub_u), asub', IList)
           | InstanceSub (asub, Drho2) ->
               findAllCands
                 (G_r, l_, (Dsq, sub_u), asub', ((x, Drho2, asub) :: IList)) end))
        (* will update asub *)) end in
findAllCands (G_r, children, ds_, asub, [])
let rec solveEqn =
  begin function
  | ((T.Trivial, s), g_) -> true
  | ((Unify (((g'_, e1, n_, eqns))(* evar *)), s), g_) ->
      let G'' = compose (g'_, g_) in
      let s' = shift (G'', s) in
      (Assign.unifiable (G'', (n_, s'), (e1, s'))) &&
        (solveEqn ((eqns, s), g_)) end
let rec solveEqn' =
  begin function
  | ((T.Trivial, s), g_) -> true
  | ((Unify (((g'_, e1, n_, eqns))(* evar *)), s), g_) ->
      let G'' = compose (g'_, g_) in
      let s' = shift (g'_, s) in
      (Assign.unifiable (G'', (n_, s'), (e1, s'))) &&
        (solveEqn' ((eqns, s), g_)) end
let rec solveEqnI' =
  begin function
  | ((T.Trivial, s), g_) -> true
  | ((Unify (((g'_, e1, n_, eqns))(* evar *)), s), g_) ->
      let G'' = compose (g'_, g_) in
      let s' = shift (g'_, s) in
      (((Assign.instance (G'', (e1, s'), (n_, s'))) &&
          (solveEqnI' ((eqns, s), g_)))
        (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
        (* at this point all AVars have been instantiated, and we could use Match.instance directly *)) end
let rec retrieveInst (Nref, (Dq, sq), asub, GR) =
  let rec retrieve' =
    begin function
    | ((Leaf ((d_, s), GRlistRef) as n_), (Dq, sq), asubst,
       ((((DEVars, DAVars) as DAEVars), G_r, eqn, stage, status) as GR')) ->
        let (Dsq, D_G) = collectEVar (Dq, sq) in
        (((begin match compatibleCtx (asubst, (D_G, G_r, eqn), !GRlistRef)
                 with
           | None -> ((raise (Instance "Compatible path -- different ctx\n"))
               (* compatible path -- but different ctx *))
           | Some ((d'_, g'_, eqn'), answRef', status') ->
               ((let DAEVars = compose (DEVars, DAVars) in
                 let esub = ctxToAVarSub (g'_, DAEVars, (I.Shift 0)) in
                 let asub =
                   convAssSub
                     (g'_, asubst, ((I.ctxLength g'_) + 1), d'_,
                       ((I.ctxLength DAVars), (I.ctxLength DEVars))) in
                 let _ =
                   if
                     solveEqn' ((((eqn, (shift (g'_, esub))), g'_))
                       (* = G_r *))
                   then begin () end
                   else begin print " failed to solve eqn_query\n" end in
                 let easub = normalizeSub (I.comp (asub, esub)) in
                 ((if solveEqnI' ((eqn', (shift (g'_, easub))), g'_)
                   then
                     begin T.RepeatedEntry ((esub, asub), answRef', status') end
                   else begin
                     raise
                       (Instance
                          "Compatible path -- resdidual equ. not solvable\n") end)
                   (*              if solveEqnI' (eqn', easub) *)
                   (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
                   (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
                   (* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
                   (*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
                   (* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)))
    (* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)) end))
  (* compatibleCtx may destructively update asub ! *)
  (* compatible path -- SAME ctx *)(* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *))
| ((Node ((d_, sub), children) as n_), (Dq, sq), asub,
   ((DAEVars, G_r, eqn, stage, status) as GR)) ->
    let InstCand = findAllInst (G_r, children, (Dq, sq), asub) in
    let rec checkCandidates =
      begin function
      | [] -> raise (Instance "No compatible child\n")
      | (ChildRef, Drho2, asub)::ICands ->
          (begin try retrieve' (!ChildRef, Drho2, asub, GR)
           with
           | Instance msg -> ((checkCandidates ICands)
               (* print msg; *)) end) end(* there is an instance  *)
    (* no child is compatible with sq *) in
  checkCandidates InstCand end(* [asub]s = sq   and there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
           s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
           *)
(* s and sq are compatible by invariant *) in
((begin function | () -> () end),
(retrieve' (!Nref, (Dq, sq), asub, GR)))
let rec compatibleSub ((D_t, nsub_t), (Dsq, squery)) =
  let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
  let Dsigma = emptyCtx () in
  let D_r1 = copy D_t in
  let D_r2 = copy Dsq in
  let choose = ref (begin function | (match_ : bool) -> () end) in
  let _ =
    S.forall squery
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
(* by invariant rho_t = empty, since nsub_t <= squery *)
(* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *))
let rec mkNode =
  begin function
  | (Node (_, Children), ((ds_, sigma) as Dsigma), ((d1_, rho1) as Drho1),
     (((evarl, l), dp, eqn, answRef, stage, status) as GR),
     ((d2_, rho2) as Drho2)) ->
      let (D_rho2, D_G2) = collectEVar (d2_, rho2) in
      let GR' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
      let (sizeSigma, sizeRho1, sizeRho2) =
        ((S.size sigma), (S.size rho1), (S.size rho2)) in
      Node
        (Dsigma,
          [ref (Leaf ((D_rho2, rho2), (ref [GR'])));
          ref (Node (Drho1, Children))])
  | (Leaf (c, GRlist), ((ds_, sigma) as Dsigma), ((d1_, rho1) as Drho1),
     (((evarl, l), dp, eqn, answRef, stage, status) as GR2),
     ((d2_, rho2) as Drho2)) ->
      let (D_rho2, D_G2) = collectEVar (d2_, rho2) in
      let GR2' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
      Node
        (Dsigma,
          [ref (Leaf ((D_rho2, rho2), (ref [GR2'])));
          ref (Leaf (Drho1, GRlist))]) end
let rec compChild =
  begin function
  | ((Leaf ((D_t, nsub_t), GList) as n_), (D_e, nsub_e)) ->
      compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
  | ((Node ((D_t, nsub_t), Children') as n_), (D_e, nsub_e)) ->
      compatibleSub ((D_t, nsub_t), (D_e, nsub_e)) end
let rec findAllCandidates (G_r, children, ds_) =
  let rec findAllCands =
    begin function
    | (G_r, [], (Dsq, sub_u), VList, SList) -> (VList, SList)
    | (G_r, x::l_, (Dsq, sub_u), VList, SList) ->
        (begin match compChild (!x, (Dsq, sub_u)) with
         | NoCompatibleSub ->
             findAllCands (G_r, l_, (Dsq, sub_u), VList, SList)
         | SplitSub (Dsigma, Drho1, Drho2) ->
             findAllCands
               (G_r, l_, (Dsq, sub_u), VList,
                 ((x, (Dsigma, Drho1, Drho2)) :: SList))
         | VariantSub ((D_r2, rho2) as Drho2) ->
             findAllCands
               (G_r, l_, (Dsq, sub_u), ((x, Drho2, I.id) :: VList), SList) end) end in
findAllCands (G_r, children, ds_, [], [])
let rec divergingCtx (stage, g_, GRlistRef) =
  let l = (I.ctxLength g_) + 3 in
  ((List.exists
      (begin function
       | ((_, l), d_, g'_, _, _, stage', _) ->
           (stage = stage') && (l > (I.ctxLength g'_)) end)
    !GRlistRef)
  (* this 3 is arbitrary -- lockstep *))
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
       | Some (dt1, t1_) -> eqTerm (t2_, (t1_, (nid ()))) end)
| (Lam (d2_, t2_), (Lam (d_, t_), rho1)) -> eqTerm (t2_, (t_, rho1))
| (_, (_, _)) -> false end
let rec eqSpine =
  begin function
  | (I.Nil, (I.Nil, rho1)) -> true
  | (App (t2_, s2_), (App (t_, s_), rho1)) ->
      (eqTerm (t2_, (t_, rho1))) && (eqSpine (s2_, (s_, rho1))) end
let rec divergingSub ((ds_, sigma), (Dr1, rho1), (Dr2, rho2)) =
  S.exists rho2
    (begin function
     | (n2, (dt2, t2)) ->
         S.exists sigma
           (begin function | (_, (d, t)) -> eqTerm (t2, (t, rho1)) end) end)
let rec variantCtx =
  begin function
  | ((g_, eqn), []) -> None
  | ((g_, eqn), (l', D_G, g'_, eqn', answRef', _, status')::GRlist) ->
      if (equalCtx' (g_, g'_)) && (equalEqn (eqn, eqn'))
      then begin Some (l', answRef', status') end
      else begin variantCtx ((g_, eqn), GRlist) end end
let rec insert (Nref, (Dsq, sq), GR) =
  let rec insert' =
    begin function
    | ((Leaf (_, GRlistRef) as n_), (Dsq, sq),
       ((l, G_r, eqn, answRef, stage, status) as GR)) ->
        (begin match variantCtx ((G_r, eqn), !GRlistRef) with
         | None ->
             ((let (D_nsub, D_G) = collectEVar (Dsq, sq) in
               let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
               (((((begin function
                    | () ->
                        (begin GRlistRef := (GR' :: !GRlistRef);
                         answList := (answRef :: !answList) end) end)),
                 (T.NewEntry answRef)))
             (* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)))
        (* compatible path -- but different ctx! *))
    | Some (_, answRef', status') -> (((((begin function | () -> () end)),
        (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
    (* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)) end)
  | ((Node ((d_, sub), children) as n_), (Dsq, sq),
     ((l, G_r, eqn, answRef, stage, status) as GR)) ->
      let (VariantCand, SplitCand) =
        findAllCandidates (G_r, children, (Dsq, sq)) in
      let (D_nsub, D_G) = collectEVar (Dsq, sq) in
      let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
      let rec checkCandidates =
        begin function
        | ([], []) ->
            (((begin function
               | () ->
                   (begin (:=) Nref Node
                            ((d_, sub),
                              ((ref (Leaf ((D_nsub, sq), (ref [GR'])))) ::
                                 children));
                    answList := (answRef :: !answList) end) end)),
        (T.NewEntry answRef))
        | ([], (ChildRef, (Dsigma, Drho1, Drho2))::_) ->
            if
              !TableParam.divHeuristic &&
                (divergingSub (Dsigma, Drho1, Drho2))
            then
              begin (((((begin function
                         | () ->
                             (begin (:=) ChildRef mkNode
                                      (!ChildRef, Dsigma, Drho1, GR, Drho2);
                              answList := (answRef :: !answList) end) end)),
            (T.DivergingEntry (I.id, answRef))))
            (* substree diverging -- splitting node *)) end
        else begin
          (((((begin function
               | () ->
                   (begin (:=) ChildRef mkNode
                            (!ChildRef, Dsigma, Drho1, GR, Drho2);
                    answList := (answRef :: !answList) end) end)),
        (T.NewEntry answRef)))(* split existing node *)) end
| ((ChildRef, Drho2, asub)::[], _) -> insert (ChildRef, Drho2, GR)
| ((ChildRef, Drho2, asub)::l_, SCands) ->
    (begin match insert (ChildRef, Drho2, GR) with
     | (_, NewEntry answRef) -> checkCandidates (l_, SCands)
     | (f, RepeatedEntry (asub, answRef, status)) ->
         (f, (T.RepeatedEntry (asub, answRef, status)))
     | (f, DivergingEntry (asub, answRef)) ->
         (f, (T.DivergingEntry (asub, answRef))) end) end(* there are several "perfect" candidates *)
(* unique "perfect" candidate (left) *)(* split an existing node *)
(* no child is compatible with sq *) in
checkCandidates (VariantCand, SplitCand) end in
insert' (!Nref, (Dsq, sq), GR)
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
  ((begin nctr := 1;
    Array.modify
      (begin function
       | (n, Tree) ->
           (begin n := 0;
            (!) ((:=) Tree) (makeTree ());
            answList := [];
            added := false;
            (n, Tree) end) end)
  indexArray end)
(* Reset Subsitution Tree *))
let rec makeCtx =
  begin function
  | (n, I.Null, (DEVars : ctx)) -> ()
  | (n, Decl (g_, d_), (DEVars : ctx)) ->
      (begin insertList ((n, d_), DEVars); makeCtx ((n + 1), g_, DEVars) end) end
let rec callCheck (a, DAVars, DEVars, g_, u_, eqn, status) =
  let (n, Tree) = Array.sub (indexArray, a) in
  let sq = S.new_ () in
  let DAEVars = compose (DEVars, DAVars) in
  let Dq = emptyCtx () in
  let n = I.ctxLength g_ in
  let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
  let l = I.ctxLength DAEVars in
  let _ = S.insert sq (1, (0, u_)) in
  let GR =
    ((l, (n + 1)), g_, eqn, (emptyAnswer ()), !TableParam.stageCtr, status) in
  let GR' = ((DEVars, DAVars), g_, eqn, !TableParam.stageCtr, status) in
  let result =
    begin try
            retrieveInst (((Tree, (Dq, sq), (asid ()), GR'))
              (* assignable subst *))
    with
    | Instance msg -> ((insert (Tree, (Dq, sq), GR))
        (* sq not in index --> insert it *)) end in
  ((begin match result with
    | (sf, NewEntry answRef) ->
        (begin sf (); added := true; T.NewEntry answRef end)
    | (_, RepeatedEntry (asub, answRef, status)) ->
        T.RepeatedEntry (asub, answRef, status)
    | (sf, DivergingEntry (asub, answRef)) ->
        (begin sf (); added := true; T.DivergingEntry (asub, answRef) end) end)
    (* n = |G| *)(* Dq = DAVars, DEVars *)
    (* l = |D| *))
let rec insertIntoTree (a, DAVars, DEVars, g_, u_, eqn, answRef, status) =
  let (n, Tree) = Array.sub (indexArray, a) in
  let sq = S.new_ () in
  let DAEVars = compose (DEVars, DAVars) in
  let Dq = emptyCtx () in
  let n = I.ctxLength g_ in
  let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
  let l = I.ctxLength DAEVars in
  let _ = S.insert sq (1, (0, u_)) in
  let GR =
    ((l, (n + 1)), g_, eqn, (emptyAnswer ()), !TableParam.stageCtr, status) in
  let result =
    insert
      (Tree, (Dq, sq),
        ((l, (n + 1)), g_, eqn, answRef, !TableParam.stageCtr, status)) in
  ((begin match result with
    | (sf, NewEntry answRef) ->
        (begin sf (); added := true; T.NewEntry answRef end)
    | (_, RepeatedEntry (asub, answRef, status)) ->
        T.RepeatedEntry (asub, answRef, status)
    | (sf, DivergingEntry (asub, answRef)) ->
        (begin sf (); added := true; T.DivergingEntry (asub, answRef) end) end)
    (* sq = query substitution *))
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
  let rec instanceCtx' =
    begin function
    | ((g_, v_), I.Null, n) -> None
    | ((g_, v_), Decl (g'_, (Dec (_, v'_) as d'_)), n) ->
        if Match.instance (g_, (v_, I.id), (v'_, (I.Shift n)))
        then begin Some d'_ end
        else begin instanceCtx' ((g_, v_), g'_, (n + 1)) end end in
instanceCtx' ((g_, v_), g'_, 1) end
