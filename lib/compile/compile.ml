module type COMPILE  =
  sig
    exception Error of string 
    type opt_ = CompSyn.opt_
    val optimize : opt_ ref
    val install : IntSyn.conDecForm_ -> IntSyn.cid -> unit
    val sProgReset : unit -> unit
    val compileCtx : bool -> IntSyn.dec_ IntSyn.ctx_ -> CompSyn.dProg_
    val compileGoal :
      (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_) -> CompSyn.goal_
    val compilePsi : bool -> Tomega.dec_ IntSyn.ctx_ -> CompSyn.dProg_
  end


module Compile(Compile:sig
                         module Whnf : WHNF
                         module TypeCheck : TYPECHECK
                         module SubTree : SUBTREE
                         module CPrint : CPRINT
                         module Print : PRINT
                         module Names : NAMES
                       end) : COMPILE =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module C = CompSyn
    type duplicates_ =
      | BVAR of int 
      | FGN 
      | DEF of int 
    let rec notCS = begin function | I.FromCS -> false | _ -> true end
    type opt_ = CompSyn.opt_
    let optimize = CompSyn.optimize
    let rec cidFromHead = begin function | Const c -> c | Def c -> c end
  let rec isConstraint =
    begin function
    | Const c ->
        (begin match I.constStatus c with | Constraint _ -> true | _ -> false end)
    | h_ -> false end
let rec head = begin function | Root (h, _) -> h | Pi (_, a_) -> head a_ end
let rec seen (i, Vars) = List.exists (begin function | (d, x) -> x = i end)
  Vars
let rec etaSpine =
  begin function
  | (I.Nil, n) -> n = 0
  | (App (Root (BVar k, I.Nil), s_), n) ->
      (k = n) && (etaSpine (s_, (n - 1)))
  | (App (a_, s_), n) -> false end
let rec collectHead =
  begin function
  | ((BVar k as h), s_, k_, Vars, depth) ->
      ((if k > depth
        then
          begin (if etaSpine (s_, depth)
                 then
                   begin (if seen ((k - depth), Vars)
                          then
                            begin (((depth, (BVAR (k - depth))) :: k_), Vars,
                                    true) end
                   else begin (k_, ((depth, (k - depth)) :: Vars), false) end) end
      else begin (((depth, (BVAR (k - depth))) :: k_), Vars, true) end) end
else begin (k_, Vars, false) end)
(* check if h is an eta-expanded variable *)(* h is a locally bound variable and need not be collected *))
| (_, _, k_, Vars, depth) -> (k_, Vars, false) end(* check if k is in Vars *)
let rec collectSpine =
  begin function
  | (I.Nil, k_, Vars, depth) -> (k_, Vars)
  | (App (u_, s_), k_, Vars, depth) ->
      let (k'_, Vars') = collectExp (u_, k_, Vars, depth) in
      collectSpine (s_, k'_, Vars', depth) end
let rec collectExp =
  begin function
  | (Root ((BVar k as h), s_), k_, Vars, depth) ->
      let (k'_, Vars', replaced) = collectHead (h, s_, k_, Vars, depth) in
      if replaced then begin (k'_, Vars') end
        else begin collectSpine (s_, k'_, Vars', depth) end
  | ((Root (Def k, s_) as u_), k_, Vars, depth) ->
      (((depth, (DEF k)) :: k_), Vars)
  | (Root (h, s_), k_, Vars, depth) -> collectSpine (s_, k_, Vars, depth)
  | (Lam (d_, u_), k_, Vars, depth) -> collectExp (u_, k_, Vars, (depth + 1))
  | (FgnExp (cs, fe), k_, Vars, depth) -> (((depth, FGN) :: k_), Vars) end
(* don't collect D, since it is ignored in unification *)
(* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)
(* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)
(* h is either const or skonst of def*)
let rec shiftHead =
  begin function
  | ((BVar k as h), depth, total) ->
      if k > depth then begin I.BVar (k + total) end else begin I.BVar k end
  | ((Const k as h), depth, total) -> h | ((Def k as h), depth, total) -> h
  | ((NSDef k as h), depth, total) -> h
  | ((FgnConst k as h), depth, total) -> h
  | ((Skonst k as h), depth, total) -> h end
let rec shiftExp =
  begin function
  | (Root (h, s_), depth, total) ->
      I.Root ((shiftHead (h, depth, total)), (shiftSpine (s_, depth, total)))
  | (Uni (l_), _, _) -> I.Uni l_
  | (Lam (d_, u_), depth, total) ->
      I.Lam
        ((shiftDec (d_, depth, total)), (shiftExp (u_, (depth + 1), total)))
  | (Pi ((d_, p_), u_), depth, total) ->
      I.Pi
        (((shiftDec (d_, depth, total)), p_),
          (shiftExp (u_, (depth + 1), total)))
  | (FgnExp csfe, depth, total) ->
      I.FgnExpStd.Map.apply csfe
        (begin function
         | u_ -> shiftExp ((Whnf.normalize (u_, I.id)), depth, total) end) end
(* Tue Apr  2 12:10:24 2002 -fp -bp *)(* this is overkill and could be very expensive for deeply nested foreign exps *)
(* calling normalize here because U may not be normal *)
let rec shiftSpine =
  begin function
  | (I.Nil, _, _) -> I.Nil
  | (App (u_, s_), depth, total) ->
      I.App ((shiftExp (u_, depth, total)), (shiftSpine (s_, depth, total))) end
let rec shiftDec (Dec (x, v_), depth, total) =
  I.Dec (x, (shiftExp (v_, depth, total)))
let rec linearHead =
  begin function
  | (g_, (BVar k as h), s_, left, Vars, depth, total) ->
      if k > depth
      then
        begin (if etaSpine (s_, depth)
               then
                 begin (if seen ((k - depth), Vars)
                        then
                          begin ((left - 1), Vars, (I.BVar (left + depth)),
                                  true) end
                 else begin
                   (left, ((depth, (k - depth)) :: Vars),
                     (I.BVar (k + total)), false) end) end
      else begin ((left - 1), Vars, (I.BVar (left + depth)), true) end) end
else begin (left, Vars, h, false) end
| (g_, (Const k as h), s_, left, Vars, depth, total) ->
    (left, Vars, h, false)
| (g_, (FgnConst (k, ConDec) as h), s_, left, Vars, depth, total) ->
    (left, Vars, h, false)
| (g_, (Skonst k as h), s_, left, Vars, depth, total) ->
    (left, Vars, h, false) end(*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)
let rec linearExp =
  begin function
  | (Gl, (Root ((Def k as h), s_) as u_), left, Vars, depth, total, eqns) ->
      let n_ = I.Root ((I.BVar (left + depth)), I.Nil) in
      let u'_ = shiftExp (u_, depth, total) in
      ((left - 1), Vars, n_, (C.UnifyEq (Gl, u'_, n_, eqns)))
  | (Gl, (Root (h, s_) as u_), left, Vars, depth, total, eqns) ->
      let (left', Vars', h', replaced) =
        linearHead (Gl, h, s_, left, Vars, depth, total) in
      ((if replaced
        then
          begin let n_ = I.Root (h', I.Nil) in
                let u'_ = shiftExp (u_, depth, total) in
                (left', Vars, n_, (C.UnifyEq (Gl, u'_, n_, eqns))) end
        else begin
          (let (left'', Vars'', s'_, eqns') =
             linearSpine (Gl, s_, left', Vars', depth, total, eqns) in
           (left'', Vars'', (I.Root (h', s'_)), eqns')) end)
  (* h = h' not replaced *))
  | (Gl, Lam (d_, u_), left, Vars, depth, total, eqns) ->
      let d'_ = shiftDec (d_, depth, total) in
      let (left', Vars', u'_, eqns') =
        linearExp
          ((I.Decl (Gl, d'_)), u_, left, Vars, (depth + 1), total, eqns) in
      (left', Vars', (I.Lam (d'_, u'_)), eqns')
  | (Gl, (FgnExp (cs, ops) as u_), left, Vars, depth, total, eqns) ->
      let n_ = I.Root ((I.BVar (left + depth)), I.Nil) in
      let u'_ = shiftExp (u_, depth, total) in
      ((left - 1), Vars, n_, (C.UnifyEq (Gl, u'_, n_, eqns))) end(*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)
(* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
let rec linearSpine =
  begin function
  | (Gl, I.Nil, left, Vars, depth, total, eqns) -> (left, Vars, I.Nil, eqns)
  | (Gl, App (u_, s_), left, Vars, depth, total, eqns) ->
      let (left', Vars', u'_, eqns') =
        linearExp (Gl, u_, left, Vars, depth, total, eqns) in
      let (left'', Vars'', s'_, eqns'') =
        linearSpine (Gl, s_, left', Vars', depth, total, eqns') in
      (left'', Vars'', (I.App (u'_, s'_)), eqns'') end
let rec compileLinearHead (g_, (Root (h, s_) as r_)) =
  let (k_, _) = collectExp (r_, [], [], 0) in
  let left = List.length k_ in
  let (left', _, r'_, Eqs) =
    linearExp (I.Null, r_, left, [], 0, left, C.Trivial) in
  let rec convertKRes =
    begin function
    | (ResG, [], 0) -> ResG
    | (ResG, (d, k)::k_, i) ->
        C.Axists
          ((I.ADec ((Some ((^) "A" Int.toString i)), d)),
            (convertKRes (ResG, k_, (i - 1)))) end in
  let r = convertKRes ((C.Assign (r'_, Eqs)), (List.rev k_), left) in
  begin if !Global.chatter >= 6
        then
          begin (begin print "\nClause LH Eqn";
                 print (CPrint.clauseToString "\t" (g_, r)) end) end
    else begin () end; r end
let rec compileSbtHead (g_, (Root (h, s_) as h_)) =
  let (k_, _) = collectExp (h_, [], [], 0) in
  let left = List.length k_ in
  let (left', _, h'_, Eqs) =
    linearExp (I.Null, h_, left, [], 0, left, C.Trivial) in
  let rec convertKRes =
    begin function
    | (g_, [], 0) -> g_
    | (g_, (d, k)::k_, i) ->
        convertKRes
          ((I.Decl (g_, (I.ADec ((Some ((^) "AVar " Int.toString i)), d)))),
            k_, (i - 1)) end in
  let g'_ = convertKRes (g_, (List.rev k_), left) in
  ((begin if !Global.chatter >= 6
          then
            begin (begin print "\nClause Sbt Eqn";
                   print
                     (CPrint.clauseToString "\t" (g'_, (C.Assign (h'_, Eqs)))) end) end
    else begin () end; (g'_, (Some (h'_, Eqs))) end)
  (* insert R' together with Eqs and G and sc C.True *))
let rec compileGoalN arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (fromCS, (g_, (Root _ as r_))) -> C.Atom r_
  | (fromCS, (g_, Pi ((Dec (_, a1_), I.No), a2_))) ->
      let Ha1 = I.targetHead a1_ in
      let r_ = compileDClauseN fromCS false (g_, a1_) in
      let goal =
        compileGoalN fromCS ((I.Decl (g_, (I.Dec (None, a1_)))), a2_) in
      ((C.Impl (r_, a1_, Ha1, goal))
        (* A1 is used to build the proof term, Ha1 for indexing *)
        (* never optimize when compiling local assumptions *))
  | (fromCS, (g_, Pi (((Dec (_, a1_) as d_), I.Maybe), a2_))) ->
      if (notCS fromCS) && (isConstraint (head a1_))
      then
        begin raise (Error "Constraint appears in dynamic clause position") end
      else begin C.All (d_, (compileGoalN fromCS ((I.Decl (g_, d_)), a2_))) end end
(* A = {x:A1} A2 *)(* A = A1 -> A2 *)
(* A = H @ S *)
let rec compileGoal fromCS (g_, (a_, s)) =
  compileGoalN fromCS (g_, (Whnf.normalize (a_, s)))
let rec compileDClauseN arg__2 arg__3 arg__4 =
  begin match (arg__2, arg__3, arg__4) with
  | (fromCS, opt, (g_, (Root (h, s_) as r_))) ->
      if opt && (!optimize = C.LinearHeads)
      then begin compileLinearHead (g_, r_) end
      else begin
        if (notCS fromCS) && (isConstraint h)
        then
          begin raise (Error "Constraint appears in dynamic clause position") end
        else begin C.Eq r_ end end
| (fromCS, opt, (g_, Pi (((Dec (_, a1_) as d_), I.No), a2_))) ->
    C.And
      ((compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_)), a1_,
        (compileGoalN fromCS (g_, a1_)))
| (fromCS, opt, (g_, Pi (((Dec (_, a1_) as d_), I.Meta), a2_))) ->
    C.In
      ((compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_)), a1_,
        (compileGoalN fromCS (g_, a1_)))
| (fromCS, opt, (g_, Pi ((d_, I.Maybe), a2_))) ->
    C.Exists (d_, (compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_))) end
(* A = {x:A1} A2 *)(* A = {x: A1} A2, x  meta variable occuring in A2 *)
(* A = A1 -> A2 *)
let rec compileSubgoals arg__5 arg__6 arg__7 =
  begin match (arg__5, arg__6, arg__7) with
  | (fromCS, g'_, (n, Decl (Stack, I.No), Decl (g_, Dec (_, a_)))) ->
      let sg = compileSubgoals fromCS g'_ ((n + 1), Stack, g_) in
      ((C.Conjunct
          ((compileGoal fromCS (g'_, (a_, (I.Shift (n + 1))))),
            (I.EClo (a_, (I.Shift (n + 1)))), sg))
        (* G |- A and G' |- A[^(n+1)] *))
  | (fromCS, g'_, (n, Decl (Stack, I.Maybe), Decl (g_, Dec (_, a1_)))) ->
      compileSubgoals fromCS g'_ ((n + 1), Stack, g_)
  | (fromCS, g'_, (n, I.Null, I.Null)) -> C.True end
let rec compileSClauseN arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (fromCS, (Stack, g_, (Root (h, s_) as r_))) ->
      let (g'_, Head) = compileSbtHead (g_, r_) in
      let d = (-) (I.ctxLength g'_) I.ctxLength g_ in
      let Sgoals = compileSubgoals fromCS g'_ (d, Stack, g_) in
      ((((g'_, Head), Sgoals))
        (* G' |- Sgoals  and G' |- ^d : G *))
  | (fromCS, (Stack, g_, Pi (((Dec (_, a1_) as d_), I.No), a2_))) ->
      compileSClauseN fromCS ((I.Decl (Stack, I.No)), (I.Decl (g_, d_)), a2_)
  | (fromCS, (Stack, g_, Pi (((Dec (_, a1_) as d_), I.Meta), a2_))) ->
      compileSClauseN fromCS
        ((I.Decl (Stack, I.Meta)), (I.Decl (g_, d_)), a2_)
  | (fromCS, (Stack, g_, Pi (((Dec (_, a1_) as d_), I.Maybe), a2_))) ->
      compileSClauseN fromCS
        ((I.Decl (Stack, I.Maybe)), (I.Decl (g_, d_)), a2_) end
let rec compileDClause opt (g_, a_) =
  compileDClauseN I.Ordinary opt (g_, (Whnf.normalize (a_, I.id)))
let rec compileGoal (g_, a_) =
  compileGoalN I.Ordinary (g_, (Whnf.normalize (a_, I.id)))
let rec compileCtx opt (g_) =
  let rec compileBlock =
    begin function
    | ([], s, (n, i)) -> []
    | ((Dec (_, v_))::vs_, t, (n, i)) ->
        let Vt = I.EClo (v_, t) in
        (::) ((compileDClause opt (g_, Vt)), I.id, (I.targetHead Vt))
          compileBlock
          (vs_,
            (I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
            (n, (i + 1))) end in
let rec compileCtx' =
  begin function
  | I.Null -> I.Null
  | Decl (g_, Dec (_, a_)) ->
      let Ha = I.targetHead a_ in
      I.Decl
        ((compileCtx' g_),
          (CompSyn.Dec ((compileDClause opt (g_, a_)), I.id, Ha)))
  | Decl (g_, BDec (_, (c, s))) ->
      let (g_, l_) = I.constBlock c in
      let dpool = compileCtx' g_ in
      let n = I.ctxLength dpool in
      ((I.Decl (dpool, (CompSyn.BDec (compileBlock (l_, s, (n, 1))))))
        (* this is inefficient! -cs *)) end in
C.DProg (g_, (compileCtx' g_))
let rec compilePsi opt (Psi) =
  let rec compileBlock =
    begin function
    | ([], s, (n, i)) -> []
    | ((Dec (_, v_))::vs_, t, (n, i)) ->
        let Vt = I.EClo (v_, t) in
        (::) ((compileDClause opt ((T.coerceCtx Psi), Vt)), I.id,
               (I.targetHead Vt))
          compileBlock
          (vs_,
            (I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
            (n, (i + 1))) end in
let rec compileCtx' =
  begin function
  | I.Null -> I.Null
  | Decl (g_, Dec (_, a_)) ->
      let Ha = I.targetHead a_ in
      I.Decl
        ((compileCtx' g_),
          (CompSyn.Dec ((compileDClause opt (g_, a_)), I.id, Ha)))
  | Decl (g_, BDec (_, (c, s))) ->
      let (g_, l_) = I.constBlock c in
      let dpool = compileCtx' g_ in
      let n = I.ctxLength dpool in
      ((I.Decl (dpool, (CompSyn.BDec (compileBlock (l_, s, (n, 1))))))
        (* this is inefficient! -cs *)) end in
let rec compilePsi' =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, UDec (Dec (_, a_))) ->
      let Ha = I.targetHead a_ in
      I.Decl
        ((compilePsi' Psi),
          (CompSyn.Dec
             ((compileDClause opt ((T.coerceCtx Psi), a_)), I.id, Ha)))
  | Decl (Psi, UDec (BDec (_, (c, s)))) ->
      let (g_, l_) = I.constBlock c in
      let dpool = compileCtx' g_ in
      let n = I.ctxLength dpool in
      ((I.Decl (dpool, (CompSyn.BDec (compileBlock (l_, s, (n, 1))))))
        (* this is inefficient! -cs *))
  | Decl (Psi, PDec _) -> I.Decl ((compilePsi' Psi), CompSyn.PDec) end in
C.DProg ((T.coerceCtx Psi), (compilePsi' Psi))
let rec installClause fromCS (a, a_) =
  begin match !C.optimize with
  | C.No ->
      C.sProgInstall
        (a, (C.SClause (compileDClauseN fromCS true (I.Null, a_))))
  | C.LinearHeads ->
      C.sProgInstall
        (a, (C.SClause (compileDClauseN fromCS true (I.Null, a_))))
  | C.Indexing ->
      let ((g_, Head), r_) =
        compileSClauseN fromCS (I.Null, I.Null, (Whnf.normalize (a_, I.id))) in
      let _ =
        C.sProgInstall
          (a, (C.SClause (compileDClauseN fromCS true (I.Null, a_)))) in
      (begin match Head with
       | None -> raise (Error "Install via normal index")
       | Some (h_, Eqs) ->
           SubTree.sProgInstall
             ((cidFromHead (I.targetHead a_)), (C.Head (h_, g_, Eqs, a)), r_) end) end
let rec compileConDec arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (fromCS, (a, ConDec (_, _, _, _, a_, I.Type))) ->
      installClause fromCS (a, a_)
  | (fromCS, (a, SkoDec (_, _, _, a_, I.Type))) ->
      (begin match !C.optimize with
       | C.No ->
           C.sProgInstall
             (a, (C.SClause (compileDClauseN fromCS true (I.Null, a_))))
       | _ ->
           C.sProgInstall
             (a, (C.SClause (compileDClauseN fromCS true (I.Null, a_)))) end)
  | (I.Clause, (a, ConDef (_, _, _, _, a_, I.Type, _))) ->
      C.sProgInstall
        (a,
          (C.SClause
             (compileDClauseN I.Clause true
                (I.Null, (Whnf.normalize (a_, I.id))))))
  | (_, _) -> () end(* we don't use substitution tree indexing for skolem constants yet -bp*)
let rec install fromCS cid = compileConDec fromCS (cid, (I.sgnLookup cid))
let rec sProgReset () = begin SubTree.sProgReset (); C.sProgReset () end end



module CPrint =
  (CPrint)(struct
                  module Print = Print
                  module Formatter = Formatter
                  module Names = Names
                end)
module SubTree =
  (SubTree)(struct
                   module IntSyn' = IntSyn
                   module Whnf = Whnf
                   module Unify = UnifyTrail
                   module CompSyn' = CompSyn
                   module Print = Print
                   module CPrint = CPrint
                   module Names = Names
                   module Formatter = Formatter
                   module CSManager = CSManager
                   module Table = IntRedBlackTree
                   module RBSet = RBSet
                 end)
module Compile =
  (Compile)(struct
                   module Whnf = Whnf
                   module TypeCheck = TypeCheck
                   module SubTree = SubTree
                   module CPrint = CPrint
                   module Print = Print
                   module Names = Names
                 end)
module Assign =
  (Assign)(struct
                  module Whnf = Whnf
                  module Unify = UnifyTrail
                  module Print = Print
                end)