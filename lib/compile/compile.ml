
(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type COMPILE  =
  sig
    (*! structure IntSyn: INTSYN !*)
    (*! structure CompSyn: COMPSYN !*)
    exception Error of string 
    type __Opt = CompSyn.__Opt
    val optimize : __Opt ref
    val install : IntSyn.__ConDecForm -> IntSyn.cid -> unit
    val sProgReset : unit -> unit
    val compileCtx : bool -> IntSyn.__Dec IntSyn.__Ctx -> CompSyn.__DProg
    val compileGoal :
      (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) -> CompSyn.__Goal
    (* for the meta theorem prover  --cs *)
    val compilePsi : bool -> Tomega.__Dec IntSyn.__Ctx -> CompSyn.__DProg
  end;;




(* Compilation for indexing with substitution trees *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield,
             Roberto Virga, Brigitte Pientka *)
module Compile(Compile:sig
                         (*! structure IntSyn' : INTSYN !*)
                         (*! structure CompSyn' : COMPSYN !*)
                         (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                         module Whnf : WHNF
                         module TypeCheck : TYPECHECK
                         module SubTree : SUBTREE
                         module CPrint : CPRINT
                         module Print : PRINT
                         (*! sharing Whnf.IntSyn = IntSyn' !*)
                         (* sharing TypeCheck.IntSyn = IntSyn' !*)
                         (*! sharing SubTree.IntSyn = IntSyn' !*)
                         (*! sharing SubTree.CompSyn = CompSyn' !*)
                         (* CPrint currently unused *)
                         (*! sharing CPrint.IntSyn = IntSyn' !*)
                         (*! sharing CPrint.CompSyn = CompSyn' !*)
                         (* CPrint currently unused *)
                         (*! sharing Print.IntSyn = IntSyn' !*)
                         module Names : NAMES
                       end) : COMPILE =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (* FIX: need to associate errors with occurrences -kw *)
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module C = CompSyn
    type __Duplicates =
      | BVAR of int 
      | FGN 
      | DEF of int 
    let rec notCS = function | I.FromCS -> false__ | _ -> true__
    type __Opt = CompSyn.__Opt
    let optimize = CompSyn.optimize
    let rec cidFromHead = function | Const c -> c | Def c -> c
    (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *)
    let rec isConstraint =
      function
      | Const c ->
          (match I.constStatus c with | Constraint _ -> true__ | _ -> false__)
      | H -> false__
    (* head (A) = H, the head of __v

       Invariants:
       __g |- A : type, A enf
       A = H @ S
    *)
    let rec head = function | Root (h, _) -> h | Pi (_, A) -> head A
    let rec seen (i, Vars) = List.exists (function | (d, x) -> x = i) Vars
    (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
    (*
  fun etaSpine' (I.Nil, n) = (n=0)
    | etaSpine' (I.App(__u, S), n) =
        if Whnf.etaContract __u = n then etaSpine' (S, n-1)
        else false

  fun etaSpine (S, n) = etaSpine' (S, n) handle Eta => false
*)
    let rec etaSpine =
      function
      | (I.Nil, n) -> n = 0
      | (App (Root (BVar k, I.Nil), S), n) ->
          (k = n) && (etaSpine (S, (n - 1)))
      | (App (A, S), n) -> false__
    (* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *)
    let rec collectHead =
      function
      | ((BVar k as h), S, K, Vars, depth) ->
          ((if k > depth
            then
              (if etaSpine (S, depth)
               then
                 (if seen ((k - depth), Vars)
                  then (((depth, (BVAR (k - depth))) :: K), Vars, true__)
                  else (K, ((depth, (k - depth)) :: Vars), false__))
               else (((depth, (BVAR (k - depth))) :: K), Vars, true__))
            else (K, Vars, false__))
          (* check if h is an eta-expanded variable *)
          (* h is a locally bound variable and need not be collected *))
      | (_, _, K, Vars, depth) -> (K, Vars, false__)(* check if k is in Vars *)
    (* collectExp (__u, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in __u or S
      K' - K = expressions in __u or S to be replaced

      __u, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *)
    let rec collectSpine =
      function
      | (I.Nil, K, Vars, depth) -> (K, Vars)
      | (App (__u, S), K, Vars, depth) ->
          let (K', Vars') = collectExp (__u, K, Vars, depth) in
          collectSpine (S, K', Vars', depth)
    let rec collectExp =
      function
      | (Root ((BVar k as h), S), K, Vars, depth) ->
          let (K', Vars', replaced) = collectHead (h, S, K, Vars, depth) in
          if replaced
          then (K', Vars')
          else collectSpine (S, K', Vars', depth)
      | ((Root (Def k, S) as __u), K, Vars, depth) ->
          (((depth, (DEF k)) :: K), Vars)
      | (Root (h, S), K, Vars, depth) -> collectSpine (S, K, Vars, depth)
      | (Lam (__d, __u), K, Vars, depth) -> collectExp (__u, K, Vars, (depth + 1))
      | (FgnExp (cs, fe), K, Vars, depth) -> (((depth, FGN) :: K), Vars)
      (* don't collect __d, since it is ignored in unification *)(* | collectExp (I.Uni(__l), K, Vars, depth) = (K, Vars) *)
      (* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)(* h is either const or skonst of def*)
    (* no EVars, since __u in NF *)
    (* shiftHead (H, depth, total) = H'
     shiftExp (__u, depth, total) = __u'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: __u is NF, S is in NF
  *)
    let rec shiftHead =
      function
      | ((BVar k as h), depth, total) ->
          if k > depth then I.BVar (k + total) else I.BVar k
      | ((Const k as h), depth, total) -> h
      | ((Def k as h), depth, total) -> h
      | ((NSDef k as h), depth, total) -> h
      | ((FgnConst k as h), depth, total) -> h
      | ((Skonst k as h), depth, total) -> h
    let rec shiftExp =
      function
      | (Root (h, S), depth, total) ->
          I.Root
            ((shiftHead (h, depth, total)), (shiftSpine (S, depth, total)))
      | (Uni (__l), _, _) -> I.Uni __l
      | (Lam (__d, __u), depth, total) ->
          I.Lam
            ((shiftDec (__d, depth, total)),
              (shiftExp (__u, (depth + 1), total)))
      | (Pi ((__d, P), __u), depth, total) ->
          I.Pi
            (((shiftDec (__d, depth, total)), P),
              (shiftExp (__u, (depth + 1), total)))
      | (FgnExp csfe, depth, total) ->
          I.FgnExpStd.Map.apply csfe
            (function
             | __u -> shiftExp ((Whnf.normalize (__u, I.id)), depth, total))
      (* Tue Apr  2 12:10:24 2002 -fp -bp *)(* this is overkill and could be very expensive for deeply nested foreign exps *)
      (* calling normalize here because __u may not be normal *)
    let rec shiftSpine =
      function
      | (I.Nil, _, _) -> I.Nil
      | (App (__u, S), depth, total) ->
          I.App
            ((shiftExp (__u, depth, total)), (shiftSpine (S, depth, total)))
    let rec shiftDec (Dec (x, __v), depth, total) =
      I.Dec (x, (shiftExp (__v, depth, total)))
    (* linearHead (Gl, h, S, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

   if G0, Gl |- h @ S and
      h is a duplicate (i.e. it is either not fully applied pattern
       or it has already occured and is an element of Vars)

      |Gl| = depth, Gl is local context of BVars
   then
      h' is a new variable standing for a new AVar
      M = Root(h, S) where each variable in G0 is shifted by total
      N = Root(h', I.Nil)

   and
      Eqn accumulates residual equation UnifyEq(Gl, M, N)
  *)
    let rec linearHead =
      function
      | (__g, (BVar k as h), S, left, Vars, depth, total) ->
          if k > depth
          then
            (if etaSpine (S, depth)
             then
               (if seen ((k - depth), Vars)
                then ((left - 1), Vars, (I.BVar (left + depth)), true__)
                else
                  (left, ((depth, (k - depth)) :: Vars),
                    (I.BVar (k + total)), false__))
             else ((left - 1), Vars, (I.BVar (left + depth)), true__))
          else (left, Vars, h, false__)
      | (__g, (Const k as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (__g, (FgnConst (k, ConDec) as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (__g, (Skonst k as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)(*
     | linearHead(__g, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)
    (* Def cannot occur *)
    (* linearExp (Gl, __u, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root

     left' = left - #replaced expressions in __u
     Vars' = all BVars in G0 seen in __u
     N = copy of __u with replaced expressions
     Eqn = residual equations

     "For any __u', __u = __u' iff (N = __u' and Eqn)"
  *)
    let rec linearExp =
      function
      | (Gl, (Root ((Def k as h), S) as __u), left, Vars, depth, total, eqns)
          ->
          let N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let __u' = shiftExp (__u, depth, total) in
          ((left - 1), Vars, N, (C.UnifyEq (Gl, __u', N, eqns)))
      | (Gl, (Root (h, S) as __u), left, Vars, depth, total, eqns) ->
          let (left', Vars', h', replaced) =
            linearHead (Gl, h, S, left, Vars, depth, total) in
          ((if replaced
            then
              let N = I.Root (h', I.Nil) in
              let __u' = shiftExp (__u, depth, total) in
              (left', Vars, N, (C.UnifyEq (Gl, __u', N, eqns)))
            else
              (let (left'', Vars'', S', eqns') =
                 linearSpine (Gl, S, left', Vars', depth, total, eqns) in
               (left'', Vars'', (I.Root (h', S')), eqns')))
            (* h = h' not replaced *))
      | (Gl, Lam (__d, __u), left, Vars, depth, total, eqns) ->
          let __d' = shiftDec (__d, depth, total) in
          let (left', Vars', __u', eqns') =
            linearExp
              ((I.Decl (Gl, __d')), __u, left, Vars, (depth + 1), total, eqns) in
          (left', Vars', (I.Lam (__d', __u')), eqns')
      | (Gl, (FgnExp (cs, ops) as __u), left, Vars, depth, total, eqns) ->
          let N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let __u' = shiftExp (__u, depth, total) in
          ((left - 1), Vars, N, (C.UnifyEq (Gl, __u', N, eqns)))(*
     | linearExp (Gl, __u as I.Uni(__l), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(__l), eqns)
     *)
      (* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
    let rec linearSpine =
      function
      | (Gl, I.Nil, left, Vars, depth, total, eqns) ->
          (left, Vars, I.Nil, eqns)
      | (Gl, App (__u, S), left, Vars, depth, total, eqns) ->
          let (left', Vars', __u', eqns') =
            linearExp (Gl, __u, left, Vars, depth, total, eqns) in
          let (left'', Vars'', S', eqns'') =
            linearSpine (Gl, S, left', Vars', depth, total, eqns') in
          (left'', Vars'', (I.App (__u', S')), eqns'')
    (* SClo(S, s') cannot occur *)
    (*  compileLinearHead (__g, R as I.Root (h, S)) = r

       r is residual goal
       if __g |- R and R might not be linear

       then

           __g |- H ResGoal  and H is linear
       and of the form
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *)
    let rec compileLinearHead (__g, (Root (h, S) as R)) =
      let (K, _) = collectExp (R, nil, nil, 0) in
      let left = List.length K in
      let (left', _, R', Eqs) =
        linearExp (I.Null, R, left, nil, 0, left, C.Trivial) in
      let rec convertKRes =
        function
        | (ResG, nil, 0) -> ResG
        | (ResG, (d, k)::K, i) ->
            C.Axists
              ((I.ADec ((Some ((^) "A" Int.toString i)), d)),
                (convertKRes (ResG, K, (i - 1)))) in
      let r = convertKRes ((C.Assign (R', Eqs)), (List.rev K), left) in
      if (!Global.chatter) >= 6
      then
        (print "\nClause LH Eqn"; print (CPrint.clauseToString "\t" (__g, r)))
      else ();
      r
    (*  compileSbtHead (__g, R as I.Root (h, S)) = r

       r is residual goal
       if __g |- R and R might not be linear

       then

           __g |- H ResGoal  and H is linear

  *)
    let rec compileSbtHead (__g, (Root (h, S) as H)) =
      let (K, _) = collectExp (H, nil, nil, 0) in
      let left = List.length K in
      let (left', _, H', Eqs) =
        linearExp (I.Null, H, left, nil, 0, left, C.Trivial) in
      let rec convertKRes =
        function
        | (__g, nil, 0) -> __g
        | (__g, (d, k)::K, i) ->
            convertKRes
              ((I.Decl (__g, (I.ADec ((Some ((^) "AVar " Int.toString i)), d)))),
                K, (i - 1)) in
      let __g' = convertKRes (__g, (List.rev K), left) in
      ((if (!Global.chatter) >= 6
        then
          (print "\nClause Sbt Eqn";
           print (CPrint.clauseToString "\t" (__g', (C.Assign (H', Eqs)))))
        else ();
        (__g', (Some (H', Eqs))))
        (* insert R' together with Eqs and __g and sc C.True *))
    (* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If __g |- A : type,  A enf
        A has no existential type variables
     then __g |- A ~> g  (A compiles to goal g)
     and  __g |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *)
    let rec compileGoalN arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (fromCS, (__g, (Root _ as R))) -> C.Atom R
      | (fromCS, (__g, Pi ((Dec (_, A1), I.No), A2))) ->
          let Ha1 = I.targetHead A1 in
          let R = compileDClauseN fromCS false__ (__g, A1) in
          let goal =
            compileGoalN fromCS ((I.Decl (__g, (I.Dec (None, A1)))), A2) in
          ((C.Impl (R, A1, Ha1, goal))
            (* A1 is used to build the proof term, Ha1 for indexing *)
            (* never optimize when compiling local assumptions *))
      | (fromCS, (__g, Pi (((Dec (_, A1) as __d), I.Maybe), A2))) ->
          if (notCS fromCS) && (isConstraint (head A1))
          then raise (Error "Constraint appears in dynamic clause position")
          else C.All (__d, (compileGoalN fromCS ((I.Decl (__g, __d)), A2)))
      (* A = {x:A1} A2 *)(* A = A1 -> A2 *)(* A = H @ S *)
    let rec compileGoal fromCS (__g, (A, s)) =
      compileGoalN fromCS (__g, (Whnf.normalize (A, s)))
    let rec compileDClauseN arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (fromCS, opt, (__g, (Root (h, S) as R))) ->
          if opt && ((!optimize) = C.LinearHeads)
          then compileLinearHead (__g, R)
          else
            if (notCS fromCS) && (isConstraint h)
            then
              raise (Error "Constraint appears in dynamic clause position")
            else C.Eq R
      | (fromCS, opt, (__g, Pi (((Dec (_, A1) as __d), I.No), A2))) ->
          C.And
            ((compileDClauseN fromCS opt ((I.Decl (__g, __d)), A2)), A1,
              (compileGoalN fromCS (__g, A1)))
      | (fromCS, opt, (__g, Pi (((Dec (_, A1) as __d), I.Meta), A2))) ->
          C.In
            ((compileDClauseN fromCS opt ((I.Decl (__g, __d)), A2)), A1,
              (compileGoalN fromCS (__g, A1)))
      | (fromCS, opt, (__g, Pi ((__d, I.Maybe), A2))) ->
          C.Exists (__d, (compileDClauseN fromCS opt ((I.Decl (__g, __d)), A2)))
      (* A = {x:A1} A2 *)(* A = {x: A1} A2, x  meta variable occuring in A2 *)
      (* A = A1 -> A2 *)
    (*  compileDClauseN _ should not arise by invariants *)
    (* Compilation of (static) program clauses *)
    (* compileSubgoals __g' (n, Stack, __g) = Subgoals  (top level)

     Invariants:
     If __g : Stack
        __g' ctx where __g' = __g, GAVar
     then Stack ~> subgoals  (Stack compiles to subgoals)
     and  __g' |- subgoals
  *)
    let rec compileSubgoals arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (fromCS, __g', (n, Decl (Stack, I.No), Decl (__g, Dec (_, A)))) ->
          let sg = compileSubgoals fromCS __g' ((n + 1), Stack, __g) in
          ((C.Conjunct
              ((compileGoal fromCS (__g', (A, (I.Shift (n + 1))))),
                (I.EClo (A, (I.Shift (n + 1)))), sg))
            (* __g |- A and __g' |- A[^(n+1)] *))
      | (fromCS, __g', (n, Decl (Stack, I.Maybe), Decl (__g, Dec (_, A1)))) ->
          compileSubgoals fromCS __g' ((n + 1), Stack, __g)
      | (fromCS, __g', (n, I.Null, I.Null)) -> C.True
    (* compileSClause (Stack, __g, A) => (Head, SubGoals) (top-level)
     if A is a type interpreted as a clause and (Head, SubGoals)
     is its compiled form.

     Invariants:
     If __g |- A : type, A enf
        A has no existential type variables
     then __g |- A ~> (Head, subgoals) ((A compiles to head and subgoals)
          where GAVar, __g |- Head and GAVar, __g |- subgoals
          and Head is linear and __g' = GAVar, __g
  *)
    let rec compileSClauseN arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (fromCS, (Stack, __g, (Root (h, S) as R))) ->
          let (__g', Head) = compileSbtHead (__g, R) in
          let d = (-) (I.ctxLength __g') I.ctxLength __g in
          let Sgoals = compileSubgoals fromCS __g' (d, Stack, __g) in
          ((((__g', Head), Sgoals))
            (* __g' |- Sgoals  and __g' |- ^d : __g *))
      | (fromCS, (Stack, __g, Pi (((Dec (_, A1) as __d), I.No), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.No)), (I.Decl (__g, __d)), A2)
      | (fromCS, (Stack, __g, Pi (((Dec (_, A1) as __d), I.Meta), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Meta)), (I.Decl (__g, __d)), A2)
      | (fromCS, (Stack, __g, Pi (((Dec (_, A1) as __d), I.Maybe), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Maybe)), (I.Decl (__g, __d)), A2)
    let rec compileDClause opt (__g, A) =
      compileDClauseN I.Ordinary opt (__g, (Whnf.normalize (A, I.id)))
    let rec compileGoal (__g, A) =
      compileGoalN I.Ordinary (__g, (Whnf.normalize (A, I.id)))
    (* compileCtx __g = (__g, dPool)

     Invariants:
     If |- __g ctx,
     then |- __g ~> dPool  (context __g compile to clause pool dPool)
     and  |- dPool  dpool
  *)
    let rec compileCtx opt (__g) =
      let rec compileBlock =
        function
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, __v))::__Vs, t, (n, i)) ->
            let Vt = I.EClo (__v, t) in
            (::) ((compileDClause opt (__g, Vt)), I.id, (I.targetHead Vt))
              compileBlock
              (__Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let rec compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (__g, Dec (_, A)) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compileCtx' __g),
                (CompSyn.Dec ((compileDClause opt (__g, A)), I.id, Ha)))
        | Decl (__g, BDec (_, (c, s))) ->
            let (__g, __l) = I.constBlock c in
            let dpool = compileCtx' __g in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__l, s, (n, 1))))))
              (* this is inefficient! -cs *)) in
      C.DProg (__g, (compileCtx' __g))
    (* compile __g = (__g, dPool)

     Invariants:
     If |- __g ctx,
     then |- __g ~> dPool  (context __g compile to clause pool dPool)
     and  |- dPool  dpool
  *)
    let rec compilePsi opt (Psi) =
      let rec compileBlock =
        function
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, __v))::__Vs, t, (n, i)) ->
            let Vt = I.EClo (__v, t) in
            (::) ((compileDClause opt ((T.coerceCtx Psi), Vt)), I.id,
                   (I.targetHead Vt))
              compileBlock
              (__Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let rec compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (__g, Dec (_, A)) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compileCtx' __g),
                (CompSyn.Dec ((compileDClause opt (__g, A)), I.id, Ha)))
        | Decl (__g, BDec (_, (c, s))) ->
            let (__g, __l) = I.constBlock c in
            let dpool = compileCtx' __g in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__l, s, (n, 1))))))
              (* this is inefficient! -cs *)) in
      let rec compilePsi' =
        function
        | I.Null -> I.Null
        | Decl (Psi, UDec (Dec (_, A))) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compilePsi' Psi),
                (CompSyn.Dec
                   ((compileDClause opt ((T.coerceCtx Psi), A)), I.id, Ha)))
        | Decl (Psi, UDec (BDec (_, (c, s)))) ->
            let (__g, __l) = I.constBlock c in
            let dpool = compileCtx' __g in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__l, s, (n, 1))))))
              (* this is inefficient! -cs *))
        | Decl (Psi, PDec _) -> I.Decl ((compilePsi' Psi), CompSyn.PDec) in
      C.DProg ((T.coerceCtx Psi), (compilePsi' Psi))
    (* installClause fromCS (a, A) = ()
     Effect: compiles and installs compiled form of A according to
             the specified compilation strategy
  *)
    let rec installClause fromCS (a, A) =
      match !C.optimize with
      | C.No ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
      | C.LinearHeads ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
      | C.Indexing ->
          let ((__g, Head), R) =
            compileSClauseN fromCS
              (I.Null, I.Null, (Whnf.normalize (A, I.id))) in
          let _ =
            C.sProgInstall
              (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A)))) in
          (match Head with
           | None -> raise (Error "Install via normal index")
           | Some (H, Eqs) ->
               SubTree.sProgInstall
                 ((cidFromHead (I.targetHead A)), (C.Head (H, __g, Eqs, a)), R))
    (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
    (* Defined constants are currently not compiled *)
    let rec compileConDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (fromCS, (a, ConDec (_, _, _, _, A, I.Type))) ->
          installClause fromCS (a, A)
      | (fromCS, (a, SkoDec (_, _, _, A, I.Type))) ->
          (match !C.optimize with
           | C.No ->
               C.sProgInstall
                 (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
           | _ ->
               C.sProgInstall
                 (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A)))))
      | (I.Clause, (a, ConDef (_, _, _, _, A, I.Type, _))) ->
          C.sProgInstall
            (a,
              (C.SClause
                 (compileDClauseN I.Clause true__
                    (I.Null, (Whnf.normalize (A, I.id))))))
      | (_, _) -> ()(* we don't use substitution tree indexing for skolem constants yet -bp*)
    let rec install fromCS cid =
      compileConDec fromCS (cid, (I.sgnLookup cid))
    let rec sProgReset () = SubTree.sProgReset (); C.sProgReset ()
  end ;;




(* Now in compsyn.fun *)
(*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !*)
module CPrint =
  (Make_CPrint)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  (*! structure CompSyn' = CompSyn !*)
                  module Print = Print
                  module Formatter = Formatter
                  module Names = Names
                end)
module SubTree =
  (Make_SubTree)(struct
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
  (Make_Compile)(struct
                   (*! structure IntSyn' = IntSyn !*)
                   (*! structure CompSyn' = CompSyn !*)
                   module Whnf = Whnf
                   module TypeCheck = TypeCheck
                   module SubTree = SubTree
                   module CPrint = CPrint
                   module Print = Print
                   module Names = Names
                 end)
module Assign =
  (Make_Assign)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  module Whnf = Whnf
                  module Unify = UnifyTrail
                  module Print = Print
                end);;
