
module type COMPILE  =
  sig
    exception Error of
      ((string)(*! structure CompSyn: COMPSYN !*)(*! structure IntSyn: INTSYN !*)
      (* Modified: Frank Pfenning *)(* Modified: Carsten Schuermann *)
      (* Modified: Jeff Polakow *)(* Author: Iliano Cervesato *)
      (* Compiler *)) 
    type __Opt = CompSyn.__Opt
    val optimize : __Opt ref
    val install : IntSyn.__ConDecForm -> IntSyn.cid -> unit
    val sProgReset : unit -> unit
    val compileCtx : bool -> IntSyn.__Dec IntSyn.__Ctx -> CompSyn.__DProg
    val compileGoal :
      (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) -> CompSyn.__Goal
    val compilePsi :
      bool ->
        Tomega.__Dec IntSyn.__Ctx ->
          ((CompSyn.__DProg)(* for the meta theorem prover  --cs *))
  end;;




module Compile(Compile:sig
                         module Whnf : WHNF
                         module TypeCheck : TYPECHECK
                         module SubTree : SUBTREE
                         module CPrint : CPRINT
                         module Print : PRINT
                         module Names :
                         ((NAMES)(* Compilation for indexing with substitution trees *)
                         (* Author: Iliano Cervesato *)
                         (* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield,
             Roberto Virga, Brigitte Pientka *)
                         (*! structure IntSyn' : INTSYN !*)
                         (*! structure CompSyn' : COMPSYN !*)(*! sharing CompSyn'.IntSyn = IntSyn' !*)
                         (*! sharing Whnf.IntSyn = IntSyn' !*)(* sharing TypeCheck.IntSyn = IntSyn' !*)
                         (*! sharing SubTree.IntSyn = IntSyn' !*)
                         (*! sharing SubTree.CompSyn = CompSyn' !*)
                         (* CPrint currently unused *)
                         (*! sharing CPrint.IntSyn = IntSyn' !*)
                         (*! sharing CPrint.CompSyn = CompSyn' !*)
                         (* CPrint currently unused *)
                         (*! sharing Print.IntSyn = IntSyn' !*))
                       end) : COMPILE =
  struct
    exception Error of
      ((string)(* FIX: need to associate errors with occurrences -kw *)
      (*! sharing Names.IntSyn = IntSyn' !*)) 
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
    let rec isConstraint =
      function
      | Const
          ((c)(* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *))
          ->
          (match I.constStatus c with | Constraint _ -> true__ | _ -> false__)
      | H -> false__
    let rec head =
      function
      | Root
          (((h)(* head (A) = H, the head of V

       Invariants:
       g |- A : type, A enf
       A = H @ S
    *)),
           _)
          -> h
      | Pi (_, A) -> head A
    let rec seen (i, Vars) = List.exists (function | (d, x) -> x = i) Vars
    let rec etaSpine =
      function
      | (((I.Nil)(* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
         (*
  fun etaSpine' (I.Nil, n) = (n=0)
    | etaSpine' (I.App(U, S), n) =
        if Whnf.etaContract U = n then etaSpine' (S, n-1)
        else false

  fun etaSpine (S, n) = etaSpine' (S, n) handle Eta => false
*)),
         n) -> n = 0
      | (App (Root (BVar k, I.Nil), S), n) ->
          (k = n) && (etaSpine (S, (n - 1)))
      | (App (A, S), n) -> false__
    let rec collectHead =
      function
      | ((BVar
            ((k)(* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *))
            as h),
         S, K, Vars, depth) ->
          if k > depth
          then
            (if etaSpine (S, depth)
             then
               (if seen ((k - depth), Vars)
                then (((depth, (BVAR (k - depth))) :: K), Vars, true__)
                else (K, ((depth, (k - depth)) :: Vars), false__))
             else (((depth, (BVAR (k - depth))) :: K), Vars, true__))
          else
            (((K)
              (* check if k is in Vars *)(* check if h is an eta-expanded variable *)
              (* h is a locally bound variable and need not be collected *)),
              Vars, false__)
      | (_, _, K, Vars, depth) -> (K, Vars, false__)
    let rec collectSpine =
      function
      | (((I.Nil)(* collectExp (U, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in U or S
      K' - K = expressions in U or S to be replaced

      U, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *)),
         K, Vars, depth) -> (K, Vars)
      | (App (U, S), K, Vars, depth) ->
          let (K', Vars') = collectExp (U, K, Vars, depth) in
          collectSpine (S, K', Vars', depth)
    let rec collectExp =
      function
      | (Root ((BVar k as h), S), K, Vars, depth) ->
          let (K', Vars', replaced) = collectHead (h, S, K, Vars, depth) in
          if replaced
          then (K', Vars')
          else collectSpine (S, K', Vars', depth)
      | ((Root (Def k, S) as U), K, Vars, depth) ->
          (((depth, (DEF k)) :: K), Vars)
      | (Root
         (((h)(* h is either const or skonst of def*)), S),
         K, Vars, depth) -> collectSpine (S, K, Vars, depth)
      | (Lam
         (((D)(* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)
          (* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)),
          U),
         K, Vars, depth) ->
          collectExp
            (((U)
              (* don't collect D, since it is ignored in unification *)),
              K, Vars, (depth + 1))
      | (FgnExp (cs, fe), K, Vars, depth) -> (((depth, FGN) :: K), Vars)
    let rec shiftHead =
      function
      | ((BVar
            ((k)(* no EVars, since U in NF *)(* shiftHead (H, depth, total) = H'
     shiftExp (U, depth, total) = U'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: U is NF, S is in NF
  *))
            as h),
         depth, total) -> if k > depth then I.BVar (k + total) else I.BVar k
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
      | (Uni (L), _, _) -> I.Uni L
      | (Lam (D, U), depth, total) ->
          I.Lam
            ((shiftDec (D, depth, total)),
              (shiftExp (U, (depth + 1), total)))
      | (Pi ((D, P), U), depth, total) ->
          I.Pi
            (((shiftDec (D, depth, total)), P),
              (shiftExp (U, (depth + 1), total)))
      | (FgnExp csfe, depth, total) ->
          I.FgnExpStd.Map.apply ((csfe)
            (* calling normalize here because U may not be normal *)
            (* this is overkill and could be very expensive for deeply nested foreign exps *)
            (* Tue Apr  2 12:10:24 2002 -fp -bp *))
            (function
             | U -> shiftExp ((Whnf.normalize (U, I.id)), depth, total))
    let rec shiftSpine =
      function
      | (I.Nil, _, _) -> I.Nil
      | (App (U, S), depth, total) ->
          I.App
            ((shiftExp (U, depth, total)), (shiftSpine (S, depth, total)))
    let rec shiftDec (Dec (x, V), depth, total) =
      I.Dec (x, (shiftExp (V, depth, total)))
    let rec linearHead =
      function
      | (((g)(* linearHead (Gl, h, S, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

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
  *)),
         (BVar k as h), S, left, Vars, depth, total) ->
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
      | (g, (Const k as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (((g)(*
     | linearHead(g, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)),
         (FgnConst (k, ConDec) as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (g, (Skonst k as h), S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
    let rec linearExp =
      function
      | (((Gl)(* Def cannot occur *)(* linearExp (Gl, U, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root

     left' = left - #replaced expressions in U
     Vars' = all BVars in G0 seen in U
     N = copy of U with replaced expressions
     Eqn = residual equations

     "For any U', U = U' iff (N = U' and Eqn)"
  *)),
         (Root ((Def k as h), S) as U), left, Vars, depth, total, eqns) ->
          let N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let U' = shiftExp (U, depth, total) in
          ((left - 1), Vars, N, (C.UnifyEq (Gl, U', N, eqns)))
      | (Gl, (Root (h, S) as U), left, Vars, depth, total, eqns) ->
          let (left', Vars', h', replaced) =
            linearHead (Gl, h, S, left, Vars, depth, total) in
          if replaced
          then
            let N = I.Root (h', I.Nil) in
            let U' = shiftExp (U, depth, total) in
            (left', Vars, N, (C.UnifyEq (Gl, U', N, eqns)))
          else
            (let (((left'')(* h = h' not replaced *)),
                  Vars'', S', eqns')
               = linearSpine (Gl, S, left', Vars', depth, total, eqns) in
             (left'', Vars'', (I.Root (h', S')), eqns'))
      | (((Gl)(* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
         (*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)),
         Lam (D, U), left, Vars, depth, total, eqns) ->
          let D' = shiftDec (D, depth, total) in
          let (left', Vars', U', eqns') =
            linearExp
              ((I.Decl (Gl, D')), U, left, Vars, (depth + 1), total, eqns) in
          (left', Vars', (I.Lam (D', U')), eqns')
      | (Gl, (FgnExp (cs, ops) as U), left, Vars, depth, total, eqns) ->
          let N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let U' = shiftExp (U, depth, total) in
          ((left - 1), Vars, N, (C.UnifyEq (Gl, U', N, eqns)))
    let rec linearSpine =
      function
      | (Gl, I.Nil, left, Vars, depth, total, eqns) ->
          (left, Vars, I.Nil, eqns)
      | (Gl, App (U, S), left, Vars, depth, total, eqns) ->
          let (left', Vars', U', eqns') =
            linearExp (Gl, U, left, Vars, depth, total, eqns) in
          let (left'', Vars'', S', eqns'') =
            linearSpine (Gl, S, left', Vars', depth, total, eqns') in
          (left'', Vars'', (I.App (U', S')), eqns'')
    let rec compileLinearHead
      (((g)(* SClo(S, s') cannot occur *)(*  compileLinearHead (g, R as I.Root (h, S)) = r

       r is residual goal
       if g |- R and R might not be linear

       then

           g |- H ResGoal  and H is linear
       and of the form
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *)),
       (Root (h, S) as R))
      =
      let (K, _) = collectExp (R, nil, nil, 0) in
      let left = List.length K in
      let (left', _, R', Eqs) =
        linearExp (I.Null, R, left, nil, 0, left, C.Trivial) in
      let convertKRes =
        function
        | (ResG, nil, 0) -> ResG
        | (ResG, (d, k)::K, i) ->
            C.Axists
              ((I.ADec ((SOME ((^) "A" Int.toString i)), d)),
                (convertKRes (ResG, K, (i - 1)))) in
      let r = convertKRes ((C.Assign (R', Eqs)), (List.rev K), left) in
      if (!Global.chatter) >= 6
      then
        (print "\nClause LH Eqn"; print (CPrint.clauseToString "\t" (g, r)))
      else ();
      r
    let rec compileSbtHead
      (((g)(*  compileSbtHead (g, R as I.Root (h, S)) = r

       r is residual goal
       if g |- R and R might not be linear

       then

           g |- H ResGoal  and H is linear

  *)),
       (Root (h, S) as H))
      =
      let (K, _) = collectExp (H, nil, nil, 0) in
      let left = List.length K in
      let (left', _, H', Eqs) =
        linearExp (I.Null, H, left, nil, 0, left, C.Trivial) in
      let convertKRes =
        function
        | (g, nil, 0) -> g
        | (g, (d, k)::K, i) ->
            convertKRes
              ((I.Decl (g, (I.ADec ((SOME ((^) "AVar " Int.toString i)), d)))),
                K, (i - 1)) in
      let g' = convertKRes (g, (List.rev K), left) in
      if (!Global.chatter) >= 6
      then
        (print "\nClause Sbt Eqn";
         print (CPrint.clauseToString "\t" (g', (C.Assign (H', Eqs)))))
      else ();
      (((g')
        (* insert R' together with Eqs and g and sc C.True *)),
        (SOME (H', Eqs)))
    let rec compileGoalN arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((fromCS)(* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If g |- A : type,  A enf
        A has no existential type variables
     then g |- A ~> g  (A compiles to goal g)
     and  g |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *)),
         (g, (Root _ as R))) -> C.Atom ((R)(* A = H @ S *))
      | (fromCS, (g, Pi ((Dec (_, A1), I.No), A2))) ->
          let ((Ha1)(* A = A1 -> A2 *)) = I.targetHead A1 in
          let R = compileDClauseN fromCS false__ (g, A1) in
          let goal =
            compileGoalN fromCS ((I.Decl (g, (I.Dec (NONE, A1)))), A2) in
          C.Impl
            (((R)
              (* A1 is used to build the proof term, Ha1 for indexing *)
              (* never optimize when compiling local assumptions *)),
              A1, Ha1, goal)
      | (fromCS, (g, Pi (((Dec (_, A1) as D), I.Maybe), A2))) ->
          if (notCS fromCS) && (isConstraint (head A1))
          then raise (Error "Constraint appears in dynamic clause position")
          else
            C.All
              (((D)(* A = {x:A1} A2 *)),
                (compileGoalN fromCS ((I.Decl (g, D)), A2)))
    let rec compileGoal
      ((fromCS)(*  compileGoalN _ should not arise by invariants *))
      (g, (A, s)) = compileGoalN fromCS (g, (Whnf.normalize (A, s)))
    let rec compileDClauseN arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (((fromCS)(* compileDClause A => g (top level)
     if A is a type interpreted as a clause and g is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If g |- A : type, A enf
        A has no existential type variables
     then g |- A ~> r  (A compiles to residual goal r)
     and  g |- r  resgoal
  *)),
         opt, (g, (Root (h, S) as R))) ->
          if opt && ((!optimize) = C.LinearHeads)
          then compileLinearHead (g, R)
          else
            if (notCS fromCS) && (isConstraint h)
            then
              raise (Error "Constraint appears in dynamic clause position")
            else C.Eq R
      | (fromCS, opt, (g, Pi (((Dec (_, A1) as D), I.No), A2))) ->
          C.And
            ((compileDClauseN ((fromCS)(* A = A1 -> A2 *))
                opt ((I.Decl (g, D)), A2)), A1,
              (compileGoalN fromCS (g, A1)))
      | (fromCS, opt, (g, Pi (((Dec (_, A1) as D), I.Meta), A2))) ->
          C.In
            ((compileDClauseN ((fromCS)
                (* A = {x: A1} A2, x  meta variable occuring in A2 *))
                opt ((I.Decl (g, D)), A2)), A1,
              (compileGoalN fromCS (g, A1)))
      | (fromCS, opt, (g, Pi ((D, I.Maybe), A2))) ->
          C.Exists
            (((D)(* A = {x:A1} A2 *)),
              (compileDClauseN fromCS opt ((I.Decl (g, D)), A2)))
    let rec compileSubgoals arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (((fromCS)(*  compileDClauseN _ should not arise by invariants *)
         (* Compilation of (static) program clauses *)
         (* compileSubgoals g' (n, Stack, g) = Subgoals  (top level)

     Invariants:
     If g : Stack
        g' ctx where g' = g, GAVar
     then Stack ~> subgoals  (Stack compiles to subgoals)
     and  g' |- subgoals
  *)),
         g', (n, Decl (Stack, I.No), Decl (g, Dec (_, A)))) ->
          let ((sg)(* g |- A and g' |- A[^(n+1)] *)) =
            compileSubgoals fromCS g' ((n + 1), Stack, g) in
          C.Conjunct
            ((compileGoal fromCS (g', (A, (I.Shift (n + 1))))),
              (I.EClo (A, (I.Shift (n + 1)))), sg)
      | (fromCS, g', (n, Decl (Stack, I.Maybe), Decl (g, Dec (_, A1)))) ->
          compileSubgoals fromCS g' ((n + 1), Stack, g)
      | (fromCS, g', (n, I.Null, I.Null)) -> C.True
    let rec compileSClauseN arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((fromCS)(* compileSClause (Stack, g, A) => (Head, SubGoals) (top-level)
     if A is a type interpreted as a clause and (Head, SubGoals)
     is its compiled form.

     Invariants:
     If g |- A : type, A enf
        A has no existential type variables
     then g |- A ~> (Head, subgoals) ((A compiles to head and subgoals)
          where GAVar, g |- Head and GAVar, g |- subgoals
          and Head is linear and g' = GAVar, g
  *)),
         (Stack, g, (Root (h, S) as R))) ->
          let (g', Head) = compileSbtHead (g, R) in
          let d = (-) (I.ctxLength g') I.ctxLength g in
          let Sgoals = compileSubgoals fromCS g' (d, Stack, g) in
          ((((g')(* g' |- Sgoals  and g' |- ^d : g *)),
             Head), Sgoals)
      | (fromCS, (Stack, g, Pi (((Dec (_, A1) as D), I.No), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.No)), (I.Decl (g, D)), A2)
      | (fromCS, (Stack, g, Pi (((Dec (_, A1) as D), I.Meta), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Meta)), (I.Decl (g, D)), A2)
      | (fromCS, (Stack, g, Pi (((Dec (_, A1) as D), I.Maybe), A2))) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Maybe)), (I.Decl (g, D)), A2)
    let rec compileDClause opt (g, A) =
      compileDClauseN I.Ordinary opt (g, (Whnf.normalize (A, I.id)))
    let rec compileGoal (g, A) =
      compileGoalN I.Ordinary (g, (Whnf.normalize (A, I.id)))
    let rec compileCtx
      ((opt)(* compileCtx g = (g, dPool)

     Invariants:
     If |- g ctx,
     then |- g ~> dPool  (context g compile to clause pool dPool)
     and  |- dPool  dpool
  *))
      (g) =
      let compileBlock =
        function
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, V))::Vs, t, (n, i)) ->
            let Vt = I.EClo (V, t) in
            (::) ((compileDClause opt (g, Vt)), I.id, (I.targetHead Vt))
              compileBlock
              (Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (g, Dec (_, A)) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compileCtx' g),
                (CompSyn.Dec ((compileDClause opt (g, A)), I.id, Ha)))
        | Decl (g, BDec (_, (c, s))) ->
            let (g, L) = I.constBlock c in
            let dpool = compileCtx' g in
            let n = I.ctxLength dpool in
            I.Decl
              (((dpool)(* this is inefficient! -cs *)),
                (CompSyn.BDec (compileBlock (L, s, (n, 1))))) in
      C.DProg (g, (compileCtx' g))
    let rec compilePsi
      ((opt)(* compile g = (g, dPool)

     Invariants:
     If |- g ctx,
     then |- g ~> dPool  (context g compile to clause pool dPool)
     and  |- dPool  dpool
  *))
      (Psi) =
      let compileBlock =
        function
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, V))::Vs, t, (n, i)) ->
            let Vt = I.EClo (V, t) in
            (::) ((compileDClause opt ((T.coerceCtx Psi), Vt)), I.id,
                   (I.targetHead Vt))
              compileBlock
              (Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (g, Dec (_, A)) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compileCtx' g),
                (CompSyn.Dec ((compileDClause opt (g, A)), I.id, Ha)))
        | Decl (g, BDec (_, (c, s))) ->
            let (g, L) = I.constBlock c in
            let dpool = compileCtx' g in
            let n = I.ctxLength dpool in
            I.Decl
              (((dpool)(* this is inefficient! -cs *)),
                (CompSyn.BDec (compileBlock (L, s, (n, 1))))) in
      let compilePsi' =
        function
        | I.Null -> I.Null
        | Decl (Psi, UDec (Dec (_, A))) ->
            let Ha = I.targetHead A in
            I.Decl
              ((compilePsi' Psi),
                (CompSyn.Dec
                   ((compileDClause opt ((T.coerceCtx Psi), A)), I.id, Ha)))
        | Decl (Psi, UDec (BDec (_, (c, s)))) ->
            let (g, L) = I.constBlock c in
            let dpool = compileCtx' g in
            let n = I.ctxLength dpool in
            I.Decl
              (((dpool)(* this is inefficient! -cs *)),
                (CompSyn.BDec (compileBlock (L, s, (n, 1)))))
        | Decl (Psi, PDec _) -> I.Decl ((compilePsi' Psi), CompSyn.PDec) in
      C.DProg ((T.coerceCtx Psi), (compilePsi' Psi))
    let rec installClause
      ((fromCS)(* installClause fromCS (a, A) = ()
     Effect: compiles and installs compiled form of A according to
             the specified compilation strategy
  *))
      (a, A) =
      match !C.optimize with
      | C.No ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
      | C.LinearHeads ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
      | C.Indexing ->
          let ((g, Head), R) =
            compileSClauseN fromCS
              (I.Null, I.Null, (Whnf.normalize (A, I.id))) in
          let _ =
            C.sProgInstall
              (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A)))) in
          (match Head with
           | NONE -> raise (Error "Install via normal index")
           | SOME (H, Eqs) ->
               SubTree.sProgInstall
                 ((cidFromHead (I.targetHead A)), (C.Head (H, g, Eqs, a)), R))
    let rec compileConDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((fromCS)(* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
         (* Defined constants are currently not compiled *)),
         (a, ConDec (_, _, _, _, A, I.Type))) -> installClause fromCS (a, A)
      | (fromCS, (a, SkoDec (_, _, _, A, I.Type))) ->
          (match !C.optimize with
           | C.No ->
               C.sProgInstall
                 (((a)
                   (* we don't use substitution tree indexing for skolem constants yet -bp*)),
                   (C.SClause (compileDClauseN fromCS true__ (I.Null, A))))
           | _ ->
               C.sProgInstall
                 (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, A)))))
      | (I.Clause, (a, ConDef (_, _, _, _, A, I.Type, _))) ->
          C.sProgInstall
            (a,
              (C.SClause
                 (compileDClauseN I.Clause true__
                    (I.Null, (Whnf.normalize (A, I.id))))))
      | (_, _) -> ()
    let rec install fromCS cid =
      compileConDec fromCS (cid, (I.sgnLookup cid))
    let rec sProgReset () = SubTree.sProgReset (); C.sProgReset ()
  end ;;




module CPrint =
  (Make_CPrint)(struct
                  module Print =
                    ((Print)(* Now in compsyn.fun *)
                    (*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !*)
                    (*! structure IntSyn' = IntSyn !*)
                    (*! structure CompSyn' = CompSyn !*))
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
                   module Whnf =
                     ((Whnf)(*! structure IntSyn' = IntSyn !*)(*! structure CompSyn' = CompSyn !*))
                   module TypeCheck = TypeCheck
                   module SubTree = SubTree
                   module CPrint = CPrint
                   module Print = Print
                   module Names = Names
                 end)
module Assign =
  (Make_Assign)(struct
                  module Whnf =
                    ((Whnf)(*! structure IntSyn' = IntSyn !*))
                  module Unify = UnifyTrail
                  module Print = Print
                end);;
