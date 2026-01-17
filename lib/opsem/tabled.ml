
module type TABLED  =
  sig
    val solve :
      ((CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg *
        (CompSyn.pskeleton -> unit)) ->
        ((unit)(*! structure CompSyn : COMPSYN !*)(*! structure IntSyn : INTSYN !*)
        (* Author: Brigitte Pientka     *)(* Tabled Abstract Machine      *))
    val updateGlobalTable : (CompSyn.__Goal * bool) -> unit
    val keepTable : IntSyn.cid -> bool
    val fillTable : unit -> unit
    val nextStage : unit -> bool
    val reset : unit -> unit
    val tableSize : unit -> int
    val suspGoalNo : unit -> int
  end;;




module Tabled(Tabled:sig
                       module Unify : UNIFY
                       module TabledSyn : TABLEDSYN
                       module Assign : ASSIGN
                       module Index : INDEX
                       module Queue : QUEUE
                       module AbstractTabled : ABSTRACTTABLED
                       module MemoTable : MEMOTABLE
                       module CPrint : CPRINT
                       module Print :
                       ((PRINT)(* Abstract Machine for tabling*)
                       (* Author: Brigitte Pientka *)
                       (* Based on abstract machine in absmachine.fun *)
                       (*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       (*! sharing Unify.IntSyn = IntSyn' !*)(*!  sharing TabledSyn.IntSyn = IntSyn' !*)
                       (*!  sharing Assign.IntSyn = IntSyn' !*)(*!  sharing Index.IntSyn = IntSyn' !*)
                       (*! structure TableParam : TABLEPARAM !*)
                       (*!  sharing TableParam.IntSyn = IntSyn' !*)
                       (*!  sharing TableParam.CompSyn = CompSyn' !*)
                       (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
                       (*! sharing AbstractTabled.TableParam = TableParam !*)
                       (*!  sharing MemoTable.IntSyn = IntSyn' !*)
                       (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
                       (*! sharing MemoTable.TableParam = TableParam  !*)
                       (* CPrint currently unused *)
                       (*!  sharing CPrint.IntSyn = IntSyn' !*)(*!  sharing CPrint.CompSyn = CompSyn' !*)
                       (* CPrint currently unused *))
                     end) : TABLED =
  struct
    module Unify =
      ((Unify)(*!  sharing Print.IntSyn = IntSyn' !*)
      (*              structure Names : NAMES *)(*!  sharing Names.IntSyn = IntSyn' !*)
      (*! structure CSManager : CS_MANAGER !*)(*!  sharing CSManager.IntSyn = IntSyn'!*)
      (*! structure IntSyn = IntSyn' !*)(*! structure CompSyn = CompSyn' !*))
    module TabledSyn = TabledSyn
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    module T = TableParam
    module MT = MemoTable
    type __SuspType =
      | Loop 
      | Divergence of
      ((((IntSyn.__Exp)(* Suspended goal: SuspType, s, g, sc, ftrail, answerRef, i

       where
       s is a substitution for the existential variables in D such that g |- s : g, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)
      (* ---------------------------------------------------------------------- *)
      (*  structure Match = Match*)(*! structure TableParam = TableParam !*))
      * IntSyn.__Sub) * CompSyn.__DProg) 
    let ((SuspGoals) :
      (__SuspType * (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub) *
        (CompSyn.pskeleton -> unit) * Unify.unifTrail * ((IntSyn.__Sub *
        IntSyn.__Sub) * T.answer) * int ref) list ref)
      = ref []
    exception Error of string 
    let rec cidFromHead =
      function
      | Const
          ((a)(* ---------------------------------------------------------------------- *))
          -> a
      | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec append =
      function
      | (IntSyn.Null, g) -> g
      | (Decl (g', D), g) -> IntSyn.Decl ((append (g', g)), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (g, D), s) -> I.dot1 (shift (g, s))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Lam (D, V)))
    let rec compose =
      function
      | (IntSyn.Null, g) -> g
      | (Decl (g, D), g') -> IntSyn.Decl ((compose (g, g')), D)
    let rec ctxToEVarSub =
      function
      | (((I.Null)(* ---------------------------------------------------------------------- *)
         (* We write
       g |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       g |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
    *)
         (* ---------------------------------------------------------------------- *)
         (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)),
         s) -> s
      | (Decl (g, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (ctxToEVarSub (g, s)))
    let rec ctxToAVarSub =
      function
      | (I.Null, s) -> s
      | (Decl (g, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (ctxToAVarSub (g, s)))
      | (Decl (g, ADec (_, d)), s) ->
          let X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (X, (I.Shift (~ d))))), (ctxToAVarSub (g, s)))
    let rec solveEqn =
      function
      | ((((T.Trivial)(* ---------------------------------------------------------------------- *)
          (* Solving  variable definitions *)(* solveEqn ((VarDef, s), g) = bool

    if g'' |- VarDef and g  . |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)),
          s),
         g) -> true__
      | ((Unify (g', e1, N, eqns), s), g) ->
          let ((g'')(* D, g, g' |- e1 and D, g, g' |- N and D, g |- eqns *)
            (* . |- s : D *)) = append (g', g) in
          let s' = shift (g'', s) in
          (Assign.unifiable (g'', (N, s'), (e1, s'))) &&
            (solveEqn
               ((((eqns)(* g, g' |- s' : D, g, g' *)), s),
                 g))
    let rec unifySub' (g, s1, s2) =
      try Unify.unifySub (g, s1, s2); true__ with | Unify msg -> false__
    let rec unify (g, Us, Us') =
      try Unify.unify (g, Us, Us'); true__ with | Unify msg -> false__
    let rec getHypGoal =
      function
      | (DProg, (Atom p, s)) -> (DProg, (p, s))
      | (DProg (g, dPool), (Impl (r, A, Ha, g), s)) ->
          let D' = IntSyn.Dec (NONE, (I.EClo (A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((g, (I.EClo (A, s))), g) with
             | SOME _ ->
                 let Atom p = g in
                 let X = I.newEVar (g, (I.EClo (A, s))) in
                 getHypGoal
                   ((C.DProg (g, dPool)), (g, (I.Dot ((I.Exp X), s))))
             | NONE ->
                 getHypGoal
                   ((C.DProg
                       ((I.Decl (g, D')),
                         (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (g, (I.dot1 s))))
          else
            getHypGoal
              ((C.DProg
                  ((I.Decl
                      (((g)(* is g always atomic? *)), D')),
                    (I.Decl (dPool, (C.Dec (r, s, Ha)))))), (g, (I.dot1 s)))
      | (DProg (g, dPool), (All (D, g), s)) ->
          let D' = I.decSub (D, s) in
          getHypGoal
            ((C.DProg ((I.Decl (g, D')), (I.Decl (dPool, C.Parameter)))),
              (g, (I.dot1 s)))
    let rec updateGlobalTable (goal, flag) =
      let ((DProg (g, dPool) as dProg), (p, s)) =
        getHypGoal ((C.DProg (I.Null, I.Null)), (goal, I.id)) in
      let (g', DAVars, DEVars, U', eqn', s') =
        A.abstractEVarCtx (dProg, p, s) in
      let _ =
        if solveEqn ((eqn', s'), g')
        then ()
        else print "\nresidual equation not solvable!\n" in
      let status =
        if flag then TableParam.Complete else TableParam.Incomplete in
      if TabledSyn.keepTable (IntSyn.targetFam U')
      then
        match MT.callCheck (DAVars, DEVars, g', U', eqn', status) with
        | RepeatedEntry (_, answRef, _) ->
            TableParam.globalTable :=
              ((DAVars, DEVars, g', U', eqn', answRef, status) ::
                 (!TableParam.globalTable))
        | _ -> raise (Error "Top level goal should always in the table\n")
      else ()
    let rec keepTable c = TabledSyn.keepTable c
    let rec fillTable () =
      let insert =
        function
        | nil -> ()
        | (DAVars, DEVars, g', U', eqn', answRef, status)::T ->
            (match MT.insertIntoTree
                     (DAVars, DEVars, g', U', eqn', answRef, status)
             with
             | NewEntry _ -> insert T
             | _ -> ()) in
      insert (!TableParam.globalTable)
    let rec retrieve' =
      function
      | ((((g)(*------------------------------------------------------------------------------------------*)
          (* retrieve' ((g, U, s), asub, AnswerList, sc) = ()

     retrieval for subsumption must take into account the asub substitution

     Invariants:
     if
       Goal:                        Answer substitution from index:
       D   |- Pi G. U
       .   |- s : D        and      D' |- s1 : D1
       D   |- asub : D1    and      .  |- s1' : D' (reinstantiate evars)

                                scomp = s1 o s1'
                                  .  |- scomp : D1

       .  |- [esub]asub : D1  where
       .  |- esub : D      and  g |- esub^|g| : D , g
       .  |- s : D         and  g |- s^|g| : D, g
     then
       unify (g, esub^|g|, s^|g|) and unify (g, ([esub]asub)^|g|, scomp^|g|)
       if unification succeeds
         then we continue solving the success continuation.
         otherwise we fail

     Effects: instantiation of EVars in s, s1' and esub
     any effect  sc O1  might have

   *)),
          U, s),
         asub, [], sc) -> ()
      | ((g, U, s), (esub, asub), ((D', s1), O1)::A, sc) ->
          let s1' =
            ctxToEVarSub (((D', (I.Shift (I.ctxLength D'))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (g, s) in
          let ss1 = shift (g, scomp) in
          let a = I.comp (asub, s) in
          let ass = shift (g, a) in
          let easub = I.comp (asub, esub) in
          (CSManager.trail
             (function
              | () ->
                  if
                    (unifySub' (g, (shift (g, esub)), ss)) &&
                      (unifySub' (g, (shift (g, (I.comp (asub, esub)))), ss1))
                  then sc O1
                  else ());
           retrieve'
             ((((g)
                (* Succeed *)(* Fail *)),
                U, s), (esub, asub), A, sc))
    let rec retrieveV =
      function
      | ((((g)(* currently not used -- however, it may be better to not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
          (* retrieveV ((g, U, s), answerList, sc)
      if
        . |- [s]Pi G.U
        . |- s : DAVars, DEVars

        ((DEVars_i, s_i), O_i) is an element in answer list
         DEVars_i |- s_i : DAVars, DEVars
         and O_i is a proof skeleton
      then
        sc O_i is evaluated
        Effects: instantiation of EVars in s

   *)),
          U, s),
         [], sc) -> ()
      | ((g, U, s), ((DEVars, s1), O1)::A, sc) ->
          let s1' =
            ctxToEVarSub (((DEVars, (I.Shift (I.ctxLength DEVars))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (g, s) in
          let ss1 = shift (g, scomp) in
          (CSManager.trail
             (function | () -> if unifySub' (g, ss, ss1) then sc O1 else ());
           retrieveV
             ((((g)
                (* for subsumption we must combine it with asumb!!! *)),
                U, s), A, sc))
    let rec retrieveSW ((g, U, s), asub, AnswL, sc) =
      retrieve' ((g, U, s), asub, AnswL, sc)
    let rec retrieve
      (((k)(* currently not used -- however, it may be better to  not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
       (* fun retrieveSW ((g, U, s), asub, AnswL, sc) =
     case (!TableParam.strategy) of
       TableParam.Variant =>  retrieveV ((g, U, s), AnswL, sc)
     | TableParam.Subsumption => retrieve' ((g, U, s), asub, AnswL, sc) *)
       (* retrieve (k, (g, s), (asub, answRef), sc) = ()
      Invariants:
      If
         g |-   s : g, D   where s contains free existential variables defined in D
         answRef is a pointer to the AnswerList

        g |- asub : D, g  asub is the identity in the variant case
        g |- asub : D, g  asub instantiates existential variables in s.

     then the success continuation sc is triggered.

     Effects: instantiation of EVars in s, and asub
   *)),
       (g, U, s), (asub, answRef), sc)
      =
      let lkp = T.lookup answRef in
      let asw' = List.take ((rev (T.solutions answRef)), (T.lookup answRef)) in
      let answ' = List.drop (asw', (!k)) in
      k := lkp; retrieveSW ((g, U, s), asub, answ', sc)
    let rec solve =
      function
      | ((Atom
          ((p)(* ---------------------------------------------------------------------- *)
          (* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (g, dPool) where  g ~ dPool  (context g matches dPool)
     g |- s : g'
     g' |- g  goal
     if  g |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)),
          s),
         (DProg (g, dPool) as dp), sc) ->
          if TabledSyn.tabledLookup (I.targetFam p)
          then
            let (g', DAVars, DEVars, U', eqn', s') =
              A.abstractEVarCtx (dp, p, s) in
            let _ =
              if solveEqn ((eqn', s'), g')
              then ()
              else
                print
                  "\nresidual equation not solvable! -- This should never happen! \n" in
            (match MT.callCheck (DAVars, DEVars, g', U', eqn', T.Incomplete)
             with
             | NewEntry answRef ->
                 matchAtom
                   ((p, s), dp,
                     (function
                      | pskeleton ->
                          (match MT.answerCheck (s', answRef, pskeleton) with
                           | T.repeated -> ()
                           | T.new__ -> sc pskeleton)))
             | RepeatedEntry (asub, answRef, T.Incomplete) ->
                 if T.noAnswers answRef
                 then
                   (SuspGoals :=
                      ((Loop, (g', U', s'), sc, (Unify.suspend ()),
                         (asub, answRef), (ref 0)) :: (!SuspGoals));
                    ())
                 else
                   (let le = T.lookup answRef in
                    SuspGoals :=
                      ((Loop, (g', U', s'), sc, (Unify.suspend ()),
                         (asub, answRef), (ref le)) :: (!SuspGoals));
                    retrieve ((ref 0), (g', U', s'), (asub, answRef), sc))
             | RepeatedEntry (asub, answRef, T.Complete) ->
                 if T.noAnswers answRef
                 then ()
                 else retrieve ((ref 0), (g', U', s'), (asub, answRef), sc)
             | DivergingEntry (asub, answRef) ->
                 (SuspGoals :=
                    (((Divergence ((p, s), dp)), (g', U', s'), sc,
                       (Unify.suspend ()), ((I.id, asub), answRef), (
                       ref 0)) :: (!SuspGoals));
                  ()))
          else
            matchAtom
              ((((p)
                 (* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi g'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |g'|
              g' |- s'^k : DAVars, DEVars, g'
               . |- [s'](Pi g'. U')     and  g |- [s'^k]U' = [s]p *)
                 (* Side effect: D', g' |- U' added to table *)(* loop detected
                  * NOTE: we might suspend goals more than once.
                  *     example: answer list for goal (p,s) is saturated
                  *              but not the whole table is saturated.
                  *)
                 (* loop detected
                  * new answers available from previous stages
                  * resolve current goal with all possible answers
                  *)
                 (* Subgoal is not provable *)(* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *)
                 (* loop detected  -- currently not functioning correctly.
                    we might be using this as part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
                 (* this is a hack *)), s), dp, sc)
      | ((Impl (r, A, Ha, g), s), DProg (g, dPool), sc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((g, (I.EClo (A, s))), g) with
             | SOME _ ->
                 let X = I.newEVar (g, (I.EClo (A, s))) in
                 solve
                   ((g, (I.Dot ((I.Exp X), s))), (C.DProg (g, dPool)),
                     (function | O -> sc O))
             | NONE ->
                 solve
                   ((g, (I.dot1 s)),
                     (C.DProg
                        ((I.Decl (g, D')),
                          (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (function | O -> sc O)))
          else
            solve
              ((g, (I.dot1 s)),
                (C.DProg
                   ((I.Decl (g, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                (function | O -> sc O))
      | ((All (D, g), s), DProg (g, dPool), sc) ->
          let D' = I.decSub (D, s) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (g, D')), (I.Decl (dPool, C.Parameter)))),
              (function | O -> sc O))
    let rec rSolve =
      function
      | (((ps')(* rsolve ((p,s'), (r,s), dp, sc) = ()
    Invariants:
    dp = (g, dPool) where g ~ dPool
    g |- s : g'
    g' |- r  resgoal
    g |- s' : g''
    g'' |- p : H @ S' (mod whnf)
    if g |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
     any effect  sc S  might have
     *)),
         (Eq (Q), s), DProg (g, dPool), sc) ->
          if Unify.unifiable (g, ps', (Q, s))
          then sc []
          else ((())
            (* effect: instantiate EVars *)(* call success continuation *))
      | (((ps')(* fail *)), (Assign (Q, eqns), s),
         (DProg (g, dPool) as dp), sc) ->
          (match Assign.assignable (g, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | S -> sc S))
           | NONE -> ())
      | (ps', (And (r, A, g), s), (DProg (g, dPool) as dp), sc) ->
          let ((X)(* is this EVar redundant? -fp *)) =
            I.newEVar (g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function
               | s1 -> solve ((g, s), dp, (function | s2 -> sc (s1 @ s2)))))
      | (ps', (Exists (Dec (_, A), r), s), (DProg (g, dPool) as dp), sc) ->
          let X = I.newEVar (g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp, (function | S -> sc S))
      | (ps', (Axists (ADec (SOME (X), d), r), s), (DProg (g, dPool) as dp),
         sc) ->
          let X' = I.newAVar () in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
    let rec aSolve =
      function
      | ((((C.Trivial)(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (g, dPool) where g ~ dPool
       g |- s : g'
       if g |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)),
          s),
         dp, cnstr, sc) -> if Assign.solveCnstr cnstr then sc [] else ()
      | ((UnifyEq (g', e1, N, eqns), s), (DProg (g, dPool) as dp), cnstr, sc)
          ->
          let g'' = append (g', g) in
          let s' = shift (g', s) in
          if Assign.unifiable (g'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom
      (((Root
         (((Ha)(* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (g, dPool) where g ~ dPool
       g |- s : g'
       g' |- p : type, p = H @ S mod whnf
       if g |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)),
          S),
         s) as ps'),
       (DProg (g, dPool) as dp), sc)
      =
      let matchSig =
        function
        | ((nil)(* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *))
            -> ()
        | (Const ((c)(* return indicates failure *)) as Hc)::sgn'
            ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            (CSManager.trail
               (function
                | () ->
                    rSolve
                      (ps', (r, I.id), dp,
                        (function | S -> sc ((C.Pc c) :: S))));
             matchSig ((sgn')
               (* trail to undo EVar instantiations *))) in
      let matchDProg =
        function
        | (((I.Null)(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)),
           I.Null, _) ->
            matchSig
              (Index.lookup
                 (cidFromHead ((Ha)
                    (* dynamic program exhausted, try signature *))))
        | (Decl (g, _), Decl (dPool', Dec (r, s, Ha')), k) ->
            if eqHead (Ha, Ha')
            then
              (CSManager.trail
                 (function
                  | () ->
                      rSolve
                        (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                          (function | S -> sc ((C.Dc k) :: S))));
               matchDProg (g, dPool', (k + 1)))
            else
              matchDProg
                (((g)
                  (* trail to undo EVar instantiations *)),
                  dPool', (k + 1))
        | (Decl (g, _), Decl (dPool', C.Parameter), k) ->
            matchDProg (g, dPool', (k + 1)) in
      let matchConstraint (solve, try__) =
        let succeeded =
          CSManager.trail
            (function
             | () ->
                 (match solve (g, (I.SClo (S, s)), try__) with
                  | SOME (U) -> (sc [C.Csolver U]; true__)
                  | NONE -> false__)) in
        if succeeded then matchConstraint (solve, (try__ + 1)) else () in
      match I.constStatus (cidFromHead Ha) with
      | Constraint (cs, solve) -> matchConstraint (solve, 0)
      | _ -> matchDProg (g, dPool, 1)
    let rec retrieval =
      function
      | (((Loop)(* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (g, dPool) where  g ~ dPool  (context g matches dPool)
     g |- s : g'
     g' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed
               by the current goal

     if answers are available
      then retrieve all new answers
     else fail
     *)),
         (g', U', s'), sc, (asub, answRef), n) ->
          if T.noAnswers answRef
          then ()
          else
            retrieve
              (((n)
                (* still  no answers available from previous stages *)
                (* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
                (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *)),
                (g', U', s'), (asub, answRef), sc)
      | (Divergence ((p, s), dp), (g', U', s'), sc, (asub, answRef), n) ->
          matchAtom
            ((p, s), dp,
              (function
               | pskeleton ->
                   (match MT.answerCheck (s', answRef, pskeleton) with
                    | T.repeated -> ()
                    | T.new__ -> sc pskeleton)))
    let rec tableSize () = MT.tableSize ()
    let rec suspGoalNo () = List.length (!SuspGoals)
    let rec nextStage
      ((())(*  nextStage () = bool
     Side effect: advances lookup pointers
   *))
      =
      let resume =
        function
        | [] -> ()
        | (Susp, s, sc, trail, (asub, answRef), k)::Goals ->
            (CSManager.trail
               (function
                | () ->
                    (Unify.resume trail;
                     retrieval (Susp, s, sc, (asub, answRef), k)));
             resume Goals) in
      let SG = rev (!SuspGoals) in
      if MT.updateTable ()
      then
        ((TableParam.stageCtr := (!TableParam.stageCtr)) + 1;
         resume SG;
         true__)
      else ((false__)
        (* table changed during previous stage *)(* table did not change during previous stage *))
    let rec reset () = SuspGoals := []; MT.reset (); TableParam.stageCtr := 0
    let rec solveQuery ((g, s), (DProg (g, dPool) as dp), sc) =
      solve
        ((((g)
           (* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)),
           s), dp, sc)
    let ((solve)(* local ... *)) = solveQuery
  end ;;
