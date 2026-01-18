
(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)
module type TABLED  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    val solve :
      ((CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg *
        (CompSyn.pskeleton -> unit)) -> unit
    val updateGlobalTable : (CompSyn.__Goal * bool) -> unit
    val keepTable : IntSyn.cid -> bool
    val fillTable : unit -> unit
    val nextStage : unit -> bool
    val reset : unit -> unit
    val tableSize : unit -> int
    val suspGoalNo : unit -> int
  end;;




(* Abstract Machine for tabling*)
(* Author: Brigitte Pientka *)
(* Based on abstract machine in absmachine.fun *)
module Tabled(Tabled:sig
                       (*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       module Unify : UNIFY
                       module TabledSyn : TABLEDSYN
                       module Assign : ASSIGN
                       module Index : INDEX
                       module Queue : QUEUE
                       module AbstractTabled : ABSTRACTTABLED
                       module MemoTable : MEMOTABLE
                       module CPrint : CPRINT
                       (*! sharing Unify.IntSyn = IntSyn' !*)
                       (*!  sharing TabledSyn.IntSyn = IntSyn' !*)
                       (*!  sharing Assign.IntSyn = IntSyn' !*)
                       (*!  sharing Index.IntSyn = IntSyn' !*)
                       (*! structure TableParam : TABLEPARAM !*)
                       (*!  sharing TableParam.IntSyn = IntSyn' !*)
                       (*!  sharing TableParam.CompSyn = CompSyn' !*)
                       (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
                       (*! sharing AbstractTabled.TableParam = TableParam !*)
                       (*!  sharing MemoTable.IntSyn = IntSyn' !*)
                       (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
                       (*! sharing MemoTable.TableParam = TableParam  !*)
                       (* CPrint currently unused *)
                       (*!  sharing CPrint.IntSyn = IntSyn' !*)
                       (*!  sharing CPrint.CompSyn = CompSyn' !*)
                       (* CPrint currently unused *)
                       module Print : PRINT
                     end) : TABLED =
  struct
    (*!  sharing Print.IntSyn = IntSyn' !*)
    (*              structure Names : NAMES *)
    (*!  sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*!  sharing CSManager.IntSyn = IntSyn'!*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    module Unify = Unify
    module TabledSyn = TabledSyn
    (*! structure TableParam = TableParam !*)
    (*  structure Match = Match*)
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    module T = TableParam
    module MT = MemoTable
    (* ---------------------------------------------------------------------- *)
    (* Suspended goal: SuspType, s, G, sc, ftrail, answerRef, i

       where
       s is a substitution for the existential variables in D such that G |- s : G, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)
    type __SuspType =
      | Loop 
      | Divergence of ((IntSyn.__Exp * IntSyn.__Sub) * CompSyn.__DProg) 
    let ((SuspGoals) :
      (__SuspType * (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub) *
        (CompSyn.pskeleton -> unit) * Unify.unifTrail * ((IntSyn.__Sub *
        IntSyn.__Sub) * T.answer) * int ref) list ref)
      = ref []
    exception Error of string 
    (* ---------------------------------------------------------------------- *)
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec append =
      function
      | (IntSyn.Null, G) -> G
      | (Decl (G', D), G) -> IntSyn.Decl ((append (G', G)), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shift (G, s))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (G, D), V) -> raiseType (G, (I.Lam (D, V)))
    let rec compose =
      function
      | (IntSyn.Null, G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose (G, G')), D)
    (* ---------------------------------------------------------------------- *)
    (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
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

    *)
    let rec ctxToEVarSub =
      function
      | (I.Null, s) -> s
      | (Decl (G, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (ctxToEVarSub (G, s)))
    let rec ctxToAVarSub =
      function
      | (I.Null, s) -> s
      | (Decl (G, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (ctxToAVarSub (G, s)))
      | (Decl (G, ADec (_, d)), s) ->
          let X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (X, (I.Shift (~ d))))), (ctxToAVarSub (G, s)))
    (* ---------------------------------------------------------------------- *)
    (* Solving  variable definitions *)
    (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
    let rec solveEqn =
      function
      | ((T.Trivial, s), G) -> true__
      | ((Unify (G', e1, N, eqns), s), G) ->
          let G'' = append (G', G) in
          let s' = shift (G'', s) in
          (((Assign.unifiable (G'', (N, s'), (e1, s'))) &&
              (solveEqn ((eqns, s), G)))
            (* G, G' |- s' : D, G, G' *))(* . |- s : D *)
      (* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)
    let rec unifySub' (G, s1, s2) =
      try Unify.unifySub (G, s1, s2); true__ with | Unify msg -> false__
    let rec unify (G, Us, Us') =
      try Unify.unify (G, Us, Us'); true__ with | Unify msg -> false__
    let rec getHypGoal =
      function
      | (DProg, (Atom p, s)) -> (DProg, (p, s))
      | (DProg (G, dPool), (Impl (r, A, Ha, g), s)) ->
          let D' = IntSyn.Dec (NONE, (I.EClo (A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((G, (I.EClo (A, s))), G) with
             | SOME _ ->
                 let Atom p = g in
                 let X = I.newEVar (G, (I.EClo (A, s))) in
                 ((getHypGoal
                     ((C.DProg (G, dPool)), (g, (I.Dot ((I.Exp X), s)))))
                   (* is g always atomic? *))
             | NONE ->
                 getHypGoal
                   ((C.DProg
                       ((I.Decl (G, D')),
                         (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (g, (I.dot1 s))))
          else
            getHypGoal
              ((C.DProg
                  ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                (g, (I.dot1 s)))
      | (DProg (G, dPool), (All (D, g), s)) ->
          let D' = I.decSub (D, s) in
          getHypGoal
            ((C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              (g, (I.dot1 s)))
    let rec updateGlobalTable (goal, flag) =
      let ((DProg (G, dPool) as dProg), (p, s)) =
        getHypGoal ((C.DProg (I.Null, I.Null)), (goal, I.id)) in
      let (G', DAVars, DEVars, U', eqn', s') =
        A.abstractEVarCtx (dProg, p, s) in
      let _ =
        if solveEqn ((eqn', s'), G')
        then ()
        else print "\nresidual equation not solvable!\n" in
      let status =
        if flag then TableParam.Complete else TableParam.Incomplete in
      if TabledSyn.keepTable (IntSyn.targetFam U')
      then
        match MT.callCheck (DAVars, DEVars, G', U', eqn', status) with
        | RepeatedEntry (_, answRef, _) ->
            TableParam.globalTable :=
              ((DAVars, DEVars, G', U', eqn', answRef, status) ::
                 (!TableParam.globalTable))
        | _ -> raise (Error "Top level goal should always in the table\n")
      else ()
    let rec keepTable c = TabledSyn.keepTable c
    let rec fillTable () =
      let rec insert =
        function
        | nil -> ()
        | (DAVars, DEVars, G', U', eqn', answRef, status)::T ->
            (match MT.insertIntoTree
                     (DAVars, DEVars, G', U', eqn', answRef, status)
             with
             | NewEntry _ -> insert T
             | _ -> ()) in
      insert (!TableParam.globalTable)
    (*------------------------------------------------------------------------------------------*)
    (* retrieve' ((G, U, s), asub, AnswerList, sc) = ()

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
       .  |- esub : D      and  G |- esub^|G| : D , G
       .  |- s : D         and  G |- s^|G| : D, G
     then
       unify (G, esub^|G|, s^|G|) and unify (G, ([esub]asub)^|G|, scomp^|G|)
       if unification succeeds
         then we continue solving the success continuation.
         otherwise we fail

     Effects: instantiation of EVars in s, s1' and esub
     any effect  sc O1  might have

   *)
    let rec retrieve' =
      function
      | ((G, U, s), asub, [], sc) -> ()
      | ((G, U, s), (esub, asub), ((D', s1), O1)::A, sc) ->
          let s1' =
            ctxToEVarSub (((D', (I.Shift (I.ctxLength D'))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (G, s) in
          let ss1 = shift (G, scomp) in
          let a = I.comp (asub, s) in
          let ass = shift (G, a) in
          let easub = I.comp (asub, esub) in
          (((CSManager.trail
               (function
                | () ->
                    ((if
                        (unifySub' (G, (shift (G, esub)), ss)) &&
                          (unifySub'
                             (G, (shift (G, (I.comp (asub, esub)))), ss1))
                      then sc O1
                      else ())
                    (* Succeed *)));
             retrieve' ((G, U, s), (esub, asub), A, sc)))
            (* Fail *))
    (* currently not used -- however, it may be better to not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
    (* retrieveV ((G, U, s), answerList, sc)
      if
        . |- [s]Pi G.U
        . |- s : DAVars, DEVars

        ((DEVars_i, s_i), O_i) is an element in answer list
         DEVars_i |- s_i : DAVars, DEVars
         and O_i is a proof skeleton
      then
        sc O_i is evaluated
        Effects: instantiation of EVars in s

   *)
    let rec retrieveV =
      function
      | ((G, U, s), [], sc) -> ()
      | ((G, U, s), ((DEVars, s1), O1)::A, sc) ->
          let s1' =
            ctxToEVarSub (((DEVars, (I.Shift (I.ctxLength DEVars))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (G, s) in
          let ss1 = shift (G, scomp) in
          (((CSManager.trail
               (function | () -> if unifySub' (G, ss, ss1) then sc O1 else ());
             retrieveV ((G, U, s), A, sc)))
            (* for subsumption we must combine it with asumb!!! *))
    let rec retrieveSW ((G, U, s), asub, AnswL, sc) =
      retrieve' ((G, U, s), asub, AnswL, sc)
    (* currently not used -- however, it may be better to  not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
    (* fun retrieveSW ((G, U, s), asub, AnswL, sc) =
     case (!TableParam.strategy) of
       TableParam.Variant =>  retrieveV ((G, U, s), AnswL, sc)
     | TableParam.Subsumption => retrieve' ((G, U, s), asub, AnswL, sc) *)
    (* retrieve (k, (G, s), (asub, answRef), sc) = ()
      Invariants:
      If
         G |-   s : G, D   where s contains free existential variables defined in D
         answRef is a pointer to the AnswerList

        G |- asub : D, G  asub is the identity in the variant case
        G |- asub : D, G  asub instantiates existential variables in s.

     then the success continuation sc is triggered.

     Effects: instantiation of EVars in s, and asub
   *)
    let rec retrieve (k, (G, U, s), (asub, answRef), sc) =
      let lkp = T.lookup answRef in
      let asw' = List.take ((rev (T.solutions answRef)), (T.lookup answRef)) in
      let answ' = List.drop (asw', (!k)) in
      k := lkp; retrieveSW ((G, U, s), asub, answ', sc)
    (* ---------------------------------------------------------------------- *)
    (* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- g  goal
     if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)
    let rec solve =
      function
      | ((Atom p, s), (DProg (G, dPool) as dp), sc) ->
          if TabledSyn.tabledLookup (I.targetFam p)
          then
            let (G', DAVars, DEVars, U', eqn', s') =
              A.abstractEVarCtx (dp, p, s) in
            let _ =
              if solveEqn ((eqn', s'), G')
              then ()
              else
                print
                  "\nresidual equation not solvable! -- This should never happen! \n" in
            (((match MT.callCheck
                       (DAVars, DEVars, G', U', eqn', T.Incomplete)
               with
               | NewEntry answRef ->
                   matchAtom
                     ((p, s), dp,
                       (function
                        | pskeleton ->
                            (match MT.answerCheck (s', answRef, pskeleton)
                             with
                             | T.repeated -> ()
                             | T.new__ -> sc pskeleton)))
               | RepeatedEntry (asub, answRef, T.Incomplete) ->
                   ((if T.noAnswers answRef
                     then
                       (SuspGoals :=
                          ((Loop, (G', U', s'), sc, (Unify.suspend ()),
                             (asub, answRef), (ref 0)) :: (!SuspGoals));
                        ())
                     else
                       (let le = T.lookup answRef in
                        SuspGoals :=
                          ((Loop, (G', U', s'), sc, (Unify.suspend ()),
                             (asub, answRef), (ref le)) :: (!SuspGoals));
                        retrieve ((ref 0), (G', U', s'), (asub, answRef), sc)))
                   (* loop detected
                  * NOTE: we might suspend goals more than once.
                  *     example: answer list for goal (p,s) is saturated
                  *              but not the whole table is saturated.
                  *)
                   (* loop detected
                  * new answers available from previous stages
                  * resolve current goal with all possible answers
                  *))
               | RepeatedEntry (asub, answRef, T.Complete) ->
                   ((if T.noAnswers answRef
                     then ()
                     else
                       retrieve ((ref 0), (G', U', s'), (asub, answRef), sc))
                   (* Subgoal is not provable *)(* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *))
               | DivergingEntry (asub, answRef) ->
                   (SuspGoals :=
                      (((Divergence ((p, s), dp)), (G', U', s'), sc,
                         (Unify.suspend ()),
                         ((((I.id, asub))
                           (* this is a hack *)), answRef),
                         (ref 0)) :: (!SuspGoals));
                    ())))
              (* Side effect: D', G' |- U' added to table *)
              (* loop detected  -- currently not functioning correctly.
                    we might be using this as part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
              (* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *))
          else matchAtom ((p, s), dp, sc)
      | ((Impl (r, A, Ha, g), s), DProg (G, dPool), sc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((G, (I.EClo (A, s))), G) with
             | SOME _ ->
                 let X = I.newEVar (G, (I.EClo (A, s))) in
                 solve
                   ((g, (I.Dot ((I.Exp X), s))), (C.DProg (G, dPool)),
                     (function | O -> sc O))
             | NONE ->
                 solve
                   ((g, (I.dot1 s)),
                     (C.DProg
                        ((I.Decl (G, D')),
                          (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (function | O -> sc O)))
          else
            solve
              ((g, (I.dot1 s)),
                (C.DProg
                   ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                (function | O -> sc O))
      | ((All (D, g), s), DProg (G, dPool), sc) ->
          let D' = I.decSub (D, s) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              (function | O -> sc O))
    let rec rSolve =
      function
      | (ps', (Eq (Q), s), DProg (G, dPool), sc) ->
          ((if Unify.unifiable (G, ps', (Q, s)) then sc [] else ())
          (* effect: instantiate EVars *)(* call success continuation *))
      | (ps', (Assign (Q, eqns), s), (DProg (G, dPool) as dp), sc) ->
          (match Assign.assignable (G, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | S -> sc S))
           | NONE -> ())
      | (ps', (And (r, A, g), s), (DProg (G, dPool) as dp), sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp X), s))), dp,
                (function
                 | S1 -> solve ((g, s), dp, (function | S2 -> sc (S1 @ S2))))))
            (* is this EVar redundant? -fp *))
      | (ps', (Exists (Dec (_, A), r), s), (DProg (G, dPool) as dp), sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp, (function | S -> sc S))
      | (ps', (Axists (ADec (SOME (X), d), r), s), (DProg (G, dPool) as dp),
         sc) ->
          let X' = I.newAVar () in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc [] else ()
      | ((UnifyEq (G', e1, N, eqns), s), (DProg (G, dPool) as dp), cnstr, sc)
          ->
          let G'' = append (G', G) in
          let s' = shift (G', s) in
          if Assign.unifiable (G'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom
      (((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc) =
      let rec matchSig =
        function
        | nil -> ()
        | (Const c as Hc)::sgn' ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            (((CSManager.trail
                 (function
                  | () ->
                      rSolve
                        (ps', (r, I.id), dp,
                          (function | S -> sc ((C.Pc c) :: S))));
               matchSig sgn'))
              (* trail to undo EVar instantiations *))
        (* return indicates failure *) in
      let rec matchDProg =
        function
        | (I.Null, I.Null, _) -> matchSig (Index.lookup (cidFromHead Ha))
        | (Decl (G, _), Decl (dPool', Dec (r, s, Ha')), k) ->
            ((if eqHead (Ha, Ha')
              then
                (CSManager.trail
                   (function
                    | () ->
                        rSolve
                          (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                            (function | S -> sc ((C.Dc k) :: S))));
                 matchDProg (G, dPool', (k + 1)))
              else matchDProg (G, dPool', (k + 1)))
            (* trail to undo EVar instantiations *))
        | (Decl (G, _), Decl (dPool', C.Parameter), k) ->
            matchDProg (G, dPool', (k + 1))(* dynamic program exhausted, try signature *) in
      let rec matchConstraint (solve, try__) =
        let succeeded =
          CSManager.trail
            (function
             | () ->
                 (match solve (G, (I.SClo (S, s)), try__) with
                  | SOME (U) -> (sc [C.Csolver U]; true__)
                  | NONE -> false__)) in
        if succeeded then matchConstraint (solve, (try__ + 1)) else () in
      ((match I.constStatus (cidFromHead Ha) with
        | Constraint (cs, solve) -> matchConstraint (solve, 0)
        | _ -> matchDProg (G, dPool, 1))
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    (* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed
               by the current goal

     if answers are available
      then retrieve all new answers
     else fail
     *)
    let rec retrieval =
      function
      | (Loop, (G', U', s'), sc, (asub, answRef), n) ->
          ((if T.noAnswers answRef
            then ()
            else retrieve (n, (G', U', s'), (asub, answRef), sc))
          (* still  no answers available from previous stages *)
          (* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
          (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *))
      | (Divergence ((p, s), dp), (G', U', s'), sc, (asub, answRef), n) ->
          matchAtom
            ((p, s), dp,
              (function
               | pskeleton ->
                   (match MT.answerCheck (s', answRef, pskeleton) with
                    | T.repeated -> ()
                    | T.new__ -> sc pskeleton)))
    let rec tableSize () = MT.tableSize ()
    let rec suspGoalNo () = List.length (!SuspGoals)
    (*  nextStage () = bool
     Side effect: advances lookup pointers
   *)
    let rec nextStage () =
      let rec resume =
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
      ((if MT.updateTable ()
        then
          ((TableParam.stageCtr := (!TableParam.stageCtr)) + 1;
           resume SG;
           true__)
        else false__)
        (* table changed during previous stage *)(* table did not change during previous stage *))
    let rec reset () = SuspGoals := []; MT.reset (); TableParam.stageCtr := 0
    let rec solveQuery ((g, s), (DProg (G, dPool) as dp), sc) =
      solve ((g, s), dp, sc)(* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)
    (* rsolve ((p,s'), (r,s), dp, sc) = ()
    Invariants:
    dp = (G, dPool) where G ~ dPool
    G |- s : G'
    G' |- r  resgoal
    G |- s' : G''
    G'' |- p : H @ S' (mod whnf)
    if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
     any effect  sc S  might have
     *)
    (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
    (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
    (* local ... *)
    let solve = solveQuery
  end ;;
