
module type TABLED  =
  sig
    val solve :
      (CompSyn.__Goal * IntSyn.__Sub) ->
        CompSyn.__DProg -> (CompSyn.pskeleton -> unit) -> unit
    val updateGlobalTable : CompSyn.__Goal -> bool -> unit
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
                       module Print : PRINT
                     end) : TABLED =
  struct
    module Unify = Unify
    module TabledSyn = TabledSyn
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    module T = TableParam
    module MT = MemoTable
    type __SuspType =
      | Loop 
      | Divergence of ((IntSyn.__Exp * IntSyn.__Sub) * CompSyn.__DProg) 
    let ((SuspGoals) :
      (__SuspType * (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub) *
        (CompSyn.pskeleton -> unit) * Unify.unifTrail * ((IntSyn.__Sub *
        IntSyn.__Sub) * T.answer) * int ref) list ref)
      = ref []
    exception Error of string 
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec append __2__ __3__ =
      match (__2__, __3__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G', __D), __G) -> IntSyn.Decl ((append (__G', __G)), __D)
    let rec shift __4__ __5__ =
      match (__4__, __5__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec raiseType __6__ __7__ =
      match (__6__, __7__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) -> raiseType (__G, (I.Lam (__D, __V)))
    let rec compose __8__ __9__ =
      match (__8__, __9__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose (__G, __G')), __D)
    let rec ctxToEVarSub __10__ __11__ =
      match (__10__, __11__) with
      | (I.Null, s) -> s
      | (Decl (__G, Dec (_, __A)), s) ->
          let __X = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __X), (ctxToEVarSub (__G, s)))
    let rec ctxToAVarSub __12__ __13__ =
      match (__12__, __13__) with
      | (I.Null, s) -> s
      | (Decl (__G, Dec (_, __A)), s) ->
          let __X = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __X), (ctxToAVarSub (__G, s)))
      | (Decl (__G, ADec (_, d)), s) ->
          let __X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (__X, (I.Shift (~ d))))),
              (ctxToAVarSub (__G, s)))
    let rec solveEqn __14__ __15__ =
      match (__14__, __15__) with
      | ((T.Trivial, s), __G) -> true__
      | ((Unify (__G', e1, __N, eqns), s), __G) ->
          let G'' = append (__G', __G) in
          let s' = shift (G'', s) in
          (((Assign.unifiable (G'', (__N, s'), (e1, s'))) &&
              (solveEqn ((eqns, s), __G)))
            (* G, G' |- s' : D, G, G' *))(* . |- s : D *)
      (* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)
    let rec unifySub' (__G) s1 s2 =
      try Unify.unifySub (__G, s1, s2); true__ with | Unify msg -> false__
    let rec unify (__G) (__Us) (__Us') =
      try Unify.unify (__G, __Us, __Us'); true__ with | Unify msg -> false__
    let rec getHypGoal __16__ __17__ =
      match (__16__, __17__) with
      | (DProg, (Atom p, s)) -> (DProg, (p, s))
      | (DProg (__G, dPool), (Impl (r, __A, Ha, g), s)) ->
          let __D' = IntSyn.Dec (NONE, (I.EClo (__A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((__G, (I.EClo (__A, s))), __G) with
             | Some _ ->
                 let Atom p = g in
                 let __X = I.newEVar (__G, (I.EClo (__A, s))) in
                 ((getHypGoal
                     ((C.DProg (__G, dPool)), (g, (I.Dot ((I.Exp __X), s)))))
                   (* is g always atomic? *))
             | NONE ->
                 getHypGoal
                   ((C.DProg
                       ((I.Decl (__G, __D')),
                         (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (g, (I.dot1 s))))
          else
            getHypGoal
              ((C.DProg
                  ((I.Decl (__G, __D')),
                    (I.Decl (dPool, (C.Dec (r, s, Ha)))))), (g, (I.dot1 s)))
      | (DProg (__G, dPool), (All (__D, g), s)) ->
          let __D' = I.decSub (__D, s) in
          getHypGoal
            ((C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              (g, (I.dot1 s)))
    let rec updateGlobalTable goal flag =
      let ((DProg (__G, dPool) as dProg), (p, s)) =
        getHypGoal ((C.DProg (I.Null, I.Null)), (goal, I.id)) in
      let (__G', DAVars, DEVars, __U', eqn', s') =
        A.abstractEVarCtx (dProg, p, s) in
      let _ =
        if solveEqn ((eqn', s'), __G')
        then ()
        else print "\nresidual equation not solvable!\n" in
      let status =
        if flag then TableParam.Complete else TableParam.Incomplete in
      if TabledSyn.keepTable (IntSyn.targetFam __U')
      then
        match MT.callCheck (DAVars, DEVars, __G', __U', eqn', status) with
        | RepeatedEntry (_, answRef, _) ->
            TableParam.globalTable :=
              ((DAVars, DEVars, __G', __U', eqn', answRef, status) ::
                 (!TableParam.globalTable))
        | _ -> raise (Error "Top level goal should always in the table\n")
      else ()
    let rec keepTable c = TabledSyn.keepTable c
    let rec fillTable () =
      let rec insert =
        function
        | nil -> ()
        | (DAVars, DEVars, __G', __U', eqn', answRef, status)::__T ->
            (match MT.insertIntoTree
                     (DAVars, DEVars, __G', __U', eqn', answRef, status)
             with
             | NewEntry _ -> insert __T
             | _ -> ()) in
      insert (!TableParam.globalTable)
    let rec retrieve' __18__ __19__ __20__ __21__ =
      match (__18__, __19__, __20__, __21__) with
      | ((__G, __U, s), asub, [], sc) -> ()
      | ((__G, __U, s), (esub, asub), ((__D', s1), __O1)::__A, sc) ->
          let s1' =
            ctxToEVarSub (((__D', (I.Shift (I.ctxLength __D'))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (__G, s) in
          let ss1 = shift (__G, scomp) in
          let a = I.comp (asub, s) in
          let ass = shift (__G, a) in
          let easub = I.comp (asub, esub) in
          (((CSManager.trail
               (fun () ->
                  ((if
                      (unifySub' (__G, (shift (__G, esub)), ss)) &&
                        (unifySub'
                           (__G, (shift (__G, (I.comp (asub, esub)))), ss1))
                    then sc __O1
                    else ())
                  (* Succeed *)));
             retrieve' ((__G, __U, s), (esub, asub), __A, sc)))
            (* Fail *))
    let rec retrieveV __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | ((__G, __U, s), [], sc) -> ()
      | ((__G, __U, s), ((DEVars, s1), __O1)::__A, sc) ->
          let s1' =
            ctxToEVarSub (((DEVars, (I.Shift (I.ctxLength DEVars))))
              (* I.id *)) in
          let scomp = I.comp (s1, s1') in
          let ss = shift (__G, s) in
          let ss1 = shift (__G, scomp) in
          (((CSManager.trail
               (fun () -> if unifySub' (__G, ss, ss1) then sc __O1 else ());
             retrieveV ((__G, __U, s), __A, sc)))
            (* for subsumption we must combine it with asumb!!! *))
    let rec retrieveSW (__G, __U, s) asub (AnswL) sc =
      retrieve' ((__G, __U, s), asub, AnswL, sc)
    let rec retrieve k (__G, __U, s) (asub, answRef) sc =
      let lkp = T.lookup answRef in
      let asw' = List.take ((rev (T.solutions answRef)), (T.lookup answRef)) in
      let answ' = List.drop (asw', (!k)) in
      k := lkp; retrieveSW ((__G, __U, s), asub, answ', sc)
    let rec solve __25__ __26__ __27__ =
      match (__25__, __26__, __27__) with
      | ((Atom p, s), (DProg (__G, dPool) as dp), sc) ->
          if TabledSyn.tabledLookup (I.targetFam p)
          then
            let (__G', DAVars, DEVars, __U', eqn', s') =
              A.abstractEVarCtx (dp, p, s) in
            let _ =
              if solveEqn ((eqn', s'), __G')
              then ()
              else
                print
                  "\nresidual equation not solvable! -- This should never happen! \n" in
            (((match MT.callCheck
                       (DAVars, DEVars, __G', __U', eqn', T.Incomplete)
               with
               | NewEntry answRef ->
                   matchAtom
                     ((p, s), dp,
                       (fun pskeleton ->
                          match MT.answerCheck (s', answRef, pskeleton) with
                          | T.repeated -> ()
                          | T.new__ -> sc pskeleton))
               | RepeatedEntry (asub, answRef, T.Incomplete) ->
                   ((if T.noAnswers answRef
                     then
                       (SuspGoals :=
                          ((Loop, (__G', __U', s'), sc, (Unify.suspend ()),
                             (asub, answRef), (ref 0)) :: (!SuspGoals));
                        ())
                     else
                       (let le = T.lookup answRef in
                        SuspGoals :=
                          ((Loop, (__G', __U', s'), sc, (Unify.suspend ()),
                             (asub, answRef), (ref le)) :: (!SuspGoals));
                        retrieve
                          ((ref 0), (__G', __U', s'), (asub, answRef), sc)))
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
                       retrieve
                         ((ref 0), (__G', __U', s'), (asub, answRef), sc))
                   (* Subgoal is not provable *)(* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *))
               | DivergingEntry (asub, answRef) ->
                   (SuspGoals :=
                      (((Divergence ((p, s), dp)), (__G', __U', s'), sc,
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
      | ((Impl (r, __A, Ha, g), s), DProg (__G, dPool), sc) ->
          let __D' = I.Dec (NONE, (I.EClo (__A, s))) in
          if !TableParam.strengthen
          then
            (match MT.memberCtx ((__G, (I.EClo (__A, s))), __G) with
             | Some _ ->
                 let __X = I.newEVar (__G, (I.EClo (__A, s))) in
                 solve
                   ((g, (I.Dot ((I.Exp __X), s))), (C.DProg (__G, dPool)),
                     (fun (__O) -> sc __O))
             | NONE ->
                 solve
                   ((g, (I.dot1 s)),
                     (C.DProg
                        ((I.Decl (__G, __D')),
                          (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                     (fun (__O) -> sc __O)))
          else
            solve
              ((g, (I.dot1 s)),
                (C.DProg
                   ((I.Decl (__G, __D')),
                     (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                (fun (__O) -> sc __O))
      | ((All (__D, g), s), DProg (__G, dPool), sc) ->
          let __D' = I.decSub (__D, s) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              (fun (__O) -> sc __O))
    let rec rSolve __28__ __29__ __30__ __31__ =
      match (__28__, __29__, __30__, __31__) with
      | (ps', (Eq (__Q), s), DProg (__G, dPool), sc) ->
          ((if Unify.unifiable (__G, ps', (__Q, s)) then sc [] else ())
          (* effect: instantiate EVars *)(* call success continuation *))
      | (ps', (Assign (__Q, eqns), s), (DProg (__G, dPool) as dp), sc) ->
          (match Assign.assignable (__G, ps', (__Q, s)) with
           | Some cnstr ->
               aSolve ((eqns, s), dp, cnstr, (fun (__S) -> sc __S))
           | NONE -> ())
      | (ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
                (fun (__S1) ->
                   solve ((g, s), dp, (fun (__S2) -> sc (__S1 @ __S2))))))
            (* is this EVar redundant? -fp *))
      | (ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp), sc)
          ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp __X), s))), dp, (fun (__S) -> sc __S))
      | (ps', (Axists (ADec (Some (__X), d), r), s),
         (DProg (__G, dPool) as dp), sc) ->
          let __X' = I.newAVar () in
          ((rSolve
              (ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve __32__ __33__ __34__ __35__ =
      match (__32__, __33__, __34__, __35__) with
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc [] else ()
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         cnstr, sc) ->
          let G'' = append (__G', __G) in
          let s' = shift (__G', s) in
          if Assign.unifiable (G'', (__N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom ((Root (Ha, __S), s) as ps') (DProg (__G, dPool) as dp)
      sc =
      let rec matchSig =
        function
        | nil -> ()
        | (Const c as Hc)::sgn' ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            (((CSManager.trail
                 (fun () ->
                    rSolve
                      (ps', (r, I.id), dp,
                        (fun (__S) -> sc ((C.Pc c) :: __S))));
               matchSig sgn'))
              (* trail to undo EVar instantiations *))
        (* return indicates failure *) in
      let rec matchDProg __36__ __37__ __38__ =
        match (__36__, __37__, __38__) with
        | (I.Null, I.Null, _) -> matchSig (Index.lookup (cidFromHead Ha))
        | (Decl (__G, _), Decl (dPool', Dec (r, s, Ha')), k) ->
            ((if eqHead (Ha, Ha')
              then
                (CSManager.trail
                   (fun () ->
                      rSolve
                        (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                          (fun (__S) -> sc ((C.Dc k) :: __S))));
                 matchDProg (__G, dPool', (k + 1)))
              else matchDProg (__G, dPool', (k + 1)))
            (* trail to undo EVar instantiations *))
        | (Decl (__G, _), Decl (dPool', C.Parameter), k) ->
            matchDProg (__G, dPool', (k + 1))(* dynamic program exhausted, try signature *) in
      let rec matchConstraint solve try__ =
        let succeeded =
          CSManager.trail
            (fun () ->
               match solve (__G, (I.SClo (__S, s)), try__) with
               | Some (__U) -> (sc [C.Csolver __U]; true__)
               | NONE -> false__) in
        if succeeded then matchConstraint (solve, (try__ + 1)) else () in
      ((match I.constStatus (cidFromHead Ha) with
        | Constraint (cs, solve) -> matchConstraint (solve, 0)
        | _ -> matchDProg (__G, dPool, 1))
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    let rec retrieval __39__ __40__ __41__ __42__ __43__ =
      match (__39__, __40__, __41__, __42__, __43__) with
      | (Loop, (__G', __U', s'), sc, (asub, answRef), n) ->
          ((if T.noAnswers answRef
            then ()
            else retrieve (n, (__G', __U', s'), (asub, answRef), sc))
          (* still  no answers available from previous stages *)
          (* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
          (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *))
      | (Divergence ((p, s), dp), (__G', __U', s'), sc, (asub, answRef), n)
          ->
          matchAtom
            ((p, s), dp,
              (fun pskeleton ->
                 match MT.answerCheck (s', answRef, pskeleton) with
                 | T.repeated -> ()
                 | T.new__ -> sc pskeleton))
    let rec tableSize () = MT.tableSize ()
    let rec suspGoalNo () = List.length (!SuspGoals)
    let rec nextStage () =
      let rec resume =
        function
        | [] -> ()
        | (Susp, s, sc, trail, (asub, answRef), k)::Goals ->
            (CSManager.trail
               (fun () ->
                  Unify.resume trail;
                  retrieval (Susp, s, sc, (asub, answRef), k));
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
    let rec solveQuery (g, s) (DProg (__G, dPool) as dp) sc =
      solve ((g, s), dp, sc)(* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)
    let solve = solveQuery
  end ;;
