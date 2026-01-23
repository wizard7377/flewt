module type TABLED  =
  sig
    val solve :
      ((CompSyn.goal_ * IntSyn.sub_) * CompSyn.dProg_ *
        (CompSyn.pskeleton -> unit)) -> unit
    val updateGlobalTable : (CompSyn.goal_ * bool) -> unit
    val keepTable : IntSyn.cid -> bool
    val fillTable : unit -> unit
    val nextStage : unit -> bool
    val reset : unit -> unit
    val tableSize : unit -> int
    val suspGoalNo : unit -> int
  end


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
    type suspType_ =
      | Loop 
      | Divergence of ((IntSyn.exp_ * IntSyn.sub_) * CompSyn.dProg_) 
    let ((SuspGoals) :
      (suspType_ * (IntSyn.dctx * IntSyn.exp_ * IntSyn.sub_) *
        (CompSyn.pskeleton -> unit) * Unify.unifTrail * ((IntSyn.sub_ *
        IntSyn.sub_) * T.answer) * int ref) list ref)
      = ref []
    exception Error of string 
    let rec cidFromHead = begin function | Const a -> a | Def a -> a end
    let rec eqHead =
      begin function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false end
  let rec append =
    begin function
    | (IntSyn.Null, g_) -> g_
    | (Decl (g'_, d_), g_) -> IntSyn.Decl ((append (g'_, g_)), d_) end
let rec shift =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Lam (d_, v_))) end
let rec compose =
  begin function
  | (IntSyn.Null, g_) -> g_
  | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose (g_, g'_)), d_) end
let rec ctxToEVarSub =
  begin function
  | (I.Null, s) -> s
  | (Decl (g_, Dec (_, a_)), s) ->
      let x_ = I.newEVar (I.Null, a_) in
      I.Dot ((I.Exp x_), (ctxToEVarSub (g_, s))) end
let rec ctxToAVarSub =
  begin function
  | (I.Null, s) -> s
  | (Decl (g_, Dec (_, a_)), s) ->
      let x_ = I.newEVar (I.Null, a_) in
      I.Dot ((I.Exp x_), (ctxToAVarSub (g_, s)))
  | (Decl (g_, ADec (_, d)), s) ->
      let x_ = I.newAVar () in
      I.Dot ((I.Exp (I.EClo (x_, (I.Shift (- d))))), (ctxToAVarSub (g_, s))) end
let rec solveEqn =
  begin function
  | ((T.Trivial, s), g_) -> true
  | ((Unify (g'_, e1, n_, eqns), s), g_) ->
      let G'' = append (g'_, g_) in
      let s' = shift (G'', s) in
      (((Assign.unifiable (G'', (n_, s'), (e1, s'))) &&
          (solveEqn ((eqns, s), g_)))
        (* G, G' |- s' : D, G, G' *)) end(* . |- s : D *)
(* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)
let rec unifySub' (g_, s1, s2) =
  begin try begin Unify.unifySub (g_, s1, s2); true end
  with | Unify msg -> false end
let rec unify (g_, us_, us'_) =
  begin try begin Unify.unify (g_, us_, us'_); true end
  with | Unify msg -> false end
let rec getHypGoal =
  begin function
  | (DProg, (Atom p, s)) -> (DProg, (p, s))
  | (DProg (g_, dPool), (Impl (r, a_, Ha, g), s)) ->
      let d'_ = IntSyn.Dec (None, (I.EClo (a_, s))) in
      if !TableParam.strengthen
      then
        begin (begin match MT.memberCtx ((g_, (I.EClo (a_, s))), g_) with
               | Some _ ->
                   let Atom p = g in
                   let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
                   ((getHypGoal
                       ((C.DProg (g_, dPool)), (g, (I.Dot ((I.Exp x_), s)))))
                     (* is g always atomic? *))
               | None ->
                   getHypGoal
                     ((C.DProg
                         ((I.Decl (g_, d'_)),
                           (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                       (g, (I.dot1 s))) end) end
      else begin
        getHypGoal
          ((C.DProg
              ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
            (g, (I.dot1 s))) end
| (DProg (g_, dPool), (All (d_, g), s)) ->
    let d'_ = I.decSub (d_, s) in
    getHypGoal
      ((C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
        (g, (I.dot1 s))) end
let rec updateGlobalTable (goal, flag) =
  let ((DProg (g_, dPool) as dProg), (p, s)) =
    getHypGoal ((C.DProg (I.Null, I.Null)), (goal, I.id)) in
  let (g'_, DAVars, DEVars, u'_, eqn', s') = A.abstractEVarCtx (dProg, p, s) in
  let _ = if solveEqn ((eqn', s'), g'_) then begin () end
    else begin print "\nresidual equation not solvable!\n" end in
  let status = if flag then begin TableParam.Complete end
    else begin TableParam.Incomplete end in
if TabledSyn.keepTable (IntSyn.targetFam u'_)
then
  begin begin match MT.callCheck (DAVars, DEVars, g'_, u'_, eqn', status)
              with
        | RepeatedEntry (_, answRef, _) ->
            TableParam.globalTable :=
              ((DAVars, DEVars, g'_, u'_, eqn', answRef, status) ::
                 !TableParam.globalTable)
        | _ -> raise (Error "Top level goal should always in the table\n") end end
  else begin () end
let rec keepTable c = TabledSyn.keepTable c
let rec fillTable () =
  let rec insert =
    begin function
    | [] -> ()
    | (DAVars, DEVars, g'_, u'_, eqn', answRef, status)::t_ ->
        (begin match MT.insertIntoTree
                       (DAVars, DEVars, g'_, u'_, eqn', answRef, status)
               with
         | NewEntry _ -> insert t_
         | _ -> () end) end in
insert !TableParam.globalTable
let rec retrieve' =
  begin function
  | ((g_, u_, s), asub, [], sc) -> ()
  | ((g_, u_, s), (esub, asub), ((d'_, s1), o1_)::a_, sc) ->
      let s1' =
        ctxToEVarSub (((d'_, (I.Shift (I.ctxLength d'_))))
          (* I.id *)) in
      let scomp = I.comp (s1, s1') in
      let ss = shift (g_, s) in
      let ss1 = shift (g_, scomp) in
      let a = I.comp (asub, s) in
      let ass = shift (g_, a) in
      let easub = I.comp (asub, esub) in
      (((begin CSManager.trail
                 (begin function
                  | () ->
                      ((if
                          (unifySub' (g_, (shift (g_, esub)), ss)) &&
                            (unifySub'
                               (g_, (shift (g_, (I.comp (asub, esub)))), ss1))
                        then begin sc o1_ end
                      else begin () end)(* Succeed *)) end);
        retrieve' ((g_, u_, s), (esub, asub), a_, sc) end))
        (* Fail *)) end
let rec retrieveV =
  begin function
  | ((g_, u_, s), [], sc) -> ()
  | ((g_, u_, s), ((DEVars, s1), o1_)::a_, sc) ->
      let s1' =
        ctxToEVarSub (((DEVars, (I.Shift (I.ctxLength DEVars))))
          (* I.id *)) in
      let scomp = I.comp (s1, s1') in
      let ss = shift (g_, s) in
      let ss1 = shift (g_, scomp) in
      (((begin CSManager.trail
                 (begin function
                  | () -> if unifySub' (g_, ss, ss1) then begin sc o1_ end
                      else begin () end end);
        retrieveV ((g_, u_, s), a_, sc) end))
      (* for subsumption we must combine it with asumb!!! *)) end
let rec retrieveSW ((g_, u_, s), asub, AnswL, sc) =
  retrieve' ((g_, u_, s), asub, AnswL, sc)
let rec retrieve (k, (g_, u_, s), (asub, answRef), sc) =
  let lkp = T.lookup answRef in
  let asw' = List.take ((rev (T.solutions answRef)), (T.lookup answRef)) in
  let answ' = List.drop (asw', !k) in
  begin k := lkp; retrieveSW ((g_, u_, s), asub, answ', sc) end
let rec solve =
  begin function
  | ((Atom p, s), (DProg (g_, dPool) as dp), sc) ->
      if TabledSyn.tabledLookup (I.targetFam p)
      then
        begin let (g'_, DAVars, DEVars, u'_, eqn', s') =
                A.abstractEVarCtx (dp, p, s) in
              let _ = if solveEqn ((eqn', s'), g'_) then begin () end
                else begin
                  print
                    "\nresidual equation not solvable! -- This should never happen! \n" end in
      (((begin match MT.callCheck
                       (DAVars, DEVars, g'_, u'_, eqn', T.Incomplete)
               with
         | NewEntry answRef ->
             matchAtom
               ((p, s), dp,
                 (begin function
                  | pskeleton ->
                      (begin match MT.answerCheck (s', answRef, pskeleton)
                             with
                       | T.repeated -> ()
                       | T.new_ -> sc pskeleton end) end))
      | RepeatedEntry (asub, answRef, T.Incomplete) ->
          ((if T.noAnswers answRef
            then
              begin (begin SuspGoals :=
                             ((Loop, (g'_, u'_, s'), sc, (Unify.suspend ()),
                                (asub, answRef), (ref 0)) :: !SuspGoals);
                     () end) end
      else begin
        (let le = T.lookup answRef in
         begin SuspGoals :=
                 ((Loop, (g'_, u'_, s'), sc, (Unify.suspend ()),
                    (asub, answRef), (ref le)) :: !SuspGoals);
         retrieve ((ref 0), (g'_, u'_, s'), (asub, answRef), sc) end) end)
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
      ((if T.noAnswers answRef then begin () end
      else begin retrieve ((ref 0), (g'_, u'_, s'), (asub, answRef), sc) end)
(* Subgoal is not provable *)(* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *))
| DivergingEntry (asub, answRef) ->
    (begin SuspGoals :=
             (((Divergence ((p, s), dp)), (g'_, u'_, s'), sc,
                (Unify.suspend ()),
                ((((I.id, asub))(* this is a hack *)),
                  answRef), (ref 0))
                :: !SuspGoals);
     () end) end))
(* Side effect: D', G' |- U' added to table *)(* loop detected  -- currently not functioning correctly.
                    we might be using this as part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
(* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)) end
else begin matchAtom ((p, s), dp, sc) end
| ((Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
    let d'_ = I.Dec (None, (I.EClo (a_, s))) in
    if !TableParam.strengthen
    then
      begin (begin match MT.memberCtx ((g_, (I.EClo (a_, s))), g_) with
             | Some _ ->
                 let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
                 solve
                   ((g, (I.Dot ((I.Exp x_), s))), (C.DProg (g_, dPool)),
                     (begin function | o_ -> sc o_ end))
      | None ->
          solve
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (begin function | o_ -> sc o_ end)) end) end
else begin
  solve
    ((g, (I.dot1 s)),
      (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
      (begin function | o_ -> sc o_ end)) end
| ((All (d_, g), s), DProg (g_, dPool), sc) ->
    let d'_ = I.decSub (d_, s) in
    solve
      ((g, (I.dot1 s)),
        (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
        (begin function | o_ -> sc o_ end)) end
let rec rSolve =
  begin function
  | (ps', (Eq (q_), s), DProg (g_, dPool), sc) ->
      ((if Unify.unifiable (g_, ps', (q_, s)) then begin sc [] end
      else begin () end)
  (* effect: instantiate EVars *)(* call success continuation *))
  | (ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), sc) ->
      (begin match Assign.assignable (g_, ps', (q_, s)) with
       | Some cnstr ->
           aSolve ((eqns, s), dp, cnstr, (begin function | s_ -> sc s_ end))
      | None -> () end)
| (ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | s1_ ->
               solve
                 ((g, s), dp, (begin function | s2_ -> sc (s1_ @ s2_) end)) end)))
(* is this EVar redundant? -fp *))
| (ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
        (begin function | s_ -> sc s_ end))
| (ps', (Axists (ADec (Some (x_), d), r), s), (DProg (g_, dPool) as dp), sc)
    ->
    let x'_ = I.newAVar () in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp (I.EClo (x'_, (I.Shift (- d))))), s))), dp,
          sc))
      (* we don't increase the proof term here! *)) end
(* fail *)
let rec aSolve =
  begin function
  | ((C.Trivial, s), dp, cnstr, sc) ->
      if Assign.solveCnstr cnstr then begin sc [] end else begin () end
  | ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), cnstr, sc)
      ->
      let G'' = append (g'_, g_) in
      let s' = shift (g'_, s) in
      if Assign.unifiable (G'', (n_, s'), (e1, s'))
      then begin aSolve ((eqns, s), dp, cnstr, sc) end else begin () end end
let rec matchAtom
  (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  let rec matchSig =
    begin function
    | [] -> ()
    | (Const c as Hc)::sgn' ->
        let SClause r = C.sProgLookup (cidFromHead Hc) in
        (((begin CSManager.trail
                   (begin function
                    | () ->
                        rSolve
                          (ps', (r, I.id), dp,
                            (begin function | s_ -> sc ((C.Pc c) :: s_) end)) end);
        matchSig sgn' end))
    (* trail to undo EVar instantiations *)) end(* return indicates failure *) in
let rec matchDProg =
begin function
| (I.Null, I.Null, _) -> matchSig (Index.lookup (cidFromHead Ha))
| (Decl (g_, _), Decl (dPool', Dec (r, s, Ha')), k) ->
    ((if eqHead (Ha, Ha')
      then
        begin (begin CSManager.trail
                       (begin function
                        | () ->
                            rSolve
                              (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                (begin function | s_ -> sc ((C.Dc k) :: s_) end)) end);
      matchDProg (g_, dPool', (k + 1)) end) end
else begin matchDProg (g_, dPool', (k + 1)) end)
(* trail to undo EVar instantiations *))
| (Decl (g_, _), Decl (dPool', C.Parameter), k) ->
    matchDProg (g_, dPool', (k + 1)) end(* dynamic program exhausted, try signature *) in
let rec matchConstraint (solve, try_) =
let succeeded =
  CSManager.trail
    (begin function
     | () ->
         (begin match solve (g_, (I.SClo (s_, s)), try_) with
          | Some (u_) -> (begin sc [C.Csolver u_]; true end)
         | None -> false end) end) in
if succeeded then begin matchConstraint (solve, (try_ + 1)) end
else begin () end in
((begin match I.constStatus (cidFromHead Ha) with
| Constraint (cs, solve) -> matchConstraint (solve, 0)
| _ -> matchDProg (g_, dPool, 1) end)
(* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
let rec retrieval =
  begin function
  | (Loop, (g'_, u'_, s'), sc, (asub, answRef), n) ->
      ((if T.noAnswers answRef then begin () end
      else begin retrieve (n, (g'_, u'_, s'), (asub, answRef), sc) end)
  (* still  no answers available from previous stages *)
  (* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
  (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *))
  | (Divergence ((p, s), dp), (g'_, u'_, s'), sc, (asub, answRef), n) ->
      matchAtom
        ((p, s), dp,
          (begin function
           | pskeleton ->
               (begin match MT.answerCheck (s', answRef, pskeleton) with
                | T.repeated -> ()
                | T.new_ -> sc pskeleton end) end)) end
let rec tableSize () = MT.tableSize ()
let rec suspGoalNo () = List.length !SuspGoals
let rec nextStage () =
  let rec resume =
    begin function
    | [] -> ()
    | (Susp, s, sc, trail, (asub, answRef), k)::Goals ->
        (begin CSManager.trail
                 (begin function
                  | () ->
                      (begin Unify.resume trail;
                       retrieval (Susp, s, sc, (asub, answRef), k) end) end);
    resume Goals end) end in
let SG = rev !SuspGoals in
((if MT.updateTable ()
then
  begin (begin (TableParam.stageCtr := !TableParam.stageCtr) + 1;
         resume SG;
         true end) end else begin false end)
(* table changed during previous stage *)(* table did not change during previous stage *))
let rec reset () =
  begin SuspGoals := []; MT.reset (); TableParam.stageCtr := 0 end
let rec solveQuery ((g, s), (DProg (g_, dPool) as dp), sc) =
  solve ((g, s), dp, sc)(* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)
let solve = solveQuery end
