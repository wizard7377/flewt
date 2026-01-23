module TMachine(TMachine:sig
                           module Unify : UNIFY
                           module Assign : ASSIGN
                           module Index : INDEX
                           module CPrint : CPRINT
                           module Names : NAMES
                           module Trace : TRACE
                         end) : ABSMACHINE =
  struct
    module I = IntSyn
    module C = CompSyn
    module T = Trace
    module N = Names
    let rec cidFromHead = begin function | Const a -> a | Def a -> a end
    let rec eqHead =
      begin function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false end
  let rec compose =
    begin function
    | (g_, IntSyn.Null) -> g_
    | (g_, Decl (g'_, d_)) -> IntSyn.Decl ((compose (g_, g'_)), d_) end
let rec shiftSub =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shiftSub (g_, s)) end
let rec subgoalNum =
  begin function | I.Nil -> 1 | App (u_, s_) -> (+) 1 subgoalNum s_ end
let rec goalToType =
  begin function
  | (All (d_, g), s) ->
      I.Pi (((I.decSub (d_, s)), I.Maybe), (goalToType (g, (I.dot1 s))))
  | (Impl (_, a_, _, g), s) ->
      I.Pi
        (((I.Dec (None, (I.EClo (a_, s)))), I.No),
          (goalToType (g, (I.dot1 s))))
  | (Atom p, s) -> I.EClo (p, s) end
let rec solve' =
  begin function
  | ((Atom p, s), (DProg (g_, dPool) as dp), sc) ->
      matchAtom ((p, s), dp, sc)
  | ((Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
      let Dec (Some x, _) as d'_ =
        N.decUName (g_, (I.Dec (None, (I.EClo (a_, s))))) in
      let _ = T.signal (g_, (T.IntroHyp (Ha, d'_))) in
      solve'
        ((g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
          (begin function
           | m_ ->
               (begin T.signal (g_, (T.DischargeHyp (Ha, d'_)));
                sc (I.Lam (d'_, m_)) end) end))
  | ((All (d_, g), s), DProg (g_, dPool), sc) ->
      let Dec (Some x, v_) as d'_ = N.decUName (g_, (I.decSub (d_, s))) in
      let Ha = I.targetHead v_ in
      let _ = T.signal (g_, (T.IntroParm (Ha, d'_))) in
      solve'
        ((g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
          (begin function
           | m_ ->
               (begin T.signal (g_, (T.DischargeParm (Ha, d'_)));
                sc (I.Lam (d'_, m_)) end) end)) end
let rec rSolve =
  begin function
  | (ps', (Eq (q_), s), DProg (g_, dPool), HcHa, sc) ->
      (begin T.signal (g_, (T.Unify (HcHa, (I.EClo (q_, s)), (I.EClo ps'))));
       (((begin match Unify.unifiable' (g_, (q_, s), ps') with
          | None ->
              (((begin T.signal (g_, (T.Resolved HcHa)); sc I.Nil; true end))
          (* call success continuation *))
       | Some msg ->
           (begin T.signal (g_, (T.FailUnify (HcHa, msg))); false end) end))
  (* effect: instantiate EVars *)(* deep backtracking *)) end)
| (ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), HcHa, sc) ->
    (((begin match Assign.assignable (g_, ps', (q_, s)) with
       | Some cnstr ->
           aSolve
             ((eqns, s), dp, HcHa, cnstr,
               (begin function | () -> sc I.Nil end))
    | None -> ((false)
        (* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *)) end))
(* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *))
| (ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), HcHa, sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp x_), s))), dp, HcHa,
          (begin function
           | s_ ->
               (begin T.signal
                        (g_,
                          (T.Subgoal
                             (HcHa, (begin function | () -> subgoalNum s_ end))));
               solve'
                 ((g, s), dp, (begin function | m_ -> sc (I.App (m_, s_)) end)) end) end)))
(* is this EVar redundant? -fp *))
| (ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), HcHa, sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (ps', (r, (I.Dot ((I.Exp x_), s))), dp, HcHa,
        (begin function | s_ -> sc (I.App (x_, s_)) end))
| (ps', (Axists (ADec (_, d), r), s), (DProg (g_, dPool) as dp), HcHa, sc) ->
    let x_ = I.newAVar () in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp (I.EClo (x_, (I.Shift (- d))))), s))), dp,
          HcHa, sc))
      (* we don't increase the proof term here! *)) end
(* Optimized clause heads lead to unprintable substitutions *)(* Do not signal unification events for optimized clauses *)
(* shallow backtracking *)
let rec aSolve =
  begin function
  | ((C.Trivial, s), (DProg (g_, dPool) as dp), HcHa, cnstr, sc) ->
      if Assign.solveCnstr cnstr
      then begin (begin T.signal (g_, (T.Resolved HcHa)); sc (); true end) end
  else begin ((false)
    (* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *)) end
| ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), HcHa, cnstr,
   sc) ->
    let G'' = compose (g_, g'_) in
    let s' = shiftSub (g'_, s) in
    if Assign.unifiable (G'', (n_, s'), (e1, s'))
    then begin aSolve ((eqns, s), dp, HcHa, cnstr, sc) end
      else begin ((false)
        (* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *)) end end
let rec matchAtom
  (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  let tag = T.tagGoal () in
  let _ = T.signal (g_, (T.SolveGoal (tag, Ha, (I.EClo ps')))) in
  let deterministic = C.detTableCheck (cidFromHead Ha) in
  let exception SucceedOnce of I.spine_  in
    let rec matchSig =
      begin function
      | [] ->
          (begin T.signal (g_, (T.FailGoal (tag, Ha, (I.EClo ps')))); () end)
      | (Hc)::sgn' ->
          let SClause r = C.sProgLookup (cidFromHead Hc) in
          (((begin ((if
                       CSManager.trail
                         (begin function
                          | () ->
                              rSolve
                                (ps', (r, I.id), dp, (Hc, Ha),
                                  (begin function
                                   | s_ ->
                                       (begin T.signal
                                                (g_,
                                                  (T.SucceedGoal
                                                     (tag, (Hc, Ha),
                                                       (I.EClo ps'))));
                                        sc (I.Root (Hc, s_)) end) end)) end)
          then
            begin (begin T.signal
                           (g_, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                   () end) end
      else begin () end)
    (* deep backtracking *)(* shallow backtracking *));
    matchSig sgn' end))
    (* trail to undo EVar instantiations *)) end(* return on failure *) in
let rec matchSigDet =
begin function
| [] -> (begin T.signal (g_, (T.FailGoal (tag, Ha, (I.EClo ps')))); () end)
| (Hc)::sgn' ->
    let SClause r = C.sProgLookup (cidFromHead Hc) in
    (((begin try
               begin ((if
                         CSManager.trail
                           (begin function
                            | () ->
                                rSolve
                                  (ps', (r, I.id), dp, (Hc, Ha),
                                    (begin function
                                     | s_ ->
                                         (begin T.signal
                                                  (g_,
                                                    (T.SucceedGoal
                                                       (tag, (Hc, Ha),
                                                         (I.EClo ps'))));
                                          raise (SucceedOnce s_) end) end)) end)
       then
         begin (begin T.signal
                        (g_, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                () end) end
    else begin () end)
(* deep backtracking *)(* shallow backtracking *));
matchSigDet sgn' end
with
| SucceedOnce (s_) ->
    (begin T.signal (g_, (T.CommitGoal (tag, (Hc, Ha), (I.EClo ps'))));
     sc (I.Root (Hc, s_)) end) end))
(* trail to undo EVar instantiations *)) end(* return on failure *) in
let rec matchDProg =
begin function
| (I.Null, _) ->
    if deterministic
    then begin matchSigDet (Index.lookup (cidFromHead Ha)) end
    else begin matchSig (Index.lookup (cidFromHead Ha)) end
| (Decl (dPool', Dec (r, s, Ha')), k) ->
    if eqHead (Ha, Ha')
    then
      begin (((if deterministic
               then
                 begin begin try
                               begin ((if
                                         ((CSManager.trail
                                             (begin function
                                              | () ->
                                                  rSolve
                                                    (ps',
                                                      (r,
                                                        (I.comp
                                                           (s, (I.Shift k)))),
                                                      dp, ((I.BVar k), Ha),
                                                      (begin function
                                                       | s_ ->
                                                           (begin T.signal
                                                                    (g_,
                                                                    (T.SucceedGoal
                                                                    (tag,
                                                                    ((I.BVar
                                                                    k), Ha),
                                                                    (I.EClo
                                                                    ps'))));
                                                            raise
                                                              (SucceedOnce s_) end) end)) end))
                               (* trail to undo EVar instantiations *))
                       then
                         begin (begin T.signal
                                        (g_,
                                          (T.RetryGoal
                                             (tag, ((I.BVar k), Ha),
                                               (I.EClo ps'))));
                                () end) end
               else begin () end)
    (* deep backtracking *)(* shallow backtracking *));
    matchDProg (dPool', (k + 1)) end
with
| SucceedOnce (s_) ->
    (begin T.signal
             (g_, (T.CommitGoal (tag, ((I.BVar k), Ha), (I.EClo ps'))));
     sc (I.Root ((I.BVar k), s_)) end) end end
else begin
  (begin ((if
             CSManager.trail
               (begin function
                | () ->
                    rSolve
                      (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                        ((I.BVar k), Ha),
                        (begin function
                         | s_ ->
                             (begin T.SucceedGoal
                                      (tag, ((I.BVar k), Ha), (I.EClo ps'));
                              sc (I.Root ((I.BVar k), s_)) end) end)) end)
then
  begin (begin T.signal
                 (g_, (T.RetryGoal (tag, ((I.BVar k), Ha), (I.EClo ps'))));
         () end) end else begin () end)
(* deep backtracking *)(* shallow backtracking *));
matchDProg (dPool', (k + 1)) end) end))
(* #succeeds = 1 *)(* #succeeds >= 1 -- allows backtracking *)) end
else begin matchDProg (dPool', (k + 1)) end
| (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1)) end
(* dynamic program exhausted, try signature *) in
let rec matchConstraint (cnstrSolve, try_) =
let succeeded =
  CSManager.trail
    (begin function
     | () ->
         (begin match cnstrSolve (g_, (I.SClo (s_, s)), try_) with
          | Some (u_) -> (begin sc u_; true end)
         | None -> false end) end) in
if succeeded then begin matchConstraint (cnstrSolve, (try_ + 1)) end
else begin () end in
((begin match I.constStatus (cidFromHead Ha) with
| Constraint (cs, cnstrSolve) -> matchConstraint (cnstrSolve, 0)
| _ -> matchDProg (dPool, 1) end)
(* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
(* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
let rec solve (gs, dp, sc) = begin T.init (); solve' (gs, dp, sc) end end
