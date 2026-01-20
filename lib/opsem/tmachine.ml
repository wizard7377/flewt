
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
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false
    let rec compose __2__ __3__ =
      match (__2__, __3__) with
      | (__G, IntSyn.Null) -> __G
      | (__G, Decl (__G', __D)) -> IntSyn.Decl ((compose (__G, __G')), __D)
    let rec shiftSub __4__ __5__ =
      match (__4__, __5__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shiftSub (__G, s))
    let rec subgoalNum =
      function | I.Nil -> 1 | App (__U, __S) -> (+) 1 subgoalNum __S
    let rec goalToType __6__ __7__ =
      match (__6__, __7__) with
      | (All (__D, g), s) ->
          I.Pi (((I.decSub (__D, s)), I.Maybe), (goalToType (g, (I.dot1 s))))
      | (Impl (_, __A, _, g), s) ->
          I.Pi
            (((I.Dec (None, (I.EClo (__A, s)))), I.No),
              (goalToType (g, (I.dot1 s))))
      | (Atom p, s) -> I.EClo (p, s)
    let rec solve' __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | ((Atom p, s), (DProg (__G, dPool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, __A, Ha, g), s), DProg (__G, dPool), sc) ->
          let Dec (Some x, _) as D' =
            N.decUName (__G, (I.Dec (None, (I.EClo (__A, s))))) in
          let _ = T.signal (__G, (T.IntroHyp (Ha, __D'))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__G, __D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (fun (__M) ->
                 T.signal (__G, (T.DischargeHyp (Ha, __D')));
                 sc (I.Lam (__D', __M))))
      | ((All (__D, g), s), DProg (__G, dPool), sc) ->
          let Dec (Some x, __V) as D' = N.decUName (__G, (I.decSub (__D, s))) in
          let Ha = I.targetHead __V in
          let _ = T.signal (__G, (T.IntroParm (Ha, __D'))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              (fun (__M) ->
                 T.signal (__G, (T.DischargeParm (Ha, __D')));
                 sc (I.Lam (__D', __M))))
    let rec rSolve __11__ __12__ __13__ __14__ __15__ =
      match (__11__, __12__, __13__, __14__, __15__) with
      | (ps', (Eq (__Q), s), DProg (__G, dPool), HcHa, sc) ->
          (T.signal (__G, (T.Unify (HcHa, (I.EClo (__Q, s)), (I.EClo ps'))));
           (((match Unify.unifiable' (__G, (__Q, s), ps') with
              | None ->
                  (((T.signal (__G, (T.Resolved HcHa)); sc I.Nil; true))
                  (* call success continuation *))
              | Some msg ->
                  (T.signal (__G, (T.FailUnify (HcHa, msg))); false)))
           (* effect: instantiate EVars *)(* deep backtracking *)))
      | (ps', (Assign (__Q, eqns), s), (DProg (__G, dPool) as dp), HcHa, sc)
          ->
          (((match Assign.assignable (__G, ps', (__Q, s)) with
             | Some cnstr ->
                 aSolve ((eqns, s), dp, HcHa, cnstr, (fun () -> sc I.Nil))
             | None -> ((false)
                 (* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *))))
          (* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *))
      | (ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), HcHa, sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp __X), s))), dp, HcHa,
                (fun (__S) ->
                   T.signal
                     (__G, (T.Subgoal (HcHa, (fun () -> subgoalNum __S))));
                   solve' ((g, s), dp, (fun (__M) -> sc (I.App (__M, __S)))))))
            (* is this EVar redundant? -fp *))
      | (ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp),
         HcHa, sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp __X), s))), dp, HcHa,
              (fun (__S) -> sc (I.App (__X, __S))))
      | (ps', (Axists (ADec (_, d), r), s), (DProg (__G, dPool) as dp), HcHa,
         sc) ->
          let __X = I.newAVar () in
          ((rSolve
              (ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X, (I.Shift (~ d))))), s))),
                dp, HcHa, sc))
            (* we don't increase the proof term here! *))
      (* Optimized clause heads lead to unprintable substitutions *)
      (* Do not signal unification events for optimized clauses *)
      (* shallow backtracking *)
    let rec aSolve __16__ __17__ __18__ __19__ __20__ =
      match (__16__, __17__, __18__, __19__, __20__) with
      | ((C.Trivial, s), (DProg (__G, dPool) as dp), HcHa, cnstr, sc) ->
          if Assign.solveCnstr cnstr
          then (T.signal (__G, (T.Resolved HcHa)); sc (); true)
          else ((false)
            (* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *))
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         HcHa, cnstr, sc) ->
          let G'' = compose (__G, __G') in
          let s' = shiftSub (__G', s) in
          if Assign.unifiable (G'', (__N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, HcHa, cnstr, sc)
          else ((false)
            (* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *))
    let rec matchAtom ((Root (Ha, __S), s) as ps') (DProg (__G, dPool) as dp)
      sc =
      let tag = T.tagGoal () in
      let _ = T.signal (__G, (T.SolveGoal (tag, Ha, (I.EClo ps')))) in
      let deterministic = C.detTableCheck (cidFromHead Ha) in
      let exception SucceedOnce of I.__Spine  in
        let rec matchSig =
          function
          | nil -> (T.signal (__G, (T.FailGoal (tag, Ha, (I.EClo ps')))); ())
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (((((if
                     CSManager.trail
                       (fun () ->
                          rSolve
                            (ps', (r, I.id), dp, (Hc, Ha),
                              (fun (__S) ->
                                 T.signal
                                   (__G,
                                     (T.SucceedGoal
                                        (tag, (Hc, Ha), (I.EClo ps'))));
                                 sc (I.Root (Hc, __S)))))
                   then
                     (T.signal
                        (__G, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                      ())
                   else ())
                 (* deep backtracking *)(* shallow backtracking *));
                 matchSig sgn'))
                (* trail to undo EVar instantiations *))
          (* return on failure *) in
        let rec matchSigDet =
          function
          | nil -> (T.signal (__G, (T.FailGoal (tag, Ha, (I.EClo ps')))); ())
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (((try
                   ((if
                       CSManager.trail
                         (fun () ->
                            rSolve
                              (ps', (r, I.id), dp, (Hc, Ha),
                                (fun (__S) ->
                                   T.signal
                                     (__G,
                                       (T.SucceedGoal
                                          (tag, (Hc, Ha), (I.EClo ps'))));
                                   raise (SucceedOnce __S))))
                     then
                       (T.signal
                          (__G, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                        ())
                     else ())
                   (* deep backtracking *)(* shallow backtracking *));
                   matchSigDet sgn'
                 with
                 | SucceedOnce (__S) ->
                     (T.signal
                        (__G, (T.CommitGoal (tag, (Hc, Ha), (I.EClo ps'))));
                      sc (I.Root (Hc, __S)))))
                (* trail to undo EVar instantiations *))
          (* return on failure *) in
        let rec matchDProg __21__ __22__ =
          match (__21__, __22__) with
          | (I.Null, _) ->
              if deterministic
              then matchSigDet (Index.lookup (cidFromHead Ha))
              else matchSig (Index.lookup (cidFromHead Ha))
          | (Decl (dPool', Dec (r, s, Ha')), k) ->
              if eqHead (Ha, Ha')
              then
                (((if deterministic
                   then
                     try
                       ((if
                           ((CSManager.trail
                               (fun () ->
                                  rSolve
                                    (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                      ((I.BVar k), Ha),
                                      (fun (__S) ->
                                         T.signal
                                           (__G,
                                             (T.SucceedGoal
                                                (tag, ((I.BVar k), Ha),
                                                  (I.EClo ps'))));
                                         raise (SucceedOnce __S)))))
                           (* trail to undo EVar instantiations *))
                         then
                           (T.signal
                              (__G,
                                (T.RetryGoal
                                   (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                            ())
                         else ())
                       (* deep backtracking *)(* shallow backtracking *));
                       matchDProg (dPool', (k + 1))
                     with
                     | SucceedOnce (__S) ->
                         (T.signal
                            (__G,
                              (T.CommitGoal
                                 (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                          sc (I.Root ((I.BVar k), __S)))
                   else
                     (((if
                          CSManager.trail
                            (fun () ->
                               rSolve
                                 (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                   ((I.BVar k), Ha),
                                   (fun (__S) ->
                                      T.SucceedGoal
                                        (tag, ((I.BVar k), Ha), (I.EClo ps'));
                                      sc (I.Root ((I.BVar k), __S)))))
                        then
                          (T.signal
                             (__G,
                               (T.RetryGoal
                                  (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                           ())
                        else ())
                      (* deep backtracking *)(* shallow backtracking *));
                      matchDProg (dPool', (k + 1)))))
                (* #succeeds = 1 *)(* #succeeds >= 1 -- allows backtracking *))
              else matchDProg (dPool', (k + 1))
          | (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1))
          (* dynamic program exhausted, try signature *) in
        let rec matchConstraint cnstrSolve try__ =
          let succeeded =
            CSManager.trail
              (fun () ->
                 match cnstrSolve (__G, (I.SClo (__S, s)), try__) with
                 | Some (__U) -> (sc __U; true)
                 | None -> false) in
          if succeeded then matchConstraint (cnstrSolve, (try__ + 1)) else () in
        ((match I.constStatus (cidFromHead Ha) with
          | Constraint (cs, cnstrSolve) -> matchConstraint (cnstrSolve, 0)
          | _ -> matchDProg (dPool, 1))
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
    let rec solve gs dp sc = T.init (); solve' (gs, dp, sc)
  end ;;
