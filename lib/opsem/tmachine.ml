
(* Abstract Machine for Tracing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
module TMachine(TMachine:sig
                           (*! structure IntSyn' : INTSYN !*)
                           (*! structure CompSyn' : COMPSYN !*)
                           (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                           module Unify : UNIFY
                           module Assign : ASSIGN
                           module Index : INDEX
                           module CPrint : CPRINT
                           module Names : NAMES
                           (*! sharing Unify.IntSyn = IntSyn' !*)
                           (*! sharing Assign.IntSyn = IntSyn' !*)
                           (*! sharing Index.IntSyn = IntSyn' !*)
                           (*! sharing CPrint.IntSyn = IntSyn' !*)
                           (*! sharing CPrint.CompSyn = CompSyn' !*)
                           (*! sharing Names.IntSyn = IntSyn' !*)
                           (*! structure CSManager : CS_MANAGER !*)
                           (*! sharing CSManager.IntSyn = IntSyn' !*)
                           module Trace : TRACE
                         end) : ABSMACHINE =
  struct
    (*! sharing Trace.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    module I = IntSyn
    module C = CompSyn
    module T = Trace
    module N = Names
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec compose =
      function
      | (G, IntSyn.Null) -> G
      | (G, Decl (G', D)) -> IntSyn.Decl ((compose (G, G')), D)
    let rec shiftSub =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shiftSub (G, s))
    let rec subgoalNum =
      function | I.Nil -> 1 | App (U, S) -> (+) 1 subgoalNum S
    let rec goalToType =
      function
      | (All (D, g), s) ->
          I.Pi (((I.decSub (D, s)), I.Maybe), (goalToType (g, (I.dot1 s))))
      | (Impl (_, A, _, g), s) ->
          I.Pi
            (((I.Dec (NONE, (I.EClo (A, s)))), I.No),
              (goalToType (g, (I.dot1 s))))
      | (Atom p, s) -> I.EClo (p, s)
    let rec solve' =
      function
      | ((Atom p, s), (DProg (G, dPool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, A, Ha, g), s), DProg (G, dPool), sc) ->
          let Dec (SOME x, _) as D' =
            N.decUName (G, (I.Dec (NONE, (I.EClo (A, s))))) in
          let _ = T.signal (G, (T.IntroHyp (Ha, D'))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (function
               | M ->
                   (T.signal (G, (T.DischargeHyp (Ha, D')));
                    sc (I.Lam (D', M)))))
      | ((All (D, g), s), DProg (G, dPool), sc) ->
          let Dec (SOME x, V) as D' = N.decUName (G, (I.decSub (D, s))) in
          let Ha = I.targetHead V in
          let _ = T.signal (G, (T.IntroParm (Ha, D'))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              (function
               | M ->
                   (T.signal (G, (T.DischargeParm (Ha, D')));
                    sc (I.Lam (D', M)))))
    let rec rSolve =
      function
      | (ps', (Eq (Q), s), DProg (G, dPool), HcHa, sc) ->
          (T.signal (G, (T.Unify (HcHa, (I.EClo (Q, s)), (I.EClo ps'))));
           (match Unify.unifiable' (G, (Q, s), ps') with
            | NONE -> (T.signal (G, (T.Resolved HcHa)); sc I.Nil; true__)
            | SOME msg -> (T.signal (G, (T.FailUnify (HcHa, msg))); false__)))
      | (ps', (Assign (Q, eqns), s), (DProg (G, dPool) as dp), HcHa, sc) ->
          (match Assign.assignable (G, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve
                 ((eqns, s), dp, HcHa, cnstr, (function | () -> sc I.Nil))
           | NONE -> false__)
      | (ps', (And (r, A, g), s), (DProg (G, dPool) as dp), HcHa, sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp, HcHa,
              (function
               | S ->
                   (T.signal
                      (G,
                        (T.Subgoal (HcHa, (function | () -> subgoalNum S))));
                    solve' ((g, s), dp, (function | M -> sc (I.App (M, S)))))))
      | (ps', (Exists (Dec (_, A), r), s), (DProg (G, dPool) as dp), HcHa,
         sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp, HcHa,
              (function | S -> sc (I.App (X, S))))
      | (ps', (Axists (ADec (_, d), r), s), (DProg (G, dPool) as dp), HcHa,
         sc) ->
          let X = I.newAVar () in
          rSolve
            (ps', (r, (I.Dot ((I.Exp (I.EClo (X, (I.Shift (~ d))))), s))),
              dp, HcHa, sc)
    let rec aSolve =
      function
      | ((C.Trivial, s), (DProg (G, dPool) as dp), HcHa, cnstr, sc) ->
          if Assign.solveCnstr cnstr
          then (T.signal (G, (T.Resolved HcHa)); sc (); true__)
          else false__
      | ((UnifyEq (G', e1, N, eqns), s), (DProg (G, dPool) as dp), HcHa,
         cnstr, sc) ->
          let G'' = compose (G, G') in
          let s' = shiftSub (G', s) in
          if Assign.unifiable (G'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, HcHa, cnstr, sc)
          else false__
    let rec matchAtom
      (((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc) =
      let tag = T.tagGoal () in
      let _ = T.signal (G, (T.SolveGoal (tag, Ha, (I.EClo ps')))) in
      let deterministic = C.detTableCheck (cidFromHead Ha) in
      let exception SucceedOnce of I.__Spine  in
        let rec matchSig =
          function
          | nil -> (T.signal (G, (T.FailGoal (tag, Ha, (I.EClo ps')))); ())
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (if
                 CSManager.trail
                   (function
                    | () ->
                        rSolve
                          (ps', (r, I.id), dp, (Hc, Ha),
                            (function
                             | S ->
                                 (T.signal
                                    (G,
                                      (T.SucceedGoal
                                         (tag, (Hc, Ha), (I.EClo ps'))));
                                  sc (I.Root (Hc, S))))))
               then
                 (T.signal (G, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                  ())
               else ();
               matchSig sgn') in
        let rec matchSigDet =
          function
          | nil -> (T.signal (G, (T.FailGoal (tag, Ha, (I.EClo ps')))); ())
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (try
                 if
                   CSManager.trail
                     (function
                      | () ->
                          rSolve
                            (ps', (r, I.id), dp, (Hc, Ha),
                              (function
                               | S ->
                                   (T.signal
                                      (G,
                                        (T.SucceedGoal
                                           (tag, (Hc, Ha), (I.EClo ps'))));
                                    raise (SucceedOnce S)))))
                 then
                   (T.signal (G, (T.RetryGoal (tag, (Hc, Ha), (I.EClo ps'))));
                    ())
                 else ();
                 matchSigDet sgn'
               with
               | SucceedOnce (S) ->
                   (T.signal
                      (G, (T.CommitGoal (tag, (Hc, Ha), (I.EClo ps'))));
                    sc (I.Root (Hc, S)))) in
        let rec matchDProg =
          function
          | (I.Null, _) ->
              if deterministic
              then matchSigDet (Index.lookup (cidFromHead Ha))
              else matchSig (Index.lookup (cidFromHead Ha))
          | (Decl (dPool', Dec (r, s, Ha')), k) ->
              if eqHead (Ha, Ha')
              then
                (if deterministic
                 then
                   try
                     if
                       CSManager.trail
                         (function
                          | () ->
                              rSolve
                                (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                  ((I.BVar k), Ha),
                                  (function
                                   | S ->
                                       (T.signal
                                          (G,
                                            (T.SucceedGoal
                                               (tag, ((I.BVar k), Ha),
                                                 (I.EClo ps'))));
                                        raise (SucceedOnce S)))))
                     then
                       (T.signal
                          (G,
                            (T.RetryGoal
                               (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                        ())
                     else ();
                     matchDProg (dPool', (k + 1))
                   with
                   | SucceedOnce (S) ->
                       (T.signal
                          (G,
                            (T.CommitGoal
                               (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                        sc (I.Root ((I.BVar k), S)))
                 else
                   (if
                      CSManager.trail
                        (function
                         | () ->
                             rSolve
                               (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                 ((I.BVar k), Ha),
                                 (function
                                  | S ->
                                      (T.SucceedGoal
                                         (tag, ((I.BVar k), Ha),
                                           (I.EClo ps'));
                                       sc (I.Root ((I.BVar k), S))))))
                    then
                      (T.signal
                         (G,
                           (T.RetryGoal (tag, ((I.BVar k), Ha), (I.EClo ps'))));
                       ())
                    else ();
                    matchDProg (dPool', (k + 1))))
              else matchDProg (dPool', (k + 1))
          | (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1)) in
        let rec matchConstraint (cnstrSolve, try__) =
          let succeeded =
            CSManager.trail
              (function
               | () ->
                   (match cnstrSolve (G, (I.SClo (S, s)), try__) with
                    | SOME (U) -> (sc U; true__)
                    | NONE -> false__)) in
          if succeeded then matchConstraint (cnstrSolve, (try__ + 1)) else () in
        match I.constStatus (cidFromHead Ha) with
        | Constraint (cs, cnstrSolve) -> matchConstraint (cnstrSolve, 0)
        | _ -> matchDProg (dPool, 1)
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
    (* Wed Mar 13 10:27:00 2002 -bp  *)
    (* should probably go to intsyn.fun *)
    (* currently unused *)
    (* solve' ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated to

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
    (* rSolve' ((p,s'), (r,s), dp, (Hc, Ha), sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
       Hc is the clause which generated this residual goal
       Ha is the target family of p and r (which must be equal)
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
    (* effect: instantiate EVars *)
    (* call success continuation *)
    (* deep backtracking *)
    (* shallow backtracking *)
    (* Do not signal unification events for optimized clauses *)
    (* Optimized clause heads lead to unprintable substitutions *)
    (* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *)
    (* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *)
    (* is this EVar redundant? -fp *)
    (* we don't increase the proof term here! *)
    (* aSolve ((ag, s), dp, HcHa, sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated

     Effects: instantiation of EVars in ag[s], dp and sc () *)
    (* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *)
    (* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *)
    (* matchatom ((p, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else res = False
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
    (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
    (* return on failure *)
    (* trail to undo EVar instantiations *)
    (* deep backtracking *)
    (* shallow backtracking *)
    (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
    (* return on failure *)
    (* trail to undo EVar instantiations *)
    (* deep backtracking *)
    (* shallow backtracking *)
    (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
    (* dynamic program exhausted, try signature *)
    (* #succeeds = 1 *)
    (* trail to undo EVar instantiations *)
    (* deep backtracking *)
    (* shallow backtracking *)
    (* #succeeds >= 1 -- allows backtracking *)
    (* deep backtracking *)
    (* shallow backtracking *)
    let rec solve (gs, dp, sc) = T.init (); solve' (gs, dp, sc)
  end ;;
