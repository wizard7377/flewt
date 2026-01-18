
(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
module type ABSMACHINE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    val solve :
      ((CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg *
        (IntSyn.__Exp -> unit)) -> unit
  end;;




(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
module AbsMachine(AbsMachine:sig
                               (*! structure IntSyn' : INTSYN !*)
                               (*! structure CompSyn' : COMPSYN !*)
                               (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                               module Unify : UNIFY
                               module Assign : ASSIGN
                               module Index : INDEX
                               module CPrint : CPRINT
                               module Print : PRINT
                               (*! sharing Unify.IntSyn = IntSyn' !*)
                               (*! sharing Assign.IntSyn = IntSyn' !*)
                               (*! sharing Index.IntSyn = IntSyn' !*)
                               (* CPrint currently unused *)
                               (*! sharing CPrint.IntSyn = IntSyn' !*)
                               (*! sharing CPrint.CompSyn = CompSyn' !*)
                               (*! sharing Print.IntSyn = IntSyn' !*)
                               module Names : NAMES
                             end) : ABSMACHINE =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    module I = IntSyn
    module C = CompSyn
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec compose =
      function
      | (__g, IntSyn.Null) -> __g
      | (__g, Decl (__g', __d)) -> IntSyn.Decl ((compose (__g, __g')), __d)
    let rec shiftSub =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (__g, __d), s) -> I.dot1 (shiftSub (__g, s))
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec solve =
      function
      | ((Atom p, s), (DProg (__g, dPool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, A, Ha, g), s), DProg (__g, dPool), sc) ->
          let __d' = I.Dec (None, (I.EClo (A, s))) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__g, __d')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (function | M -> sc (I.Lam (__d', M))))
      | ((All (__d, g), s), DProg (__g, dPool), sc) ->
          let __d' = Names.decLUName (__g, (I.decSub (__d, s))) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__g, __d')), (I.Decl (dPool, C.Parameter)))),
              (function | M -> sc (I.Lam (__d', M))))
    let rec rSolve =
      function
      | (ps', (Eq (Q), s), DProg (__g, dPool), sc) ->
          if Unify.unifiable (__g, (Q, s), ps') then sc I.Nil else ()
      | (ps', (Assign (Q, eqns), s), (DProg (__g, dPool) as dp), sc) ->
          (match Assign.assignable (__g, ps', (Q, s)) with
           | Some cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | () -> sc I.Nil))
           | None -> ())
      | (ps', (And (r, A, g), s), (DProg (__g, dPool) as dp), sc) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function
               | S -> solve ((g, s), dp, (function | M -> sc (I.App (M, S))))))
      | (ps', (Exists (Dec (_, A), r), s), (DProg (__g, dPool) as dp), sc) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function | S -> sc (I.App (x, S))))
      | (ps', (Axists (ADec (_, d), r), s), (DProg (__g, dPool) as dp), sc) ->
          let x' = I.newAVar () in
          rSolve
            (ps', (r, (I.Dot ((I.Exp (I.EClo (x', (I.Shift (~- d))))), s))),
              dp, sc)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc () else ()
      | ((UnifyEq (__g', e1, N, eqns), s), (DProg (__g, dPool) as dp), cnstr, sc)
          ->
          let __g'' = compose (__g, __g') in
          let s' = shiftSub (__g', s) in
          if Assign.unifiable (__g'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom
      (((Root (Ha, S), s) as ps'), (DProg (__g, dPool) as dp), sc) =
      let deterministic = C.detTableCheck (cidFromHead Ha) in
      let exception SucceedOnce of I.__Spine  in
        let rec matchSig =
          function
          | nil -> ()
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (CSManager.trail
                 (function
                  | () ->
                      rSolve
                        (ps', (r, I.id), dp,
                          (function | S -> sc (I.Root (Hc, S)))));
               matchSig sgn') in
        let rec matchSigDet =
          function
          | nil -> ()
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (try
                 CSManager.trail
                   (function
                    | () ->
                        rSolve
                          (ps', (r, I.id), dp,
                            (function | S -> raise (SucceedOnce S))));
                 matchSigDet sgn'
               with | SucceedOnce (S) -> sc (I.Root (Hc, S))) in
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
                     CSManager.trail
                       (function
                        | () ->
                            rSolve
                              (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                (function | S -> raise (SucceedOnce S))));
                     matchDProg (dPool', (k + 1))
                   with | SucceedOnce (S) -> sc (I.Root ((I.BVar k), S))
                 else
                   (CSManager.trail
                      (function
                       | () ->
                           rSolve
                             (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                               (function | S -> sc (I.Root ((I.BVar k), S)))));
                    matchDProg (dPool', (k + 1))))
              else matchDProg (dPool', (k + 1))
          | (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1)) in
        let rec matchConstraint (cnstrSolve, try__) =
          let succeeded =
            CSManager.trail
              (function
               | () ->
                   (match cnstrSolve (__g, (I.SClo (S, s)), try__) with
                    | Some (__u) -> (sc __u; true__)
                    | None -> false__)) in
          if succeeded then matchConstraint (cnstrSolve, (try__ + 1)) else () in
        match I.constStatus (cidFromHead Ha) with
        | Constraint (cs, cnstrSolve) -> matchConstraint (cnstrSolve, 0)
        | _ -> matchDProg (dPool, 1)
    (* We write
       __g |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       __g |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)
    (* Wed Mar 13 10:27:00 2002 -bp  *)
    (* should probably go to intsyn.fun *)
    (* solve ((g, s), dp, sc) = ()
     Invariants:
       dp = (__g, dPool) where  __g ~ dPool  (context __g matches dPool)
       __g |- s : __g'
       __g' |- g  goal
       if  __g |- M : g[s]
       then  sc M  is evaluated

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
    (*      val __d' = I.decSub (__d, s) *)
    (* rSolve ((p,s'), (r,s), dp, sc) = ()
     Invariants:
       dp = (__g, dPool) where __g ~ dPool
       __g |- s : __g'
       __g' |- r  resgoal
       __g |- s' : __g''
       __g'' |- p : H @ S' (mod whnf)
       if __g |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
    (* effect: instantiate EVars *)
    (* call success continuation *)
    (* fail *)
    (* is this EVar redundant? -fp *)
    (* same effect as s^-1 *)
    (* we don't increase the proof term here! *)
    (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (__g, dPool) where __g ~ dPool
       __g |- s : __g'
       if __g |- ag[s] auxgoal
       then sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *)
    (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (__g, dPool) where __g ~ dPool
       __g |- s : __g'
       __g' |- p : type, p = H @ S mod whnf
       if __g |- M :: p[s]
       then sc M is evaluated
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
    (* return unit on failure *)
    (* trail to undo EVar instantiations *)
    (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
    (* return unit on failure *)
    (* trail to undo EVar instantiations *)
    (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
    (* dynamic program exhausted, try signature *)
    (* #succeeds = 1 *)
    (* trail to undo EVar instantiations *)
    (* #succeeds >= 1 -- allows backtracking *)
    (* trail to undo EVar instantiations *)
    let solve = solve
  end ;;
