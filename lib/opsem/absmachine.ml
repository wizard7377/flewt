module type ABSMACHINE  =
  sig
    val solve :
      ((CompSyn.goal_ * IntSyn.sub_) * CompSyn.dProg_ *
        (IntSyn.exp_ -> unit)) -> unit
  end


module AbsMachine(AbsMachine:sig
                               module Unify : UNIFY
                               module Assign : ASSIGN
                               module Index : INDEX
                               module CPrint : CPRINT
                               module Print : PRINT
                               module Names : NAMES
                             end) : ABSMACHINE =
  struct
    module I = IntSyn
    module C = CompSyn
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
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec solve =
  begin function
  | ((Atom p, s), (DProg (g_, dPool) as dp), sc) ->
      matchAtom ((p, s), dp, sc)
  | ((Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
      let d'_ = I.Dec (None, (I.EClo (a_, s))) in
      solve
        ((g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
          (begin function | m_ -> sc (I.Lam (d'_, m_)) end))
  | ((All (d_, g), s), DProg (g_, dPool), sc) ->
      let d'_ = Names.decLUName (g_, (I.decSub (d_, s))) in
      ((solve
          ((g, (I.dot1 s)),
            (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
            (begin function | m_ -> sc (I.Lam (d'_, m_)) end)))
      (*      val D' = I.decSub (D, s) *)) end
let rec rSolve =
  begin function
  | (ps', (Eq (q_), s), DProg (g_, dPool), sc) ->
      ((if Unify.unifiable (g_, (q_, s), ps') then begin sc I.Nil end
      else begin () end)
  (* effect: instantiate EVars *)(* call success continuation *))
  | (ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), sc) ->
      (begin match Assign.assignable (g_, ps', (q_, s)) with
       | Some cnstr ->
           aSolve
             ((eqns, s), dp, cnstr, (begin function | () -> sc I.Nil end))
      | None -> () end)
| (ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | s_ ->
               solve
                 ((g, s), dp, (begin function | m_ -> sc (I.App (m_, s_)) end)) end)))
(* is this EVar redundant? -fp *)(* same effect as s^-1 *))
| (ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
        (begin function | s_ -> sc (I.App (x_, s_)) end))
| (ps', (Axists (ADec (_, d), r), s), (DProg (g_, dPool) as dp), sc) ->
    let x'_ = I.newAVar () in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp (I.EClo (x'_, (I.Shift (- d))))), s))), dp,
          sc))
      (* we don't increase the proof term here! *)) end
(* fail *)
let rec aSolve =
  begin function
  | ((C.Trivial, s), dp, cnstr, sc) ->
      if Assign.solveCnstr cnstr then begin sc () end else begin () end
  | ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), cnstr, sc)
      ->
      let G'' = compose (g_, g'_) in
      let s' = shiftSub (g'_, s) in
      if Assign.unifiable (G'', (n_, s'), (e1, s'))
      then begin aSolve ((eqns, s), dp, cnstr, sc) end else begin () end end
let rec matchAtom
  (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  let deterministic = C.detTableCheck (cidFromHead Ha) in
  let exception SucceedOnce of I.spine_  in
    let rec matchSig =
      begin function
      | [] -> ()
      | (Hc)::sgn' ->
          let SClause r = C.sProgLookup (cidFromHead Hc) in
          (((begin CSManager.trail
                     (begin function
                      | () ->
                          rSolve
                            (ps', (r, I.id), dp,
                              (begin function | s_ -> sc (I.Root (Hc, s_)) end)) end);
          matchSig sgn' end))
      (* trail to undo EVar instantiations *)) end(* return unit on failure *) in
let rec matchSigDet =
  begin function
  | [] -> ()
  | (Hc)::sgn' ->
      let SClause r = C.sProgLookup (cidFromHead Hc) in
      (((begin try
                 begin CSManager.trail
                         (begin function
                          | () ->
                              rSolve
                                (ps', (r, I.id), dp,
                                  (begin function
                                   | s_ -> raise (SucceedOnce s_) end)) end);
         matchSigDet sgn' end
  with | SucceedOnce (s_) -> sc (I.Root (Hc, s_)) end))
  (* trail to undo EVar instantiations *)) end(* return unit on failure *) in
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
                               begin ((CSManager.trail
                                         (begin function
                                          | () ->
                                              rSolve
                                                (ps',
                                                  (r,
                                                    (I.comp (s, (I.Shift k)))),
                                                  dp,
                                                  (begin function
                                                   | s_ ->
                                                       raise (SucceedOnce s_) end)) end))
                       (* trail to undo EVar instantiations *));
                       matchDProg (dPool', (k + 1)) end
      with | SucceedOnce (s_) -> sc (I.Root ((I.BVar k), s_)) end end
else begin
  (begin ((CSManager.trail
             (begin function
              | () ->
                  rSolve
                    (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                      (begin function | s_ -> sc (I.Root ((I.BVar k), s_)) end)) end))
(* trail to undo EVar instantiations *));
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
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
let solve = solve end
