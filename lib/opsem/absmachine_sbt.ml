module type ABSMACHINESBT  =
  sig
    val solve :
      ((CompSyn.goal_ * IntSyn.sub_) * CompSyn.dProg_ *
        (CompSyn.flatterm_ list -> unit)) -> unit
  end


module AbsMachineSbt(AbsMachineSbt:sig
                                     module Unify : UNIFY
                                     module SubTree : SUBTREE
                                     module Assign : ASSIGN
                                     module Index : INDEX
                                     module CPrint : CPRINT
                                     module Print : PRINT
                                     module Names : NAMES
                                   end) : ABSMACHINESBT =
  struct
    module I = IntSyn
    module C = CompSyn
    let (mSig :
      (((IntSyn.exp_ * IntSyn.sub_) * CompSyn.dProg_ *
         (CompSyn.flatterm_ list -> unit)) -> unit)
        ref)
      = ref (begin function | (ps, dp, sc) -> () end)
    let rec cidFromHead = begin function | Const a -> a | Def a -> a end
  let rec eqHead =
    begin function
    | (Const a, Const a') -> a = a'
    | (Def a, Def a') -> a = a'
    | _ -> false end
let rec compose' =
  begin function
  | (IntSyn.Null, g_) -> g_
  | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose' (g_, g'_)), d_) end
let rec shift =
  begin function
  | (IntSyn.Null, s) -> s
  | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec invShiftN (n, s) = if n = 0 then begin I.comp (I.invShift, s) end
  else begin I.comp (I.invShift, (invShiftN ((n - 1), s))) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec printSub =
  begin function
  | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
  | Dot (Idx n, s) ->
      (begin print (((^) "Idx " Int.toString n) ^ " . "); printSub s end)
  | Dot (Exp (EVar (_, _, _, _)), s) ->
      (begin print "Exp (EVar _ ). "; printSub s end)
  | Dot (Exp (AVar _), s) -> (begin print "Exp (AVar _ ). "; printSub s end)
| Dot (Exp (EClo (AVar _, _)), s) ->
    (begin print "Exp (AVar _ ). "; printSub s end)
| Dot (Exp (EClo (_, _)), s) ->
    (begin print "Exp (EClo _ ). "; printSub s end)
| Dot (Exp _, s) -> (begin print "Exp (_ ). "; printSub s end)
| Dot (IntSyn.Undef, s) -> (begin print "Undef . "; printSub s end) end
let rec ctxToEVarSub =
  begin function
  | (Gglobal, I.Null, s) -> s
  | (Gglobal, Decl (g_, Dec (_, a_)), s) ->
      let s' = ctxToEVarSub (Gglobal, g_, s) in
      let x_ = I.newEVar (Gglobal, (I.EClo (a_, s'))) in
      I.Dot ((I.Exp x_), s')
  | (Gglobal, Decl (g_, ADec (_, d)), s) ->
      let x_ = I.newAVar () in
      I.Dot
        ((I.Exp (I.EClo (x_, (I.Shift (- d))))),
          (ctxToEVarSub (Gglobal, g_, s))) end
let rec solve' =
  begin function
  | ((Atom p, s), (DProg (g_, dpool) as dp), sc) ->
      matchAtom ((p, s), dp, sc)
  | ((Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
      let d'_ = I.Dec (None, (I.EClo (a_, s))) in
      solve'
        ((g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
          sc)
  | ((All (d_, g), s), DProg (g_, dPool), sc) ->
      let d'_ = Names.decLUName (g_, (I.decSub (d_, s))) in
      solve'
        ((g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))), sc) end
let rec rSolve =
  begin function
  | (ps', (Eq (q_), s), DProg (g_, dPool), sc) ->
      ((if Unify.unifiable (g_, ps', (q_, s)) then begin sc [] end
      else begin () end)
  (* effect: instantiate EVars *)(* call success continuation *))
  | (ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), sc) ->
      (begin match Assign.assignable (g_, ps', (q_, s)) with
       | Some cnstr ->
           aSolve ((eqns, s), dp, cnstr, (begin function | () -> sc [] end))
      | None -> () end)
| (ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | skel1 ->
               solve'
                 ((g, s), dp,
                   (begin function | skel2 -> sc (skel1 @ skel2) end)) end)))
(* is this EVar redundant? -fp *))
| (ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve (ps', (r, (I.Dot ((I.Exp x_), s))), dp, sc)
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
      ((if Assign.solveCnstr cnstr then begin sc () end else begin () end)
  (* Fail *))
  | ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), cnstr, sc)
      ->
      let G'' = compose' (g'_, g_) in
      let s' = shift (g'_, s) in
      ((if Assign.unifiable (G'', (n_, s'), (e1, s'))
        then begin aSolve ((eqns, s), dp, cnstr, sc) end else begin () end)
      (* Fail *)) end
let rec sSolve =
  begin function
  | ((C.True, s), dp, sc) -> sc []
  | ((Conjunct (g, a_, Sgoals), s), (DProg (g_, dPool) as dp), sc) ->
      solve'
        ((g, s), dp,
          (begin function
           | skel1 ->
               sSolve
                 ((Sgoals, s), dp,
                   (begin function | skel2 -> sc (skel1 @ skel2) end)) end)) end
let rec matchSig (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc)
  =
  let rec mSig =
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
        mSig sgn' end))
    (* trail to undo EVar instantiations *)) end(* return on failure *) in
mSig (Index.lookup (cidFromHead Ha))
let rec matchIndexSig
  (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  SubTree.matchSig
    ((cidFromHead Ha), g_, ps',
      (begin function
       | ((ConjGoals, s), clauseName) ->
           sSolve
             ((ConjGoals, s), dp,
               (begin function | s_ -> sc ((C.Pc clauseName) :: s_) end)) end))
let rec matchAtom
  (((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  let rec matchDProg =
    begin function
    | (I.Null, _) -> (!) mSig (ps', dp, sc)
    | (Decl (dPool', Dec (r, s, Ha')), k) ->
        if eqHead (Ha, Ha')
        then
          begin (begin ((CSManager.trail
                           (begin function
                            | () ->
                                rSolve
                                  (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                    (begin function
                                     | s_ -> sc ((C.Dc k) :: s_) end)) end))
        (* trail to undo EVar instantiations *));
        matchDProg (dPool', (k + 1)) end) end
    else begin matchDProg (dPool', (k + 1)) end
| (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1)) end
(* dynamic program exhausted, try signature
               there is a choice depending on how we compiled signature
             *) in
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
| _ -> matchDProg (dPool, 1) end)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
let rec solve args =
  begin match !CompSyn.optimize with
  | CompSyn.No -> (begin mSig := matchSig; solve' args end)
  | CompSyn.LinearHeads -> (begin mSig := matchSig; solve' args end)
  | CompSyn.Indexing -> (begin mSig := matchIndexSig; solve' args end) end
end
