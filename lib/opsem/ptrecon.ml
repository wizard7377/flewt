module type PTRECON  =
  sig
    exception Error of string 
    val solve :
      (CompSyn.pskeleton * (CompSyn.goal_ * IntSyn.sub_) * CompSyn.dProg_ *
        ((CompSyn.pskeleton * IntSyn.exp_) -> unit)) -> unit
  end


module PtRecon(PtRecon:sig
                         module Unify : UNIFY
                         module Assign : ASSIGN
                         module MemoTable : MEMOTABLE
                         module Index : INDEX
                         module CPrint : CPRINT
                         module Names : NAMES
                       end) : PTRECON =
  struct
    module I = IntSyn
    module C = CompSyn
    module MT = MemoTable
    exception Error of string 
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
let rec solve' =
  begin function
  | (o_, (Atom p, s), (DProg (g_, dPool) as dp), sc) ->
      matchAtom (o_, (p, s), dp, sc)
  | (o_, (Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
      let d'_ = I.Dec (None, (I.EClo (a_, s))) in
      ((if !TableParam.strengthen
        then
          begin (begin match MT.memberCtx ((g_, (I.EClo (a_, s))), g_) with
                 | Some (d_) ->
                     let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
                     ((solve'
                         (o_, (g, (I.Dot ((I.Exp x_), s))),
                           (C.DProg (g_, dPool)),
                           (begin function
                            | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))) end)))
                     (* need to reuse label for this assumption .... *))
          | None ->
              solve'
                (o_, (g, (I.dot1 s)),
                  (C.DProg
                     ((I.Decl (g_, d'_)),
                       (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                  (begin function | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))) end)) end) end
  else begin
    solve'
      (o_, (g, (I.dot1 s)),
        (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
        (begin function | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))) end)) end)
(*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*))
| (o_, (All (d_, g), s), DProg (g_, dPool), sc) ->
    let d'_ = Names.decLUName (g_, (I.decSub (d_, s))) in
    ((solve'
        (o_, (g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
          (begin function | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))) end)))
    (* val D' = I.decSub (D, s) *)) end
let rec rSolve =
  begin function
  | (o_, ps', (Eq (q_), s), DProg (g_, dPool), sc) ->
      ((if Unify.unifiable (g_, (q_, s), ps') then begin sc (o_, I.Nil) end
      else begin
        (let _ =
           begin print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
           print ((Print.expToString (g_, (I.EClo ps'))) ^ " unify ");
           print ((Print.expToString (g_, (I.EClo (q_, s)))) ^ "\n") end in
      ()) end)
  (* effect: instantiate EVars *)(* call success continuation *))
| (o_, ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), sc) ->
    (begin match Assign.assignable (g_, ps', (q_, s)) with
     | Some cnstr ->
         if aSolve ((eqns, s), dp, cnstr) then begin sc (o_, I.Nil) end
         else begin
           print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n" end
| None -> print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n" end)
| (o_, ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (o_, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | (o_, s_) ->
               solve'
                 (o_, (g, s), dp,
                   (begin function | (o_, m_) -> sc (o_, (I.App (m_, s_))) end)) end)))
(* is this EVar redundant? -fp *))
| (o_, ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (o_, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
        (begin function | (o_, s_) -> sc (o_, (I.App (x_, s_))) end))
| (o_, ps', (Axists (ADec (Some (x_), d), r), s), (DProg (g_, dPool) as dp),
   sc) ->
    let x'_ = I.newAVar () in
    ((rSolve
        (o_, ps', (r, (I.Dot ((I.Exp (I.EClo (x'_, (I.Shift (- d))))), s))),
          dp, sc))
      (* we don't increase the proof term here! *)) end
(* fail *)
let rec aSolve =
  begin function
  | ((C.Trivial, s), dp, cnstr) -> Assign.solveCnstr cnstr
  | ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), cnstr) ->
      let G'' = compose' (g'_, g_) in
      let s' = shift (g'_, s) in
      (Assign.unifiable (G'', (n_, s'), (e1, s'))) &&
        (aSolve ((eqns, s), dp, cnstr)) end
let rec matchAtom
  ((Ho)::o_, ((Root (Ha, s_), s) as ps'), (DProg (g_, dPool) as dp), sc) =
  let rec matchSig =
    begin function
    | ([], k) -> raise (Error " \noracle #Pc does not exist \n")
    | ((Const c as Hc)::sgn', k) ->
        if c = k
        then
          begin let SClause r = C.sProgLookup (cidFromHead Hc) in
                rSolve
                  (o_, ps', (r, I.id), dp,
                    (begin function | (o_, s_) -> sc (o_, (I.Root (Hc, s_))) end)) end
    else begin matchSig (sgn', k) end
  | ((Def d as Hc)::sgn', k) ->
      if d = k
      then
        begin let SClause r = C.sProgLookup (cidFromHead Hc) in
              rSolve
                (o_, ps', (r, I.id), dp,
                  (begin function | (o_, s_) -> sc (o_, (I.Root (Hc, s_))) end)) end
  else begin matchSig (sgn', k) end end(* should not happen *) in
let rec matchDProg =
begin function
| (I.Null, i, k) ->
    raise
      (Error
         "\n selected dynamic clause number does not exist in current dynamic clause pool!\n")
| (Decl (dPool', Dec (r, s, Ha')), 1, k) ->
    ((if eqHead (Ha, Ha')
      then
        begin rSolve
                (o_, ps', (r, (I.comp (s, (I.Shift k)))), dp,
                  (begin function
                   | (o_, s_) -> sc (o_, (I.Root ((I.BVar k), s_))) end)) end
else begin
  raise (Error "\n selected dynamic clause does not match current goal!\n") end)
(* shouldn't happen *))
| (Decl (dPool', dc), i, k) -> matchDProg (dPool', (i - 1), k) end(* dynamic program exhausted -- shouldn't happen *) in
((begin match Ho with
| Pc i -> matchSig ((Index.lookup (cidFromHead Ha)), i)
| Dc i -> matchDProg (dPool, i, i)
| Csolver (u_) -> sc (o_, u_) end)
(* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
let rec solve (o_, (g, s), (DProg (g_, dPool) as dp), sc) =
  begin try solve' (o_, (g, s), dp, sc) with | Error msg -> print msg end end
