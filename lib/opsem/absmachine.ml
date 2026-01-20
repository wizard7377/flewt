
module type ABSMACHINE  =
  sig
    val solve :
      (CompSyn.__Goal * IntSyn.__Sub) ->
        CompSyn.__DProg -> (IntSyn.__Exp -> unit) -> unit
  end;;




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
    let rec raiseType __6__ __7__ =
      match (__6__, __7__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec solve __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | ((Atom p, s), (DProg (__G, dPool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, __A, Ha, g), s), DProg (__G, dPool), sc) ->
          let __D' = I.Dec (None, (I.EClo (__A, s))) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__G, __D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (fun (__M) -> sc (I.Lam (__D', __M))))
      | ((All (__D, g), s), DProg (__G, dPool), sc) ->
          let __D' = Names.decLUName (__G, (I.decSub (__D, s))) in
          ((solve
              ((g, (I.dot1 s)),
                (C.DProg
                   ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
                (fun (__M) -> sc (I.Lam (__D', __M)))))
            (*      val D' = I.decSub (D, s) *))
    let rec rSolve __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (ps', (Eq (__Q), s), DProg (__G, dPool), sc) ->
          ((if Unify.unifiable (__G, (__Q, s), ps') then sc I.Nil else ())
          (* effect: instantiate EVars *)(* call success continuation *))
      | (ps', (Assign (__Q, eqns), s), (DProg (__G, dPool) as dp), sc) ->
          (match Assign.assignable (__G, ps', (__Q, s)) with
           | Some cnstr ->
               aSolve ((eqns, s), dp, cnstr, (fun () -> sc I.Nil))
           | None -> ())
      | (ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
                (fun (__S) ->
                   solve ((g, s), dp, (fun (__M) -> sc (I.App (__M, __S)))))))
            (* is this EVar redundant? -fp *)(* same effect as s^-1 *))
      | (ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp), sc)
          ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
              (fun (__S) -> sc (I.App (__X, __S))))
      | (ps', (Axists (ADec (_, d), r), s), (DProg (__G, dPool) as dp), sc)
          ->
          let __X' = I.newAVar () in
          ((rSolve
              (ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve __15__ __16__ __17__ __18__ =
      match (__15__, __16__, __17__, __18__) with
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc () else ()
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         cnstr, sc) ->
          let G'' = compose (__G, __G') in
          let s' = shiftSub (__G', s) in
          if Assign.unifiable (G'', (__N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom ((Root (Ha, __S), s) as ps') (DProg (__G, dPool) as dp)
      sc =
      let deterministic = C.detTableCheck (cidFromHead Ha) in
      let exception SucceedOnce of I.__Spine  in
        let rec matchSig =
          function
          | nil -> ()
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (((CSManager.trail
                   (fun () ->
                      rSolve
                        (ps', (r, I.id), dp,
                          (fun (__S) -> sc (I.Root (Hc, __S)))));
                 matchSig sgn'))
                (* trail to undo EVar instantiations *))
          (* return unit on failure *) in
        let rec matchSigDet =
          function
          | nil -> ()
          | (Hc)::sgn' ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              (((try
                   CSManager.trail
                     (fun () ->
                        rSolve
                          (ps', (r, I.id), dp,
                            (fun (__S) -> raise (SucceedOnce __S))));
                   matchSigDet sgn'
                 with | SucceedOnce (__S) -> sc (I.Root (Hc, __S))))
                (* trail to undo EVar instantiations *))
          (* return unit on failure *) in
        let rec matchDProg __19__ __20__ =
          match (__19__, __20__) with
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
                       ((CSManager.trail
                           (fun () ->
                              rSolve
                                (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                  (fun (__S) -> raise (SucceedOnce __S)))))
                       (* trail to undo EVar instantiations *));
                       matchDProg (dPool', (k + 1))
                     with
                     | SucceedOnce (__S) -> sc (I.Root ((I.BVar k), __S))
                   else
                     (((CSManager.trail
                          (fun () ->
                             rSolve
                               (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                                 (fun (__S) -> sc (I.Root ((I.BVar k), __S))))))
                      (* trail to undo EVar instantiations *));
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
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
          (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    let solve = solve
  end ;;
