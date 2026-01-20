
module type ABSMACHINESBT  =
  sig
    val solve :
      (CompSyn.__Goal * IntSyn.__Sub) ->
        CompSyn.__DProg -> (CompSyn.__Flatterm list -> unit) -> unit
  end;;




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
      ((IntSyn.__Exp * IntSyn.__Sub) ->
         CompSyn.__DProg -> (CompSyn.__Flatterm list -> unit) -> unit)
        ref)
      = ref (fun ps -> fun dp -> fun sc -> ())
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false
    let rec compose' __2__ __3__ =
      match (__2__, __3__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose' (__G, __G')), __D)
    let rec shift __4__ __5__ =
      match (__4__, __5__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec invShiftN n s =
      if n = 0
      then I.comp (I.invShift, s)
      else I.comp (I.invShift, (invShiftN ((n - 1), s)))
    let rec raiseType __6__ __7__ =
      match (__6__, __7__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec printSub =
      function
      | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
      | Dot (Idx n, s) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub s)
      | Dot (Exp (EVar (_, _, _, _)), s) ->
          (print "Exp (EVar _ ). "; printSub s)
      | Dot (Exp (AVar _), s) -> (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (AVar _, _)), s) ->
          (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (_, _)), s) -> (print "Exp (EClo _ ). "; printSub s)
      | Dot (Exp _, s) -> (print "Exp (_ ). "; printSub s)
      | Dot (IntSyn.Undef, s) -> (print "Undef . "; printSub s)
    let rec ctxToEVarSub __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (Gglobal, I.Null, s) -> s
      | (Gglobal, Decl (__G, Dec (_, __A)), s) ->
          let s' = ctxToEVarSub (Gglobal, __G, s) in
          let __X = I.newEVar (Gglobal, (I.EClo (__A, s'))) in
          I.Dot ((I.Exp __X), s')
      | (Gglobal, Decl (__G, ADec (_, d)), s) ->
          let __X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (__X, (I.Shift (~ d))))),
              (ctxToEVarSub (Gglobal, __G, s)))
    let rec solve' __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | ((Atom p, s), (DProg (__G, dpool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, __A, Ha, g), s), DProg (__G, dPool), sc) ->
          let __D' = I.Dec (None, (I.EClo (__A, s))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__G, __D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              sc)
      | ((All (__D, g), s), DProg (__G, dPool), sc) ->
          let __D' = Names.decLUName (__G, (I.decSub (__D, s))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              sc)
    let rec rSolve __14__ __15__ __16__ __17__ =
      match (__14__, __15__, __16__, __17__) with
      | (ps', (Eq (__Q), s), DProg (__G, dPool), sc) ->
          ((if Unify.unifiable (__G, ps', (__Q, s)) then sc nil else ())
          (* effect: instantiate EVars *)(* call success continuation *))
      | (ps', (Assign (__Q, eqns), s), (DProg (__G, dPool) as dp), sc) ->
          (match Assign.assignable (__G, ps', (__Q, s)) with
           | Some cnstr -> aSolve ((eqns, s), dp, cnstr, (fun () -> sc nil))
           | None -> ())
      | (ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
                (fun skel1 ->
                   solve' ((g, s), dp, (fun skel2 -> sc (skel1 @ skel2))))))
            (* is this EVar redundant? -fp *))
      | (ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp), sc)
          ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve (ps', (r, (I.Dot ((I.Exp __X), s))), dp, sc)
      | (ps', (Axists (ADec (_, d), r), s), (DProg (__G, dPool) as dp), sc)
          ->
          let __X' = I.newAVar () in
          ((rSolve
              (ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve __18__ __19__ __20__ __21__ =
      match (__18__, __19__, __20__, __21__) with
      | ((C.Trivial, s), dp, cnstr, sc) ->
          ((if Assign.solveCnstr cnstr then sc () else ())
          (* Fail *))
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         cnstr, sc) ->
          let G'' = compose' (__G', __G) in
          let s' = shift (__G', s) in
          ((if Assign.unifiable (G'', (__N, s'), (e1, s'))
            then aSolve ((eqns, s), dp, cnstr, sc)
            else ())(* Fail *))
    let rec sSolve __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | ((C.True, s), dp, sc) -> sc nil
      | ((Conjunct (g, __A, Sgoals), s), (DProg (__G, dPool) as dp), sc) ->
          solve'
            ((g, s), dp,
              (fun skel1 ->
                 sSolve ((Sgoals, s), dp, (fun skel2 -> sc (skel1 @ skel2)))))
    let rec matchSig ((Root (Ha, __S), s) as ps') (DProg (__G, dPool) as dp)
      sc =
      let rec mSig =
        function
        | nil -> ()
        | (Const c as Hc)::sgn' ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            (((CSManager.trail
                 (fun () ->
                    rSolve
                      (ps', (r, I.id), dp,
                        (fun (__S) -> sc ((C.Pc c) :: __S))));
               mSig sgn'))
              (* trail to undo EVar instantiations *))
        (* return on failure *) in
      mSig (Index.lookup (cidFromHead Ha))
    let rec matchIndexSig ((Root (Ha, __S), s) as ps')
      (DProg (__G, dPool) as dp) sc =
      SubTree.matchSig
        ((cidFromHead Ha), __G, ps',
          (fun (ConjGoals, s) ->
             fun clauseName ->
               sSolve
                 ((ConjGoals, s), dp,
                   (fun (__S) -> sc ((C.Pc clauseName) :: __S)))))
    let rec matchAtom ((Root (Ha, __S), s) as ps') (DProg (__G, dPool) as dp)
      sc =
      let rec matchDProg __25__ __26__ =
        match (__25__, __26__) with
        | (I.Null, _) -> (!) mSig (ps', dp, sc)
        | (Decl (dPool', Dec (r, s, Ha')), k) ->
            if eqHead (Ha, Ha')
            then
              (((CSManager.trail
                   (fun () ->
                      rSolve
                        (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                          (fun (__S) -> sc ((C.Dc k) :: __S)))))
               (* trail to undo EVar instantiations *));
               matchDProg (dPool', (k + 1)))
            else matchDProg (dPool', (k + 1))
        | (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1))
        (* dynamic program exhausted, try signature
               there is a choice depending on how we compiled signature
             *) in
      let rec matchConstraint solve try__ =
        let succeeded =
          CSManager.trail
            (fun () ->
               match solve (__G, (I.SClo (__S, s)), try__) with
               | Some (__U) -> (sc [C.Csolver __U]; true)
               | None -> false) in
        if succeeded then matchConstraint (solve, (try__ + 1)) else () in
      ((match I.constStatus (cidFromHead Ha) with
        | Constraint (cs, solve) -> matchConstraint (solve, 0)
        | _ -> matchDProg (dPool, 1))
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    let rec solve args =
      match !CompSyn.optimize with
      | CompSyn.No -> (mSig := matchSig; solve' args)
      | CompSyn.LinearHeads -> (mSig := matchSig; solve' args)
      | CompSyn.Indexing -> (mSig := matchIndexSig; solve' args)
  end ;;
