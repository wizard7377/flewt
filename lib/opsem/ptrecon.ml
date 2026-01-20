
module type PTRECON  =
  sig
    exception Error of string 
    val solve :
      CompSyn.pskeleton ->
        (CompSyn.__Goal * IntSyn.__Sub) ->
          CompSyn.__DProg ->
            (CompSyn.pskeleton -> IntSyn.__Exp -> unit) -> unit
  end;;




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
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec compose' __2__ __3__ =
      match (__2__, __3__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose' (__G, __G')), __D)
    let rec shift __4__ __5__ =
      match (__4__, __5__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec solve' __6__ __7__ __8__ __9__ =
      match (__6__, __7__, __8__, __9__) with
      | (__O, (Atom p, s), (DProg (__G, dPool) as dp), sc) ->
          matchAtom (__O, (p, s), dp, sc)
      | (__O, (Impl (r, __A, Ha, g), s), DProg (__G, dPool), sc) ->
          let __D' = I.Dec (NONE, (I.EClo (__A, s))) in
          ((if !TableParam.strengthen
            then
              (match MT.memberCtx ((__G, (I.EClo (__A, s))), __G) with
               | Some (__D) ->
                   let __X = I.newEVar (__G, (I.EClo (__A, s))) in
                   ((solve'
                       (__O, (g, (I.Dot ((I.Exp __X), s))),
                         (C.DProg (__G, dPool)),
                         (fun (__O) ->
                            fun (__M) -> sc (__O, (I.Lam (__D', __M))))))
                     (* need to reuse label for this assumption .... *))
               | NONE ->
                   solve'
                     (__O, (g, (I.dot1 s)),
                       (C.DProg
                          ((I.Decl (__G, __D')),
                            (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                       (fun (__O) ->
                          fun (__M) -> sc (__O, (I.Lam (__D', __M))))))
            else
              solve'
                (__O, (g, (I.dot1 s)),
                  (C.DProg
                     ((I.Decl (__G, __D')),
                       (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                  (fun (__O) -> fun (__M) -> sc (__O, (I.Lam (__D', __M))))))
            (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*))
      | (__O, (All (__D, g), s), DProg (__G, dPool), sc) ->
          let __D' = Names.decLUName (__G, (I.decSub (__D, s))) in
          ((solve'
              (__O, (g, (I.dot1 s)),
                (C.DProg
                   ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
                (fun (__O) -> fun (__M) -> sc (__O, (I.Lam (__D', __M))))))
            (* val D' = I.decSub (D, s) *))
    let rec rSolve __10__ __11__ __12__ __13__ __14__ =
      match (__10__, __11__, __12__, __13__, __14__) with
      | (__O, ps', (Eq (__Q), s), DProg (__G, dPool), sc) ->
          ((if Unify.unifiable (__G, (__Q, s), ps')
            then sc (__O, I.Nil)
            else
              (let _ =
                 print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
                 print ((Print.expToString (__G, (I.EClo ps'))) ^ " unify ");
                 print ((Print.expToString (__G, (I.EClo (__Q, s)))) ^ "\n") in
               ()))
          (* effect: instantiate EVars *)(* call success continuation *))
      | (__O, ps', (Assign (__Q, eqns), s), (DProg (__G, dPool) as dp), sc)
          ->
          (match Assign.assignable (__G, ps', (__Q, s)) with
           | Some cnstr ->
               if aSolve ((eqns, s), dp, cnstr)
               then sc (__O, I.Nil)
               else
                 print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
           | NONE ->
               print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n")
      | (__O, ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (__O, ps', (r, (I.Dot ((I.Exp __X), s))), dp,
                (fun (__O) ->
                   fun (__S) ->
                     solve'
                       (__O, (g, s), dp,
                         (fun (__O) ->
                            fun (__M) -> sc (__O, (I.App (__M, __S))))))))
            (* is this EVar redundant? -fp *))
      | (__O, ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp),
         sc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (__O, ps', (r, (I.Dot ((I.Exp __X), s))), dp,
              (fun (__O) -> fun (__S) -> sc (__O, (I.App (__X, __S)))))
      | (__O, ps', (Axists (ADec (Some (__X), d), r), s),
         (DProg (__G, dPool) as dp), sc) ->
          let __X' = I.newAVar () in
          ((rSolve
              (__O, ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s))),
                dp, sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | ((C.Trivial, s), dp, cnstr) -> Assign.solveCnstr cnstr
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         cnstr) ->
          let G'' = compose' (__G', __G) in
          let s' = shift (__G', s) in
          (Assign.unifiable (G'', (__N, s'), (e1, s'))) &&
            (aSolve ((eqns, s), dp, cnstr))
    let rec matchAtom ((Ho)::__O) ((Root (Ha, __S), s) as ps')
      (DProg (__G, dPool) as dp) sc =
      let rec matchSig __18__ __19__ =
        match (__18__, __19__) with
        | (nil, k) -> raise (Error " \noracle #Pc does not exist \n")
        | ((Const c as Hc)::sgn', k) ->
            if c = k
            then
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              rSolve
                (__O, ps', (r, I.id), dp,
                  (fun (__O) -> fun (__S) -> sc (__O, (I.Root (Hc, __S)))))
            else matchSig (sgn', k)
        | ((Def d as Hc)::sgn', k) ->
            if d = k
            then
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              rSolve
                (__O, ps', (r, I.id), dp,
                  (fun (__O) -> fun (__S) -> sc (__O, (I.Root (Hc, __S)))))
            else matchSig (sgn', k)(* should not happen *) in
      let rec matchDProg __20__ __21__ __22__ =
        match (__20__, __21__, __22__) with
        | (I.Null, i, k) ->
            raise
              (Error
                 "\n selected dynamic clause number does not exist in current dynamic clause pool!\n")
        | (Decl (dPool', Dec (r, s, Ha')), 1, k) ->
            ((if eqHead (Ha, Ha')
              then
                rSolve
                  (__O, ps', (r, (I.comp (s, (I.Shift k)))), dp,
                    (fun (__O) ->
                       fun (__S) -> sc (__O, (I.Root ((I.BVar k), __S)))))
              else
                raise
                  (Error
                     "\n selected dynamic clause does not match current goal!\n"))
            (* shouldn't happen *))
        | (Decl (dPool', dc), i, k) -> matchDProg (dPool', (i - 1), k)
        (* dynamic program exhausted -- shouldn't happen *) in
      ((match Ho with
        | Pc i -> matchSig ((Index.lookup (cidFromHead Ha)), i)
        | Dc i -> matchDProg (dPool, i, i)
        | Csolver (__U) -> sc (__O, __U))
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    let rec solve (__O) (g, s) (DProg (__G, dPool) as dp) sc =
      try solve' (__O, (g, s), dp, sc) with | Error msg -> print msg
  end ;;
