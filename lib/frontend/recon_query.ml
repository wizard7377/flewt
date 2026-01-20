
module type EXTQUERY  =
  sig
    module ExtSyn : EXTSYN
    type nonrec query
    val query : string option -> ExtSyn.term -> query
    type nonrec define
    val define : string option -> ExtSyn.term -> ExtSyn.term option -> define
    type nonrec solve
    val solve : string option -> ExtSyn.term -> Paths.region -> solve
  end
module type RECON_QUERY  =
  sig
    include EXTQUERY
    exception Error of string 
    val queryToQuery :
      query ->
        Paths.location ->
          (IntSyn.__Exp * string option * (IntSyn.__Exp * string) list)
    val solveToSolve :
      define list ->
        solve ->
          Paths.location ->
            (IntSyn.__Exp *
              (IntSyn.__Exp ->
                 (IntSyn.__ConDec * Paths.occConDec option) list))
  end;;




module ReconQuery(ReconQuery:sig
                               module Global : GLOBAL
                               module Names : NAMES
                               module Abstract : ABSTRACT
                               module ReconTerm' : RECON_TERM
                               module TypeCheck : TYPECHECK
                               module Strict : STRICT
                               module Timers : TIMERS
                               module Print : PRINT
                             end) : RECON_QUERY =
  struct
    module ExtSyn = ReconTerm'
    module T = ReconTerm'
    exception Error of string 
    let rec error r msg = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    type query =
      | query of (name option * T.term)
      [@sml.renamed "query"][@sml.renamed "query"]
    type define =
      | define of (string option * T.term * T.term option)
      [@sml.renamed "define"][@sml.renamed "define"]
    type solve =
      | solve of (string option * T.term * Paths.region)
      [@sml.renamed "solve"][@sml.renamed "solve"]
    let rec freeVar __0__ __1__ =
      match (__0__, __1__) with
      | (Some name, __Xs) ->
          List.exists (fun _ -> fun name' -> name = name') __Xs
      | _ -> false
    let rec queryToQuery (query (optName, tm)) (Loc (fileName, r)) =
      let _ = Names.varReset IntSyn.Null in
      let _ = T.resetErrors fileName in
      let JClass ((__V, oc), __L) =
        Timers.time Timers.recon T.reconQuery (T.jclass tm) in
      let _ = T.checkErrors r in
      let _ =
        match __L with
        | IntSyn.Type -> ()
        | _ -> error (r, "Query was not a type") in
      let __Xs = Names.namedEVars () in
      let _ =
        if freeVar (optName, __Xs)
        then
          error
            (r,
              (((^) "Proof term variable " valOf optName) ^ " occurs in type"))
        else () in
      (((__V, optName, __Xs))
        (* construct an external term for the result of the query
        val res = (case optName
                     of None => T.omitted (r)
                      | Some name => T.evar (name, r)) *)
        (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *))
    let rec finishDefine (define (optName, tm, clsOpt))
      ((__U, oc1), (__V, oc2Opt), __L) =
      let (i, (__U', __V')) =
        try Timers.time Timers.abstract Abstract.abstractDef (__U, __V)
        with
        | Error msg ->
            raise (Abstract.Error (Paths.wrap ((Paths.toRegion oc1), msg))) in
      let name = match optName with | None -> "_" | Some name -> name in
      let ocd = Paths.def (i, oc1, oc2Opt) in
      let cd =
        try
          Strict.check ((__U', __V'), (Some ocd));
          IntSyn.ConDef
            (name, None, i, __U', __V', __L, (IntSyn.ancestor __U'))
        with | Error _ -> IntSyn.AbbrevDef (name, None, i, __U', __V', __L) in
      let cd = Names.nameConDec cd in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n")
        else () in
      let _ =
        if !Global.doubleCheck
        then
          (Timers.time Timers.checking TypeCheck.check
             (__V', (IntSyn.Uni __L));
           Timers.time Timers.checking TypeCheck.check (__U', __V'))
        else () in
      let conDecOpt = match optName with | None -> None | Some _ -> Some cd in
      (((conDecOpt, (Some ocd)))
        (* is this necessary? -kw *))
    let rec finishSolve (solve (nameOpt, tm, r)) (__U) (__V) =
      let (i, (__U', __V')) =
        try Timers.time Timers.abstract Abstract.abstractDef (__U, __V)
        with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
      let name = match nameOpt with | None -> "_" | Some name -> name in
      let cd =
        try
          Strict.check ((__U', __V'), None);
          IntSyn.ConDef
            (name, None, i, __U', __V', IntSyn.Type, (IntSyn.ancestor __U'))
        with
        | Error _ ->
            IntSyn.AbbrevDef (name, None, i, __U', __V', IntSyn.Type) in
      let cd = Names.nameConDec cd in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n")
        else () in
      let _ =
        if !Global.doubleCheck
        then
          (Timers.time Timers.checking TypeCheck.check
             (__V', (IntSyn.Uni IntSyn.Type));
           Timers.time Timers.checking TypeCheck.check (__U', __V'))
        else () in
      let conDecOpt = match nameOpt with | None -> None | Some _ -> Some cd in
      ((conDecOpt)(* is this necessary? -kw *))
    let rec solveToSolve defines (solve (optName, tm, r0) as sol) (Loc
      (fileName, r)) =
      let _ = Names.varReset IntSyn.Null in
      let _ = T.resetErrors fileName in
      let rec mkd =
        function
        | define (_, tm1, None) -> T.jterm tm1
        | define (_, tm1, Some tm2) -> T.jof (tm1, tm2) in
      let rec mkj =
        function
        | nil -> T.jnothing
        | def::defs -> T.jand ((mkd def), (mkj defs)) in
      let JAnd (defines', JClass ((__V, _), __L)) =
        Timers.time Timers.recon T.reconQuery
          (T.jand ((mkj defines), (T.jclass tm))) in
      let _ = T.checkErrors r in
      let _ =
        match __L with
        | IntSyn.Type -> ()
        | _ -> error (r0, "Query was not a type") in
      let rec sc __2__ __3__ __4__ =
        match (__2__, __3__, __4__) with
        | (__M, nil, _) ->
            (match finishSolve (sol, __M, __V) with
             | None -> nil
             | Some condec -> [(condec, None)])
        | (__M, def::defs, JAnd (JTerm ((__U, oc1), __V, __L), f)) ->
            (match finishDefine (def, ((__U, oc1), (__V, None), __L)) with
             | (None, _) -> sc (__M, defs, f)
             | (Some condec, ocdOpt) ->
                 (::) (condec, ocdOpt) sc (__M, defs, f))
        | (__M, def::defs, JAnd (JOf ((__U, oc1), (__V, oc2), __L), f)) ->
            (match finishDefine (def, ((__U, oc1), (__V, (Some oc2)), __L))
             with
             | (None, _) -> sc (__M, defs, f)
             | (Some condec, ocdOpt) ->
                 (::) (condec, ocdOpt) sc (__M, defs, f)) in
      (((__V, (fun (__M) -> sc (__M, defines, defines'))))
        (* val Xs = Names.namedEVars () *))
  end ;;
