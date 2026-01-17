
module type EXTQUERY  =
  sig
    module ExtSyn : EXTSYN
    type nonrec query
    val query : (string option * ExtSyn.term) -> query
    type nonrec define
    val define : (string option * ExtSyn.term * ExtSyn.term option) -> define
    type nonrec solve
    val solve : (string option * ExtSyn.term * Paths.region) -> solve
  end
module type RECON_QUERY  =
  sig
    include
      ((EXTQUERY)(* External Syntax for queries *)(* Author: Frank Pfenning *)
      (*! structure Paths : PATHS !*)(* query *)
      (* ucid : tm | tm *)(* id : tm | _ : tm *)
      (* signature EXTQUERY *)(*! structure IntSyn : INTSYN !*))
    exception Error of string 
    val queryToQuery :
      (query * Paths.location) ->
        (IntSyn.__Exp * string option * (IntSyn.__Exp * string) list)
    val solveToSolve :
      (define list * solve * Paths.location) ->
        (((IntSyn.__Exp)(* Yi the EVars in the query and "Yi" their names *)
          (* where A is query type, X the optional proof term variable name *)
          (* (A, SOME("X"), [(Y1, "Y1"),...] *)) *
          (IntSyn.__Exp -> (IntSyn.__ConDec * Paths.occConDec option) list))
  end;;




module ReconQuery(ReconQuery:sig
                               module Global : GLOBAL
                               module Names : NAMES
                               module Abstract : ABSTRACT
                               module ReconTerm' : RECON_TERM
                               module TypeCheck : TYPECHECK
                               module Strict : STRICT
                               module Timers : TIMERS
                               module Print :
                               ((PRINT)(* Reconstruct queries *)
                               (* Author: Frank Pfenning *)
                               (* Modified: Roberto Virga, Jeff Polakow *)
                               (*! structure IntSyn' : INTSYN !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn' !*)
                               (*! structure Paths' : PATHS !*)(*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                               (*! sharing ReconTerm'.Paths = Paths' !*)
                               (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                               (*! sharing Strict.IntSyn = IntSyn' !*)
                               (*! sharing Strict.Paths = Paths' !*))
                             end) : RECON_QUERY =
  struct
    module ExtSyn =
      ((ReconTerm')(*! sharing Print.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure Paths = Paths' !*))
    module T = ReconTerm'
    exception Error of string 
    let rec error
      (((r)(* error (r, msg) raises a syntax error within region r with text msg *)),
       msg)
      = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    type query =
      | query of
      (((name)(* Queries, with optional proof term variable *))
      option * T.term) [@sml.renamed "query"][@sml.renamed "query"]
    type define =
      | define of
      (((string)(* define := <constant name> option * <def body> * <type> option *))
      option * T.term * T.term option)
      [@sml.renamed "define"][@sml.renamed "define"]
    type solve =
      | solve of (string option * T.term * Paths.region)
      [@sml.renamed "solve"][@sml.renamed "solve"]
    let rec freeVar =
      function
      | (SOME
         ((name)(* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)),
         Xs) -> List.exists (function | (_, name') -> name = name') Xs
      | _ -> false__
    let rec queryToQuery
      (query
       (((optName)(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
        (* call TypeCheck... if !doubleCheck = true? *)
        (* Wed May 20 08:00:28 1998 -fp *)), tm),
       Loc (fileName, r))
      =
      let ((_)(* construct an external term for the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *))
        = Names.varReset IntSyn.Null in
      let _ = T.resetErrors fileName in
      let JClass ((V, oc), L) =
        Timers.time Timers.recon T.reconQuery (T.jclass tm) in
      let _ = T.checkErrors r in
      let _ =
        match L with
        | IntSyn.Type -> ()
        | _ -> error (r, "Query was not a type") in
      let Xs = Names.namedEVars () in
      let ((_)(* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *))
        =
        if freeVar (optName, Xs)
        then
          error
            (r,
              (((^) "Proof term variable " valOf optName) ^ " occurs in type"))
        else () in
      (V, optName, Xs)
    let rec finishDefine
      (define (optName, tm, clsOpt), ((U, oc1), (V, oc2Opt), L)) =
      let (i, (U', V')) =
        try Timers.time Timers.abstract Abstract.abstractDef (U, V)
        with
        | Error msg ->
            raise (Abstract.Error (Paths.wrap ((Paths.toRegion oc1), msg))) in
      let name = match optName with | NONE -> "_" | SOME name -> name in
      let ocd = Paths.def (i, oc1, oc2Opt) in
      let cd =
        try
          Strict.check ((U', V'), (SOME ocd));
          IntSyn.ConDef (name, NONE, i, U', V', L, (IntSyn.ancestor U'))
        with | Error _ -> IntSyn.AbbrevDef (name, NONE, i, U', V', L) in
      let ((cd)(* is this necessary? -kw *)) =
        Names.nameConDec cd in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n")
        else () in
      let _ =
        if !Global.doubleCheck
        then
          (Timers.time Timers.checking TypeCheck.check (V', (IntSyn.Uni L));
           Timers.time Timers.checking TypeCheck.check (U', V'))
        else () in
      let conDecOpt = match optName with | NONE -> NONE | SOME _ -> SOME cd in
      (conDecOpt, (SOME ocd))
    let rec finishSolve (solve (nameOpt, tm, r), U, V) =
      let (i, (U', V')) =
        try Timers.time Timers.abstract Abstract.abstractDef (U, V)
        with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
      let name = match nameOpt with | NONE -> "_" | SOME name -> name in
      let cd =
        try
          Strict.check ((U', V'), NONE);
          IntSyn.ConDef
            (name, NONE, i, U', V', IntSyn.Type, (IntSyn.ancestor U'))
        with
        | Error _ -> IntSyn.AbbrevDef (name, NONE, i, U', V', IntSyn.Type) in
      let ((cd)(* is this necessary? -kw *)) =
        Names.nameConDec cd in
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
             (V', (IntSyn.Uni IntSyn.Type));
           Timers.time Timers.checking TypeCheck.check (U', V'))
        else () in
      let conDecOpt = match nameOpt with | NONE -> NONE | SOME _ -> SOME cd in
      conDecOpt
    let rec solveToSolve
      (((defines)(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
       (* call TypeCheck... if !doubleCheck = true? *)
       (* Wed May 20 08:00:28 1998 -fp *)),
       (solve (optName, tm, r0) as sol), Loc (fileName, r))
      =
      let _ = Names.varReset IntSyn.Null in
      let _ = T.resetErrors fileName in
      let mkd =
        function
        | define (_, tm1, NONE) -> T.jterm tm1
        | define (_, tm1, SOME tm2) -> T.jof (tm1, tm2) in
      let mkj =
        function
        | nil -> T.jnothing
        | def::defs -> T.jand ((mkd def), (mkj defs)) in
      let JAnd (defines', JClass ((V, _), L)) =
        Timers.time Timers.recon T.reconQuery
          (T.jand ((mkj defines), (T.jclass tm))) in
      let _ = T.checkErrors r in
      let _ =
        match L with
        | IntSyn.Type -> ()
        | _ -> error (r0, "Query was not a type") in
      let sc =
        function
        | (((M)(* val Xs = Names.namedEVars () *)), nil, _)
            ->
            (match finishSolve (sol, M, V) with
             | NONE -> nil
             | SOME condec -> [(condec, NONE)])
        | (M, def::defs, JAnd (JTerm ((U, oc1), V, L), f)) ->
            (match finishDefine (def, ((U, oc1), (V, NONE), L)) with
             | (NONE, _) -> sc (M, defs, f)
             | (SOME condec, ocdOpt) -> (::) (condec, ocdOpt) sc (M, defs, f))
        | (M, def::defs, JAnd (JOf ((U, oc1), (V, oc2), L), f)) ->
            (match finishDefine (def, ((U, oc1), (V, (SOME oc2)), L)) with
             | (NONE, _) -> sc (M, defs, f)
             | (SOME condec, ocdOpt) -> (::) (condec, ocdOpt) sc (M, defs, f)) in
      (V, (function | M -> sc (M, defines, defines')))
  end ;;
