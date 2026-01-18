
module type EXTQUERY  =
  sig
    module ExtSyn : EXTSYN
    type nonrec query
    val query : (string option * ExtSyn.term) -> query
    type nonrec define
    val define : (string option * ExtSyn.term * ExtSyn.term option) -> define
    type nonrec solve
    val solve : (string option * ExtSyn.term * Paths.region) -> solve
  end (* External Syntax for queries *)
(* Author: Frank Pfenning *)
(*! structure Paths : PATHS !*)
(* query *) (* ucid : tm | tm *)
(* id : tm | _ : tm *)
(* signature EXTQUERY *)
module type RECON_QUERY  =
  sig
    (*! structure IntSyn : INTSYN !*)
    include EXTQUERY
    exception Error of string 
    val queryToQuery :
      (query * Paths.location) ->
        (IntSyn.__Exp * string option * (IntSyn.__Exp * string) list)
    (* (A, Some("x"), [(Y1, "Y1"),...] *)
    (* where A is query type, x the optional proof term variable name *)
    (* Yi the EVars in the query and "Yi" their names *)
    val solveToSolve :
      (define list * solve * Paths.location) ->
        (IntSyn.__Exp *
          (IntSyn.__Exp -> (IntSyn.__ConDec * Paths.occConDec option) list))
  end;;




(* Reconstruct queries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)
module ReconQuery(ReconQuery:sig
                               module Global : GLOBAL
                               module Names : NAMES
                               module Abstract : ABSTRACT
                               module ReconTerm' : RECON_TERM
                               module TypeCheck : TYPECHECK
                               module Strict : STRICT
                               module Timers : TIMERS
                               (*! structure IntSyn' : INTSYN !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn' !*)
                               (*! structure Paths' : PATHS !*)
                               (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                               (*! sharing ReconTerm'.Paths = Paths' !*)
                               (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                               (*! sharing Strict.IntSyn = IntSyn' !*)
                               (*! sharing Strict.Paths = Paths' !*)
                               module Print : PRINT
                             end) : RECON_QUERY =
  struct
    (*! sharing Print.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Paths = Paths' !*)
    module ExtSyn = ReconTerm'
    module T = ReconTerm'
    exception Error of string 
    (* error (r, msg) raises a syntax error within region r with text msg *)
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    (* Queries, with optional proof term variable *)
    type query =
      | query of (name option * T.term)
      [@sml.renamed "query"][@sml.renamed "query"]
    (* define := <constant name> option * <def body> * <type> option *)
    type define =
      | define of (string option * T.term * T.term option)
      [@sml.renamed "define"][@sml.renamed "define"]
    type solve =
      | solve of (string option * T.term * Paths.region)
      [@sml.renamed "solve"][@sml.renamed "solve"]
    (* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = Some("Xi"), false otherwise
  *)
    let rec freeVar =
      function
      | (Some name, __Xs) ->
          List.exists (function | (_, name') -> name = name') __Xs
      | _ -> false__
    (* queryToQuery (q) = (__v, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
    (* call TypeCheck... if !doubleCheck = true? *)
    (* Wed May 20 08:00:28 1998 -fp *)
    let rec queryToQuery (query (optName, tm), Loc (fileName, r)) =
      let _ = Names.varReset IntSyn.Null in
      let _ = T.resetErrors fileName in
      let JClass ((__v, oc), __l) =
        Timers.time Timers.recon T.reconQuery (T.jclass tm) in
      let _ = T.checkErrors r in
      let _ =
        match __l with
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
      (((__v, optName, __Xs))
        (* construct an external term for the result of the query
        val res = (case optName
                     of None => T.omitted (r)
                      | Some name => T.evar (name, r)) *)
        (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *))
    let rec finishDefine
      (define (optName, tm, clsOpt), ((__u, oc1), (__v, oc2Opt), __l)) =
      let (i, (__u', __v')) =
        try Timers.time Timers.abstract Abstract.abstractDef (__u, __v)
        with
        | Error msg ->
            raise (Abstract.Error (Paths.wrap ((Paths.toRegion oc1), msg))) in
      let name = match optName with | None -> "_" | Some name -> name in
      let ocd = Paths.def (i, oc1, oc2Opt) in
      let cd =
        try
          Strict.check ((__u', __v'), (Some ocd));
          IntSyn.ConDef (name, None, i, __u', __v', __l, (IntSyn.ancestor __u'))
        with | Error _ -> IntSyn.AbbrevDef (name, None, i, __u', __v', __l) in
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
          (Timers.time Timers.checking TypeCheck.check (__v', (IntSyn.Uni __l));
           Timers.time Timers.checking TypeCheck.check (__u', __v'))
        else () in
      let conDecOpt = match optName with | None -> None | Some _ -> Some cd in
      (((conDecOpt, (Some ocd)))
        (* is this necessary? -kw *))
    let rec finishSolve (solve (nameOpt, tm, r), __u, __v) =
      let (i, (__u', __v')) =
        try Timers.time Timers.abstract Abstract.abstractDef (__u, __v)
        with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
      let name = match nameOpt with | None -> "_" | Some name -> name in
      let cd =
        try
          Strict.check ((__u', __v'), None);
          IntSyn.ConDef
            (name, None, i, __u', __v', IntSyn.Type, (IntSyn.ancestor __u'))
        with
        | Error _ -> IntSyn.AbbrevDef (name, None, i, __u', __v', IntSyn.Type) in
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
             (__v', (IntSyn.Uni IntSyn.Type));
           Timers.time Timers.checking TypeCheck.check (__u', __v'))
        else () in
      let conDecOpt = match nameOpt with | None -> None | Some _ -> Some cd in
      ((conDecOpt)(* is this necessary? -kw *))
    (* queryToQuery (q) = (__v, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
    (* call TypeCheck... if !doubleCheck = true? *)
    (* Wed May 20 08:00:28 1998 -fp *)
    let rec solveToSolve
      (defines, (solve (optName, tm, r0) as sol), Loc (fileName, r)) =
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
      let JAnd (defines', JClass ((__v, _), __l)) =
        Timers.time Timers.recon T.reconQuery
          (T.jand ((mkj defines), (T.jclass tm))) in
      let _ = T.checkErrors r in
      let _ =
        match __l with
        | IntSyn.Type -> ()
        | _ -> error (r0, "Query was not a type") in
      let rec sc =
        function
        | (M, nil, _) ->
            (match finishSolve (sol, M, __v) with
             | None -> nil
             | Some condec -> [(condec, None)])
        | (M, def::defs, JAnd (JTerm ((__u, oc1), __v, __l), f)) ->
            (match finishDefine (def, ((__u, oc1), (__v, None), __l)) with
             | (None, _) -> sc (M, defs, f)
             | (Some condec, ocdOpt) -> (::) (condec, ocdOpt) sc (M, defs, f))
        | (M, def::defs, JAnd (JOf ((__u, oc1), (__v, oc2), __l), f)) ->
            (match finishDefine (def, ((__u, oc1), (__v, (Some oc2)), __l)) with
             | (None, _) -> sc (M, defs, f)
             | (Some condec, ocdOpt) -> (::) (condec, ocdOpt) sc (M, defs, f)) in
      (((__v, (function | M -> sc (M, defines, defines'))))
        (* val __Xs = Names.namedEVars () *))
  end ;;
