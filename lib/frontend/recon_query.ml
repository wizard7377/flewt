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
    include EXTQUERY
    exception Error of string 
    val queryToQuery :
      (query * Paths.location) ->
        (IntSyn.exp_ * string option * (IntSyn.exp_ * string) list)
    val solveToSolve :
      (define list * solve * Paths.location) ->
        (IntSyn.exp_ *
          (IntSyn.exp_ -> (IntSyn.conDec_ * Paths.occConDec option) list))
  end


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
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
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
    let rec freeVar =
      begin function
      | (Some name, xs_) ->
          List.exists (begin function | (_, name') -> name = name' end) xs_
      | _ -> false end
  let rec queryToQuery (query (optName, tm), Loc (fileName, r)) =
    let _ = Names.varReset IntSyn.Null in
    let _ = T.resetErrors fileName in
    let JClass ((v_, oc), l_) =
      Timers.time Timers.recon T.reconQuery (T.jclass tm) in
    let _ = T.checkErrors r in
    let _ =
      begin match l_ with
      | IntSyn.Type -> ()
      | _ -> error (r, "Query was not a type") end in
    let xs_ = Names.namedEVars () in
    let _ =
      if freeVar (optName, xs_)
      then
        begin error
                (r,
                  (((^) "Proof term variable " valOf optName) ^
                     " occurs in type")) end
      else begin () end in
    (((v_, optName, xs_))
      (* construct an external term for the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
      (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *))
let rec finishDefine
  (define (optName, tm, clsOpt), ((u_, oc1), (v_, oc2Opt), l_)) =
  let (i, (u'_, v'_)) =
    begin try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
    with
    | Error msg ->
        raise (Abstract.Error (Paths.wrap ((Paths.toRegion oc1), msg))) end in
let name = begin match optName with | None -> "_" | Some name -> name end in
let ocd = Paths.def (i, oc1, oc2Opt) in
let cd =
  begin try
          begin Strict.check ((u'_, v'_), (Some ocd));
          IntSyn.ConDef (name, None, i, u'_, v'_, l_, (IntSyn.ancestor u'_)) end
  with | Error _ -> IntSyn.AbbrevDef (name, None, i, u'_, v'_, l_) end in
let cd = Names.nameConDec cd in
let _ =
  if !Global.chatter >= 3
  then
    begin print
            ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n") end
  else begin () end in
let _ =
  if !Global.doubleCheck
  then
    begin (begin Timers.time Timers.checking TypeCheck.check
                   (v'_, (IntSyn.Uni l_));
           Timers.time Timers.checking TypeCheck.check (u'_, v'_) end) end
  else begin () end in
let conDecOpt = begin match optName with | None -> None | Some _ -> Some cd end in
(((conDecOpt, (Some ocd)))
(* is this necessary? -kw *))
let rec finishSolve (solve (nameOpt, tm, r), u_, v_) =
  let (i, (u'_, v'_)) =
    begin try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
    with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) end in
let name = begin match nameOpt with | None -> "_" | Some name -> name end in
let cd =
  begin try
          begin Strict.check ((u'_, v'_), None);
          IntSyn.ConDef
            (name, None, i, u'_, v'_, IntSyn.Type, (IntSyn.ancestor u'_)) end
  with | Error _ -> IntSyn.AbbrevDef (name, None, i, u'_, v'_, IntSyn.Type) end in
let cd = Names.nameConDec cd in
let _ =
  if !Global.chatter >= 3
  then
    begin print
            ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n") end
  else begin () end in
let _ =
  if !Global.doubleCheck
  then
    begin (begin Timers.time Timers.checking TypeCheck.check
                   (v'_, (IntSyn.Uni IntSyn.Type));
           Timers.time Timers.checking TypeCheck.check (u'_, v'_) end) end
  else begin () end in
let conDecOpt = begin match nameOpt with | None -> None | Some _ -> Some cd end in
((conDecOpt)
(* is this necessary? -kw *))
let rec solveToSolve
  (defines, (solve (optName, tm, r0) as sol), Loc (fileName, r)) =
  let _ = Names.varReset IntSyn.Null in
  let _ = T.resetErrors fileName in
  let rec mkd =
    begin function
    | define (_, tm1, None) -> T.jterm tm1
    | define (_, tm1, Some tm2) -> T.jof (tm1, tm2) end in
  let rec mkj =
    begin function
    | [] -> T.jnothing
    | def::defs -> T.jand ((mkd def), (mkj defs)) end in
  let JAnd (defines', JClass ((v_, _), l_)) =
    Timers.time Timers.recon T.reconQuery
      (T.jand ((mkj defines), (T.jclass tm))) in
  let _ = T.checkErrors r in
  let _ =
    begin match l_ with
    | IntSyn.Type -> ()
    | _ -> error (r0, "Query was not a type") end in
  let rec sc =
    begin function
    | (m_, [], _) ->
        (begin match finishSolve (sol, m_, v_) with
         | None -> []
         | Some condec -> [(condec, None)] end)
    | (m_, def::defs, JAnd (JTerm ((u_, oc1), v_, l_), f)) ->
        (begin match finishDefine (def, ((u_, oc1), (v_, None), l_)) with
         | (None, _) -> sc (m_, defs, f)
         | (Some condec, ocdOpt) -> (::) (condec, ocdOpt) sc (m_, defs, f) end)
    | (m_, def::defs, JAnd (JOf ((u_, oc1), (v_, oc2), l_), f)) ->
        (begin match finishDefine (def, ((u_, oc1), (v_, (Some oc2)), l_))
               with
         | (None, _) -> sc (m_, defs, f)
         | (Some condec, ocdOpt) -> (::) (condec, ocdOpt) sc (m_, defs, f) end) end in
  (((v_, (begin function | m_ -> sc (m_, defines, defines') end)))
  (* val Xs = Names.namedEVars () *)) end
