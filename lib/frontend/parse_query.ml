
(* Parsing Queries *)
(* Author: Frank Pfenning *)
module type PARSE_QUERY  =
  sig
    (*! structure Parsing : PARSING !*)
    module ExtQuery : EXTQUERY
    val parseQuery' : ExtQuery.query Parsing.parser
    val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser
  end;;




(* Parsing Queries *)
(* Author: Frank Pfenning *)
module ParseQuery(ParseQuery:sig
                               (*! structure Parsing' : PARSING !*)
                               module ExtQuery' : EXTQUERY
                               (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
                               module ParseTerm : PARSE_TERM
                             end) : PARSE_QUERY =
  struct
    (*! structure Parsing = Parsing' !*)
    module ExtQuery = ExtQuery'
    module __l = Lexer
    module LS = Lexer.Stream
    module P = Paths
    let rec returnQuery (optName, (tm, f)) =
      ((ExtQuery.query (optName, tm)), f)
    let rec parseQuery1 =
      function
      | (name, f, Cons ((L.COLON, r), s')) ->
          returnQuery ((Some name), (ParseTerm.parseTerm' (LS.expose s')))
      | (name, f, _) -> returnQuery (None, (ParseTerm.parseTerm' f))
    let rec parseQuery' =
      function
      | Cons ((ID (L.Upper, name), r), s') as f ->
          parseQuery1 (name, f, (LS.expose s'))
      | f -> returnQuery (None, (ParseTerm.parseTerm' f))
    let rec parseQuery s = parseQuery' (LS.expose s)
    let rec parseDefine4 (optName, optT, s) =
      let (tm', f') = ParseTerm.parseTerm' (LS.expose s) in
      ((ExtQuery.define (optName, tm', optT)), f')
    let rec parseDefine3 =
      function
      | (optName, (tm, Cons ((L.EQUAL, r), s'))) ->
          parseDefine4 (optName, (Some tm), s')
      | (_, (tm, Cons ((t, r), _))) ->
          Parsing.error (r, ((^) "Expected `=', found " L.toString t))
    let rec parseDefine2 =
      function
      | (optName, Cons ((L.COLON, r), s')) ->
          parseDefine3 (optName, (ParseTerm.parseTerm' (LS.expose s')))
      | (optName, Cons ((L.EQUAL, r), s')) ->
          parseDefine4 (optName, None, s')
      | (_, Cons ((t, r), _)) ->
          Parsing.error (r, ((^) "Expected `:' or `=', found " L.toString t))
    let rec parseDefine1 =
      function
      | Cons ((ID (idCase, name), r), s') ->
          parseDefine2 ((Some name), (LS.expose s'))
      | Cons ((L.UNDERSCORE, r), s') -> parseDefine2 (None, (LS.expose s'))
      | Cons ((t, r), _) ->
          Parsing.error
            (r, ((^) "Expected identifier or `_', found " L.toString t))
    let rec parseSolve3 =
      function
      | (defns, nameOpt, Cons ((L.COLON, r), s'), r0) ->
          let (tm, (Cons ((_, r), _) as f')) =
            ParseTerm.parseTerm' (LS.expose s') in
          (((List.rev defns),
             (ExtQuery.solve (nameOpt, tm, (P.join (r0, r))))), f')
      | (_, _, Cons ((t, r), s'), r0) ->
          Parsing.error (r, ((^) "Expected `:', found " L.toString t))
    let rec parseSolve2 =
      function
      | (defns, Cons ((L.UNDERSCORE, r), s'), r0) ->
          parseSolve3 (defns, None, (LS.expose s'), r0)
      | (defns, Cons ((ID (_, name), r), s'), r0) ->
          parseSolve3 (defns, (Some name), (LS.expose s'), r0)
      | (_, Cons ((t, r), s'), r0) ->
          Parsing.error
            (r, ((^) "Expected identifier or `_', found " L.toString t))
    let rec parseSolve1 =
      function
      | (defns, Cons ((L.SOLVE, r0), s')) ->
          parseSolve2 (defns, (LS.expose s'), r0)
      | (defns, Cons ((L.DEFINE, r0), s')) ->
          let (defn, f') = parseDefine1 (LS.expose s') in
          parseSolve1 ((defn :: defns), f')
      | (defns, Cons ((t, r), s)) ->
          Parsing.error
            (r, ((^) "Expected %define or %solve, found " L.toString t))
    let rec parseSolve' f = parseSolve1 (nil, f)
    (* parseQuery1 (name, f, f')   ": A" from f' or "__v" from f. *)
    (* parseQuery' : lexResult front -> ExtQuery.query * lexResult front *)
    (* parseQuery'  "x : A" | "A" *)
    (* Query parsing is ambiguous, since a term "__v" might have the form "__u' : __v'" *)
    (* We look for an uppercase variable x followed by a `:'.
       If we find this, we parse a query of the form "x : A".
       Otherwise we parse a query of the form "A".
    *)
    (* parseQuery --- currently not exported *)
    (* parseDefine4 parses the definition body *)
    (* "__u" *)
    (* parseDefine3 parses the equal sign in a long form define *)
    (* "= __u" *)
    (* parseDefine2 switches between short and long form *)
    (* ": __v = __u" | "= __u" *)
    (* parseDefine1 parses the name of the constant to be defined *)
    (* "c : __v = __u" | "_ : __v = __u" | "c = __u" | "_ = __u" *)
    let parseQuery' = parseQuery'
    let parseSolve' = parseSolve'
  end ;;
