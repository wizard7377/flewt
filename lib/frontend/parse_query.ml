module type PARSE_QUERY  =
  sig
    module ExtQuery : EXTQUERY
    val parseQuery' : ExtQuery.query Parsing.parser
    val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser
  end


module ParseQuery(ParseQuery:sig
                               module ExtQuery' : EXTQUERY
                               module ParseTerm : PARSE_TERM
                             end) : PARSE_QUERY =
  struct
    module ExtQuery = ExtQuery'
    module L = Lexer
    module LS = Lexer.Stream
    module P = Paths
    let rec returnQuery (optName, (tm, f)) =
      ((ExtQuery.query (optName, tm)), f)
    let rec parseQuery1 =
      begin function
      | (name, f, Cons ((L.COLON, r), s')) ->
          returnQuery ((Some name), (ParseTerm.parseTerm' (LS.expose s')))
      | (name, f, _) -> returnQuery (None, (ParseTerm.parseTerm' f)) end
    let rec parseQuery' =
      begin function
      | Cons ((ID (L.Upper, name), r), s') as f ->
          parseQuery1 (name, f, (LS.expose s'))
      | f -> returnQuery (None, (ParseTerm.parseTerm' f)) end
  let rec parseQuery s = parseQuery' (LS.expose s)
  let rec parseDefine4 (optName, optT, s) =
    let (tm', f') = ParseTerm.parseTerm' (LS.expose s) in
    ((ExtQuery.define (optName, tm', optT)), f')
  let rec parseDefine3 =
    begin function
    | (optName, (tm, Cons ((L.EQUAL, r), s'))) ->
        parseDefine4 (optName, (Some tm), s')
    | (_, (tm, Cons ((t, r), _))) ->
        Parsing.error (r, ((^) "Expected `=', found " L.toString t)) end
let rec parseDefine2 =
  begin function
  | (optName, Cons ((L.COLON, r), s')) ->
      parseDefine3 (optName, (ParseTerm.parseTerm' (LS.expose s')))
  | (optName, Cons ((L.EQUAL, r), s')) -> parseDefine4 (optName, None, s')
  | (_, Cons ((t, r), _)) ->
      Parsing.error (r, ((^) "Expected `:' or `=', found " L.toString t)) end
let rec parseDefine1 =
  begin function
  | Cons ((ID (idCase, name), r), s') ->
      parseDefine2 ((Some name), (LS.expose s'))
  | Cons ((L.UNDERSCORE, r), s') -> parseDefine2 (None, (LS.expose s'))
  | Cons ((t, r), _) ->
      Parsing.error
        (r, ((^) "Expected identifier or `_', found " L.toString t)) end
let rec parseSolve3 =
  begin function
  | (defns, nameOpt, Cons ((L.COLON, r), s'), r0) ->
      let (tm, (Cons ((_, r), _) as f')) =
        ParseTerm.parseTerm' (LS.expose s') in
      (((List.rev defns), (ExtQuery.solve (nameOpt, tm, (P.join (r0, r))))),
        f')
  | (_, _, Cons ((t, r), s'), r0) ->
      Parsing.error (r, ((^) "Expected `:', found " L.toString t)) end
let rec parseSolve2 =
  begin function
  | (defns, Cons ((L.UNDERSCORE, r), s'), r0) ->
      parseSolve3 (defns, None, (LS.expose s'), r0)
  | (defns, Cons ((ID (_, name), r), s'), r0) ->
      parseSolve3 (defns, (Some name), (LS.expose s'), r0)
  | (_, Cons ((t, r), s'), r0) ->
      Parsing.error
        (r, ((^) "Expected identifier or `_', found " L.toString t)) end
let rec parseSolve1 =
  begin function
  | (defns, Cons ((L.SOLVE, r0), s')) ->
      parseSolve2 (defns, (LS.expose s'), r0)
  | (defns, Cons ((L.DEFINE, r0), s')) ->
      let (defn, f') = parseDefine1 (LS.expose s') in
      parseSolve1 ((defn :: defns), f')
  | (defns, Cons ((t, r), s)) ->
      Parsing.error
        (r, ((^) "Expected %define or %solve, found " L.toString t)) end
let rec parseSolve' f = parseSolve1 ([], f)
let parseQuery' = parseQuery'
let parseSolve' = parseSolve' end
