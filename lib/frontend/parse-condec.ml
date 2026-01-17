
module type PARSE_CONDEC  =
  sig
    module ExtConDec :
    ((EXTCONDEC)(* Parsing Signature Entries *)(* Author: Frank Pfenning *)
    (*! structure Parsing : PARSING !*))
    val parseConDec' : ExtConDec.condec Parsing.parser
    val parseAbbrev' : ExtConDec.condec Parsing.parser
    val parseClause' : ExtConDec.condec Parsing.parser
  end;;




module ParseConDec(ParseConDec:sig
                                 module ExtConDec' : EXTCONDEC
                                 module ParseTerm :
                                 ((PARSE_TERM)(* Parsing Signature Entries *)
                                 (* Author: Frank Pfenning *)(*! structure Parsing' : PARSING !*))
                               end) : PARSE_CONDEC =
  struct
    module ExtConDec =
      ((ExtConDec')(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
      (*! structure Parsing = Parsing' !*))
    module L = Lexer
    module LS = Lexer.Stream
    let rec parseConDec3 (optName, optTm, s) =
      let (tm', f') = ParseTerm.parseTerm' (LS.expose s) in
      ((ExtConDec.condef (optName, tm', optTm)), f')
    let rec parseConDec2 =
      function
      | (optName, (tm, Cons ((L.EQUAL, r), s'))) ->
          parseConDec3 (optName, (SOME tm), s')
      | (SOME name, (tm, f)) -> ((ExtConDec.condec (name, tm)), f)
      | (NONE, (tm, Cons ((t, r), s'))) ->
          Parsing.error (r, "Illegal anonymous declared constant")
    let rec parseConDec1 =
      function
      | (optName, Cons ((L.COLON, r), s')) ->
          parseConDec2 (optName, (ParseTerm.parseTerm' (LS.expose s')))
      | (optName, Cons ((L.EQUAL, r), s')) ->
          parseConDec3 (optName, NONE, s')
      | (optName, Cons ((t, r), s')) ->
          Parsing.error (r, ((^) "Expected `:' or `=', found " L.toString t))
    let rec parseBlock =
      function
      | Cons ((ID (_, "block"), r), s') -> ParseTerm.parseCtx' (LS.expose s')
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `block', found " L.toString t))
    let rec parseSome =
      function
      | (name, Cons ((ID (_, "some"), r), s')) ->
          let (g1, f') = ParseTerm.parseCtx' (LS.expose s') in
          let (g2, f'') = parseBlock f' in
          ((ExtConDec.blockdec (name, g1, g2)), f'')
      | (name, (Cons ((ID (_, "block"), r), s') as f)) ->
          let (g2, f') = parseBlock f in
          ((ExtConDec.blockdec (name, nil, g2)), f')
      | (name, Cons ((t, r), s')) ->
          Parsing.error
            (r, ((^) "Expected `some' or `block', found " L.toString t))
    let rec parseBlockDec1 =
      function
      | (name, Cons ((L.COLON, r), s')) -> parseSome (name, (LS.expose s'))
      | (name, Cons ((L.EQUAL, r), s')) ->
          let (g, f) = ParseTerm.parseQualIds' (LS.expose s') in
          ((ExtConDec.blockdef (name, g)), f)
      | (name, Cons ((t, r), s')) ->
          Parsing.error (r, ((^) "`:' expected, found token " L.toString t))
    let rec parseBlockDec' =
      function
      | Cons ((ID (idCase, name), r), s') ->
          parseBlockDec1 (name, (LS.expose s'))
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Label identifier expected, found token " L.toString t))
    let rec parseConDec' =
      function
      | Cons ((ID (idCase, name), r), s') ->
          parseConDec1 ((SOME name), (LS.expose s'))
      | Cons ((L.UNDERSCORE, r), s') -> parseConDec1 (NONE, (LS.expose s'))
      | Cons ((L.BLOCK, r), s') -> parseBlockDec' (LS.expose s')
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Constant or block declaration expected, found token "
                 L.toString t))
    let rec parseConDec s = parseConDec' (LS.expose s)
    let rec parseAbbrev' (Cons ((L.ABBREV, r), s)) = parseConDec s
    let rec parseClause' (Cons ((L.CLAUSE, r), s)) = parseConDec s
    let ((parseConDec')(* parseConDec3  "U" *)(* parseConDec2  "= U" | "" *)
      (* parseConDec1  ": V = U" | "= U" *)(* BlockDec parser *)
      (* added as a feature request by Carl  -- Wed Mar 16 16:11:44 2011  cs *)
      (* parseConDec' : lexResult front -> ExtConDec.ConDec * lexResult front
       Invariant: first token in exposed input stream is an identifier or underscore
    *)
      (* parseConDec --- currently not exported *)(* -fp *))
      = parseConDec'
    let parseAbbrev' = parseAbbrev'
    let parseClause' = parseClause'
  end ;;
