module type PARSE_MODULE  =
  sig
    module ModExtSyn : MODEXTSYN
    val parseSigDef' : ModExtSyn.sigdef Parsing.recparser
    val parseStructDec' : ModExtSyn.structdec Parsing.recparser
    val parseInclude' : ModExtSyn.sigexp Parsing.recparser
    val parseOpen' : ModExtSyn.strexp Parsing.parser
  end


module ParseModule(ParseModule:sig
                                 module ModExtSyn' : MODEXTSYN
                                 module ParseTerm : PARSE_TERM
                               end) : PARSE_MODULE =
  struct
    module ModExtSyn = ModExtSyn'
    module L = Lexer
    module LS = Lexer.Stream
    module E = ModExtSyn
    let rec parseStructExp' =
      begin function
      | Cons ((ID _, r0), _) as f ->
          let ((ids, (ID (_, id), r1)), f') = ParseTerm.parseQualId' f in
          ((E.strexp (ids, id, (Paths.join (r0, r1)))), f')
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected structure identifier, found token " L.toString t)) end
    let rec parseColonEqual' =
      begin function
      | Cons ((L.COLON, r1), s') ->
          (begin match LS.expose s' with
           | Cons ((L.EQUAL, _), s'') -> ((), (LS.expose s''))
           | Cons ((t, r2), s'') ->
               Parsing.error
                 (r2, ((^) "Expected `=', found token " L.toString t)) end)
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `:=', found token " L.toString t)) end
let rec parseDot' =
  begin function
  | Cons ((L.DOT, r), s') -> (r, (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error (r, ((^) "Expected `.', found token " L.toString t)) end
let rec parseConInst' =
  begin function
  | Cons ((ID _, r0), _) as f ->
      let ((ids, (ID (_, id), r1)), f1) = ParseTerm.parseQualId' f in
      let (_, f2) = parseColonEqual' f1 in
      let (tm, f3) = ParseTerm.parseTerm' f2 in
      let (r2, f4) = parseDot' f3 in
      ((E.coninst
          ((ids, id, (Paths.join (r0, r1))), tm, (Paths.join (r0, r2)))), f4)
  | Cons ((t, r), s') ->
      Parsing.error
        (r, ((^) "Expected identifier, found token " L.toString t)) end
let rec parseStrInst2' =
  begin function
  | (r0, (Cons ((ID _, r1), _) as f)) ->
      let ((ids, (ID (_, id), r2)), f1) = ParseTerm.parseQualId' f in
      let (_, f2) = parseColonEqual' f1 in
      let (strexp, f3) = parseStructExp' f2 in
      let (r3, f4) = parseDot' f3 in
      ((E.strinst
          ((ids, id, (Paths.join (r1, r2))), strexp, (Paths.join (r0, r3)))),
        f4)
  | (r0, Cons ((t, r), s')) ->
      Parsing.error
        (r, ((^) "Expected structure identifier, found token " L.toString t)) end
let rec parseStrInst' =
  begin function
  | Cons ((L.STRUCT, r), s') -> parseStrInst2' (r, (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error
        (r, ((^) "Expected `%struct', found token " L.toString t)) end
let rec parseInsts' =
  begin function
  | Cons ((ID _, _), _) as f ->
      let (inst, f') = parseConInst' f in
      let (insts, f'') = parseInsts' f' in ((inst :: insts), f'')
  | Cons ((L.STRUCT, _), _) as f ->
      let (inst, f') = parseStrInst' f in
      let (insts, f'') = parseInsts' f' in ((inst :: insts), f'')
  | Cons ((L.RBRACE, _), s') -> ([], (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error
        (r,
          ((^) "Expected identifier or `%struct', found token " L.toString t)) end
let rec parseInstantiate' =
  begin function
  | Cons ((L.LBRACE, _), s') as f -> parseInsts' (LS.expose s')
  | Cons ((t, r), s') ->
      Parsing.error (r, ((^) "Expected `{', found token " L.toString t)) end
let rec parseWhereClauses' =
  begin function
  | ((Cons ((L.WHERE, _), s') as f), sigexp) ->
      let (insts, f') = parseInstantiate' (LS.expose s') in
      parseWhereClauses' (f', (E.wheresig (sigexp, insts)))
  | (f, sigexp) -> (sigexp, f) end
let rec parseSigExp' =
  begin function
  | Cons ((ID (_, id), r), s) ->
      let (sigexp, f') =
        parseWhereClauses' ((LS.expose s), (E.sigid (id, r))) in
      ((Parsing.Done sigexp), f')
  | Cons ((L.LBRACE, r), _) as f ->
      ((Parsing.Continuation
          (begin function
           | f' ->
               let (sigexp, f'') = parseWhereClauses' (f', E.thesig) in
               ((Parsing.Done sigexp), f'') end)),
      f)
  | Cons ((t, r), _) ->
      Parsing.error
        (r,
          ((^) "Expected signature name or expression, found token "
             L.toString t)) end
let rec parseSgEqual' =
  begin function
  | (idOpt, Cons ((L.EQUAL, r), s')) ->
      Parsing.recwith
        (parseSigExp',
          (begin function | sigexp -> E.sigdef (idOpt, sigexp) end))
      (LS.expose s')
  | (idOpt, Cons ((t, r), s')) ->
      Parsing.error (r, ((^) "Expected `=', found token " L.toString t)) end
let rec parseSgDef' =
  begin function
  | Cons ((ID (_, id), r), s') -> parseSgEqual' ((Some id), (LS.expose s'))
  | Cons ((L.UNDERSCORE, r), s') -> parseSgEqual' (None, (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error
        (r, ((^) "Expected signature identifier, found token " L.toString t)) end
let rec parseSigDef' (Cons ((L.SIG, r), s')) = parseSgDef' (LS.expose s')
let rec parseStrDec2' =
  begin function
  | (idOpt, Cons ((L.COLON, r), s')) ->
      Parsing.recwith
        (parseSigExp',
          (begin function | sigexp -> E.structdec (idOpt, sigexp) end))
      (LS.expose s')
  | (idOpt, Cons ((L.EQUAL, r), s')) ->
      let (strexp, f') = parseStructExp' (LS.expose s') in
      ((Parsing.Done (E.structdef (idOpt, strexp))), f')
  | (idOpt, Cons ((t, r), s')) ->
      Parsing.error
        (r, ((^) "Expected `:' or `=', found token " L.toString t)) end
let rec parseStrDec' =
  begin function
  | Cons ((ID (_, id), r), s') -> parseStrDec2' ((Some id), (LS.expose s'))
  | Cons ((L.UNDERSCORE, r), s') -> parseStrDec2' (None, (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error
        (r, ((^) "Expected structure identifier, found token " L.toString t)) end
let rec parseStructDec' (Cons ((L.STRUCT, r), s')) =
  parseStrDec' (LS.expose s')
let rec parseInclude' (Cons ((L.INCLUDE, r), s')) =
  parseSigExp' (LS.expose s')
let rec parseOpen' (Cons ((L.OPEN, r), s')) = parseStructExp' (LS.expose s')
end
