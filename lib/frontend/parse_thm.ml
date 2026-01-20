
module type PARSE_THM  =
  sig
    module ThmExtSyn : THMEXTSYN
    val parseTotal' : ThmExtSyn.tdecl Parsing.parser
    val parseTerminates' : ThmExtSyn.tdecl Parsing.parser
    val parseReduces' : ThmExtSyn.rdecl Parsing.parser
    val parseTabled' : ThmExtSyn.tableddecl Parsing.parser
    val parseKeepTable' : ThmExtSyn.keepTabledecl Parsing.parser
    val parseTheorem' : ThmExtSyn.theorem Parsing.parser
    val parseTheoremDec' : ThmExtSyn.theoremdec Parsing.parser
    val parseWorlds' : ThmExtSyn.wdecl Parsing.parser
    val parseProve' : ThmExtSyn.prove Parsing.parser
    val parseEstablish' : ThmExtSyn.establish Parsing.parser
    val parseAssert' : ThmExtSyn.assert__ Parsing.parser
  end;;




module ParseThm(ParseThm:sig
                           module ThmExtSyn' : THMEXTSYN
                           module ParseTerm : PARSE_TERM
                         end) : PARSE_THM =
  struct
    module ThmExtSyn = ThmExtSyn'
    module L = Lexer
    module LS = Lexer.Stream
    module E = ThmExtSyn
    module P = Paths
    let rec idToNat r name =
      try L.stringToNat name
      with | Overflow -> Parsing.error (r, "Integer too large")
      | NotDigit _ -> Parsing.error (r, "Identifier not a natural number")
    let rec stripRParen =
      function
      | Cons ((L.RPAREN, r), s') -> LS.expose s'
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `)', found " L.toString t))
    let rec decideRBrace __0__ __1__ =
      match (__0__, __1__) with
      | (r0, (orders, Cons ((L.RBRACE, r), s'))) ->
          ((Some (E.lex (r0, orders))), (LS.expose s'))
      | (r0, (order, Cons ((t, r), _))) ->
          Parsing.error
            ((P.join (r0, r)), ((^) "Expected `}', found " L.toString t))
    let rec decideRBracket __2__ __3__ =
      match (__2__, __3__) with
      | (r0, (orders, Cons ((L.RBRACKET, r), s'))) ->
          ((Some (E.simul (r0, orders))), (LS.expose s'))
      | (r0, (order, Cons ((t, r), _))) ->
          Parsing.error
            ((P.join (r0, r)), ((^) "Expected `]', found " L.toString t))
    let rec decideRParen __4__ __5__ =
      match (__4__, __5__) with
      | (r0, (ids, Cons ((L.RPAREN, r), s'))) ->
          ((Some (E.varg (r, ids))), (LS.expose s'))
      | (r0, (order, Cons ((t, r), _))) ->
          Parsing.error
            ((P.join (r0, r)), ((^) "Expected `)', found " L.toString t))
    let rec parseIds =
      function
      | Cons ((ID (L.Upper, id), r), s') ->
          let (ids, f') = parseIds (LS.expose s') in ((id :: ids), f')
      | Cons (((ID (_, id) as t), r), s') ->
          Parsing.error
            (r, ((^) "Expecter upper case identifier, found " L.toString t))
      | f -> (nil, f)
    let rec parseArgPat =
      function
      | Cons ((ID (L.Upper, id), r), s') ->
          let (idOpts, f') = parseArgPat (LS.expose s') in
          (((Some id) :: idOpts), f')
      | Cons ((ID (_, id), r), s') ->
          Parsing.error (r, ("Expected upper case identifier, found " ^ id))
      | Cons ((L.UNDERSCORE, r), s') ->
          let (idOpts, f') = parseArgPat (LS.expose s') in
          ((NONE :: idOpts), f')
      | f -> (nil, f)
    let rec parseCallPat =
      function
      | Cons ((ID (_, id), r), s') ->
          let (idOpts, (Cons ((_, r'), _) as f')) =
            parseArgPat (LS.expose s') in
          ((id, idOpts, (P.join (r, r'))), f')
      | Cons ((t, r), s) ->
          Parsing.error
            (r, ((^) "Expected call pattern, found token " L.toString t))
    let rec parseCallPats =
      function
      | Cons ((L.LPAREN, r), s') ->
          let (cpat, f') = parseCallPat (LS.expose s') in
          let (cpats, f'') = parseCallPats (stripRParen f') in
          ((cpat :: cpats), f'')
      | Cons ((L.DOT, r), s') as f -> (nil, f)
      | Cons ((t, r), s) ->
          Parsing.error
            (r, ((^) "Expected call patterns, found token " L.toString t))
      (* Parens around call patterns no longer optional *)
    let rec parseOrderOpt =
      function
      | Cons ((L.LPAREN, r), s') ->
          decideRParen (r, (parseIds (LS.expose s')))
      | Cons ((L.LBRACE, r), s') ->
          decideRBrace (r, (parseOrders (LS.expose s')))
      | Cons ((L.LBRACKET, r), s') ->
          decideRBracket (r, (parseOrders (LS.expose s')))
      | Cons ((ID (L.Upper, id), r), s') ->
          ((Some (E.varg (r, [id]))), (LS.expose s'))
      | Cons (_, s') as f -> (NONE, f)
    let rec parseOrders f = parseOrders' (parseOrderOpt f)
    let rec parseOrders' __6__ __7__ =
      match (__6__, __7__) with
      | (Some order, f') ->
          let (orders, f'') = parseOrders f' in ((order :: orders), f'')
      | (NONE, f') -> (nil, f')
    let rec parseOrder f = parseOrder' (parseOrderOpt f)
    let rec parseOrder' __8__ __9__ =
      match (__8__, __9__) with
      | (Some order, f') -> (order, f')
      | (NONE, Cons ((t, r), s')) ->
          Parsing.error (r, ((^) "Expected order, found " L.toString t))
    let rec parseTDecl f =
      let (order, f') = parseOrder f in
      let (callpats, f'') = parseCallPats f' in
      ((E.tdecl (order, (E.callpats callpats))), f'')
    let rec parseTerminates' (Cons ((L.TERMINATES, r), s')) =
      parseTDecl (LS.expose s')
    let rec parseTotal' (Cons ((L.TOTAL, r), s')) = parseTDecl (LS.expose s')
    let rec parsePDecl =
      function
      | Cons ((ID (_, id), r), s') ->
          let depth = idToNat (r, id) in
          let (t', f') = parseTDecl (LS.expose s') in
          ((E.prove (depth, t')), f')
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected theorem identifier, found " L.toString t))
    let rec parseProve' (Cons ((L.PROVE, r), s')) = parsePDecl (LS.expose s')
    let rec parseEDecl =
      function
      | Cons ((ID (_, id), r), s') ->
          let depth = idToNat (r, id) in
          let (t', f') = parseTDecl (LS.expose s') in
          ((E.establish (depth, t')), f')
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected theorem identifier, found " L.toString t))
    let rec parseEstablish' (Cons ((L.ESTABLISH, r), s')) =
      parseEDecl (LS.expose s')
    let rec parseAssert' (Cons ((L.ASSERT, r), s')) =
      let (callpats, f'') = parseCallPats (LS.expose s') in
      ((E.assert__ (E.callpats callpats)), f'')
    let rec stripRBrace =
      function
      | Cons ((L.RBRACE, r), s') -> ((LS.expose s'), r)
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `}', found " L.toString t))
    let rec parseDec r f =
      let ((x, yOpt), f') = ParseTerm.parseDec' f in
      let (f'', r2) = stripRBrace f' in
      let dec =
        match yOpt with
        | NONE -> E.ExtSyn.dec0 (x, (P.join (r, r2)))
        | Some y -> E.ExtSyn.dec (x, y, (P.join (r, r2))) in
      (dec, f'')
    let rec parseDecs' __10__ __11__ =
      match (__10__, __11__) with
      | (Drs, Cons (((L.LBRACE, r), s') as BS)) ->
          let (Dr, f') = parseDec (r, (LS.expose s')) in
          parseDecs' ((E.decl (Drs, Dr)), f')
      | Drs -> Drs
    let rec parseDecs =
      function
      | Cons (((L.LBRACE, r), s') as BS) ->
          let (Dr, f') = parseDec (r, (LS.expose s')) in
          parseDecs' ((E.decl (E.null, Dr)), f')
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `{', found " L.toString t))
    let rec parsePi =
      function
      | Cons ((ID (_, "pi"), r), s') -> parseDecs (LS.expose s')
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `pi', found " L.toString t))
    let rec parseSome __12__ __13__ =
      match (__12__, __13__) with
      | (gbs, Cons ((ID (_, "some"), r), s')) ->
          let (g1, f') = parseDecs (LS.expose s') in
          let (g2, f'') = parsePi f' in parseSome' (((g1, g2) :: gbs), f'')
      | (gbs, (Cons ((ID (_, "pi"), r), s') as f)) ->
          let (g2, f') = parsePi f in parseSome' (((E.null, g2) :: gbs), f')
      | (gbs, (Cons ((L.RPAREN, r), s') as f)) -> (gbs, f)
      | (gbs, Cons ((t, r), s')) ->
          Parsing.error
            (r, ((^) "Expected `some' or `pi', found " L.toString t))
    let rec parseSome' __14__ __15__ =
      match (__14__, __15__) with
      | (gbs, (Cons ((L.RPAREN, r), s') as f)) -> (gbs, f)
      | (gbs, Cons ((ID (_, "|"), r), s')) -> parseSome (gbs, (LS.expose s'))
      | (gbs, Cons ((t, r), s')) ->
          Parsing.error (r, ((^) "Expected `)' or `|', found " L.toString t))
    let rec stripParen gbs (Cons ((L.RPAREN, r), s')) = (gbs, (LS.expose s'))
    let rec parseGBs =
      function
      | Cons ((L.LPAREN, r), s') ->
          stripParen (parseSome (nil, (LS.expose s')))
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `(', found " L.toString t))
    let rec forallG (gbs', f') r =
      let (t'', f'') = parseForallStar f' in ((E.forallG (gbs', t'')), f'')
    let rec forallStar (g', f') r =
      let (t'', f'') = parseForall f' in ((E.forallStar (g', t'')), f'')
    let rec forall (g', f') r =
      let (t'', f'') = parseExists f' in ((E.forall (g', t'')), f'')
    let rec exists (g', f') r =
      let (t'', f'') = parseTrue f' in ((E.exists (g', t'')), f'')
    let rec top f' r = (E.top, f')
    let rec parseTrue =
      function
      | Cons ((ID (_, "true"), r), s') -> top ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `true', found " L.toString t))
    let rec parseExists =
      function
      | Cons ((ID (_, "exists"), r), s') ->
          exists ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "true"), r), s') -> top ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected `exists' or `true', found " L.toString t))
    let rec parseForall =
      function
      | Cons ((ID (_, "forall"), r), s') ->
          forall ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "exists"), r), s') ->
          exists ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "true"), r), s') -> top ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected `forall', `exists', or `true', found "
                 L.toString t))
    let rec parseForallStar =
      function
      | Cons ((ID (_, "forall*"), r), s') ->
          forallStar ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "forall"), r), s') ->
          forall ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "exists"), r), s') ->
          exists ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "true"), r), s') -> top ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected `forall*', `forall', `exists', or `true', found "
                 L.toString t))
    let rec parseCtxScheme =
      function
      | Cons ((ID (_, "forallG"), r), s') ->
          forallG ((parseGBs (LS.expose s')), r)
      | Cons ((ID (_, "forall*"), r), s') ->
          forallStar ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "forall"), r), s') ->
          forall ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "exists"), r), s') ->
          exists ((parseDecs (LS.expose s')), r)
      | Cons ((ID (_, "true"), r), s') -> top ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected `forallG', `forall*', `forall', `exists', or `true', found "
                 L.toString t))
    let rec parseColon =
      function
      | Cons ((L.COLON, r), s') -> parseCtxScheme (LS.expose s')
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `:', found " L.toString t))
    let rec parseThDec =
      function
      | Cons ((ID (_, id), r), s') ->
          let (t', f') = parseColon (LS.expose s') in ((E.dec (id, t')), f')
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected theorem identifier, found " L.toString t))
    let rec parseTheoremDec' (Cons ((L.THEOREM, r), s')) =
      parseThDec (LS.expose s')
    let rec parsePredicate =
      function
      | Cons ((ID (_, "<"), r), s') ->
          ((E.predicate ("LESS", r)), (LS.expose s'))
      | Cons ((ID (_, "<="), r), s') ->
          ((E.predicate ("LEQ", r)), (LS.expose s'))
      | Cons ((L.EQUAL, r), s') ->
          ((E.predicate ("EQUAL", r)), (LS.expose s'))
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected reduction predicate <, = or <=, found "
                 L.toString t))
    let rec parseRDecl f =
      let (oOut, f1) = parseOrder f in
      let (p, f2) = parsePredicate f1 in
      let (oIn, f3) = parseOrder f2 in
      let (callpats, f4) = parseCallPats f3 in
      ((E.rdecl (p, oOut, oIn, (E.callpats callpats))), f4)
    let rec parseReduces' (Cons ((L.REDUCES, r), s')) =
      parseRDecl (LS.expose s')
    let rec parseTabledDecl (Cons ((ID (_, id), r), s') as f) =
      match LS.expose s' with
      | Cons ((L.DOT, r'), s) as f -> ((E.tableddecl (id, r)), f)
      | _ -> Parsing.error (r, "Expected .")
    let rec parseTabled' (Cons ((L.TABLED, r), s')) =
      parseTabledDecl (LS.expose s')
    let rec parseKeepTableDecl (Cons ((ID (_, id), r), s') as f) =
      match LS.expose s' with
      | Cons ((L.DOT, r'), s) as f -> ((E.keepTabledecl (id, r)), f)
      | _ -> Parsing.error (r, "Expected .")
    let rec parseKeepTable' (Cons ((L.KEEPTABLE, r), s')) =
      parseKeepTableDecl (LS.expose s')
    let rec parseWDecl f =
      let (qids, f1) = ParseTerm.parseQualIds' f in
      let (callpats, f2) = parseCallPats f1 in
      ((((E.wdecl (qids, (E.callpats callpats))), f2))
        (*       val (GBs, f1) = parseGBs f *))
    let rec parseWorlds' (Cons ((L.WORLDS, r), s')) =
      parseWDecl (LS.expose s')
    let parseTotal' = parseTotal'
    let parseTerminates' = parseTerminates'
    let parseTheorem' = parseForallStar
    let parseTheoremDec' = parseTheoremDec'
    let parseProve' = parseProve'
    let parseEstablish' = parseEstablish'
    let parseAssert' = parseAssert'
    let parseReduces' = parseReduces'
    let parseTabled' = parseTabled'
    let parseKeepTable' = parseKeepTable'
    let parseWorlds' = parseWorlds'
  end ;;
