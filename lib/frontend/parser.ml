
(* Top-Level Parser *)
(* Author: Frank Pfenning *)
module type PARSER  =
  sig
    (*! structure Parsing : PARSING !*)
    module Stream : STREAM
    module ExtSyn : EXTSYN
    module Names : NAMES
    module ExtConDec : EXTCONDEC
    module ExtQuery : EXTQUERY
    module ExtModes : EXTMODES
    module ThmExtSyn : THMEXTSYN
    module ModExtSyn : MODEXTSYN
    type fileParseResult =
      | ConDec of ExtConDec.condec 
      | FixDec of ((Names.__Qid * Paths.region) * Names.Fixity.fixity) 
      | NamePref of ((Names.__Qid * Paths.region) * (string list * string
      list)) 
      | ModeDec of ExtModes.modedec list 
      | UniqueDec of ExtModes.modedec list 
      | CoversDec of ExtModes.modedec list 
      | TotalDec of ThmExtSyn.tdecl 
      | TerminatesDec of ThmExtSyn.tdecl 
      | WorldDec of ThmExtSyn.wdecl 
      | ReducesDec of ThmExtSyn.rdecl 
      | TabledDec of ThmExtSyn.tableddecl 
      | KeepTableDec of ThmExtSyn.keepTabledecl 
      | TheoremDec of ThmExtSyn.theoremdec 
      | ProveDec of ThmExtSyn.prove 
      | EstablishDec of ThmExtSyn.establish 
      | AssertDec of ThmExtSyn.assert__ 
      | Query of (int option * int option * ExtQuery.query) 
      | FQuery of ExtQuery.query 
      | Compile of Names.__Qid list 
      | Querytabled of (int option * int option * ExtQuery.query) 
      | Solve of (ExtQuery.define list * ExtQuery.solve) 
      | AbbrevDec of ExtConDec.condec 
      | TrustMe of (fileParseResult * Paths.region) 
      | SubordDec of (Names.__Qid * Names.__Qid) list 
      | FreezeDec of Names.__Qid list 
      | ThawDec of Names.__Qid list 
      | DeterministicDec of Names.__Qid list 
      | ClauseDec of ExtConDec.condec 
      | SigDef of ModExtSyn.sigdef 
      | StructDec of ModExtSyn.structdec 
      | Include of ModExtSyn.sigexp 
      | Open of ModExtSyn.strexp 
      | BeginSubsig 
      | EndSubsig 
      | Use of string 
    (* Further declarations to be added here *)
    val parseStream :
      TextIO.instream -> (fileParseResult * Paths.region) Stream.stream
    val parseTerminalQ : (string * string) -> ExtQuery.query Stream.stream
  end;;




(* Top-Level Parser *)
(* Author: Frank Pfenning *)
module Parser(Parser:sig
                       (*! structure Parsing' : PARSING !*)
                       module Stream' : STREAM
                       module ExtSyn' : EXTSYN
                       module Names' : NAMES
                       module ExtConDec' : EXTCONDEC
                       module ExtQuery' : EXTQUERY
                       module ExtModes' : EXTMODES
                       module ThmExtSyn' : THMEXTSYN
                       module ModExtSyn' : MODEXTSYN
                       module ParseConDec : PARSE_CONDEC
                       module ParseQuery : PARSE_QUERY
                       module ParseFixity : PARSE_FIXITY
                       module ParseMode : PARSE_MODE
                       module ParseThm : PARSE_THM
                       module ParseModule : PARSE_MODULE
                       (* result stream *)
                       (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
                       (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
                       (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
                       (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
                       (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
                       (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
                       (*! sharing ParseModule.Parsing = Parsing' !*)
                       module ParseTerm : PARSE_TERM
                     end) : PARSER =
  struct
    (*! structure Parsing = Parsing' !*)
    module Stream = Stream'
    module ExtSyn = ExtSyn'
    module Names = Names'
    module ExtConDec = ExtConDec'
    module ExtQuery = ExtQuery'
    module ExtModes = ExtModes'
    module ThmExtSyn = ThmExtSyn'
    module ModExtSyn = ModExtSyn'
    type fileParseResult =
      | ConDec of ExtConDec.condec 
      | FixDec of ((Names.__Qid * Paths.region) * Names.Fixity.fixity) 
      | NamePref of ((Names.__Qid * Paths.region) * (string list * string
      list)) 
      | ModeDec of ExtModes.modedec list 
      | UniqueDec of ExtModes.modedec list 
      | CoversDec of ExtModes.modedec list 
      | TotalDec of ThmExtSyn.tdecl 
      | TerminatesDec of ThmExtSyn.tdecl 
      | WorldDec of ThmExtSyn.wdecl 
      | ReducesDec of ThmExtSyn.rdecl 
      | TabledDec of ThmExtSyn.tableddecl 
      | KeepTableDec of ThmExtSyn.keepTabledecl 
      | TheoremDec of ThmExtSyn.theoremdec 
      | ProveDec of ThmExtSyn.prove 
      | EstablishDec of ThmExtSyn.establish 
      | AssertDec of ThmExtSyn.assert__ 
      | Query of (int option * int option * ExtQuery.query) 
      | FQuery of ExtQuery.query 
      | Compile of Names.__Qid list 
      | Querytabled of (int option * int option * ExtQuery.query) 
      | Solve of (ExtQuery.define list * ExtQuery.solve) 
      | AbbrevDec of ExtConDec.condec 
      | TrustMe of (fileParseResult * Paths.region) 
      | SubordDec of (Names.__Qid * Names.__Qid) list 
      | FreezeDec of Names.__Qid list 
      | ThawDec of Names.__Qid list 
      | DeterministicDec of Names.__Qid list 
      | ClauseDec of ExtConDec.condec 
      | SigDef of ModExtSyn.sigdef 
      | StructDec of ModExtSyn.structdec 
      | Include of ModExtSyn.sigexp 
      | Open of ModExtSyn.strexp 
      | BeginSubsig 
      | EndSubsig 
      | Use of string 
    (* Further pragmas to be added later here *)
    module __l = Lexer
    module LS = Lexer.Stream
    let rec stripDot =
      function
      | Cons ((L.DOT, r), s) -> s
      | Cons ((L.RPAREN, r), s) ->
          Parsing.error (r, "Unexpected right parenthesis")
      | Cons ((L.RBRACE, r), s) ->
          Parsing.error (r, "Unexpected right brace")
      | Cons ((L.RBRACKET, r), s) ->
          Parsing.error (r, "Unexpected right bracket")
      | Cons ((L.EOF, r), s) -> Parsing.error (r, "Unexpected end of file")
      | Cons ((L.EQUAL, r), s) -> Parsing.error (r, "Unexpected `='")
      | Cons ((t, r), s) ->
          Parsing.error (r, ((^) "Expected `.', found " L.toString t))
    let rec parseBound' =
      function
      | Cons ((ID (_, "*"), r), s') -> (None, s')
      | Cons ((ID (_, name), r), s') ->
          (try ((Some (L.stringToNat name)), s')
           with | Overflow -> Parsing.error (r, "Bound too large")
           | NotDigit _ ->
               Parsing.error
                 (r,
                   (("Bound `" ^ name) ^ "' neither `*' nor a natural number")))
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected bound `*' or natural number, found " L.toString
                 t))
    let rec recParse (s, recparser, theSigParser, sc) =
      Stream.delay
        (function
         | () -> recParse' ((LS.expose s), recparser, theSigParser, sc))
    let rec recParse' (f, recparser, theSigParser, sc) =
      match recparser f with
      | (Done x, f') -> sc (x, f')
      | (Continuation k, Cons ((L.LBRACE, r1), s')) ->
          let rec finish =
            function
            | Cons ((L.RBRACE, r2), s'') ->
                Stream.Cons
                  ((EndSubsig, r2), (recParse (s'', k, theSigParser, sc)))
            | Cons ((t, r), _) ->
                Parsing.error (r, ((^) "Expected `}', found " L.toString t)) in
          Stream.Cons ((BeginSubsig, r1), (theSigParser (s', finish)))
      | (Continuation _, Cons ((t, r), _)) ->
          Parsing.error (r, ((^) "Expected `{', found " L.toString t))
    let rec parseStream (s, sc) =
      Stream.delay (function | () -> parseStream' ((LS.expose s), sc))
    let rec parseStream' =
      function
      | ((Cons ((ID (idCase, name), r0), s') as f), sc) ->
          parseConDec' (f, sc)
      | ((Cons ((L.ABBREV, r), s') as f), sc) -> parseAbbrev' (f, sc)
      | ((Cons ((L.UNDERSCORE, r), s') as f), sc) -> parseConDec' (f, sc)
      | ((Cons ((L.INFIX, r), s') as f), sc) -> parseFixity' (f, sc)
      | ((Cons ((L.PREFIX, r), s') as f), sc) -> parseFixity' (f, sc)
      | ((Cons ((L.POSTFIX, r), s') as f), sc) -> parseFixity' (f, sc)
      | ((Cons ((L.NAME, r1), s') as f), sc) ->
          let (namePref, (Cons ((_, r2), _) as f')) =
            ParseFixity.parseNamePref' f in
          let r = Paths.join (r1, r2) in
          Stream.Cons
            (((NamePref namePref), r), (parseStream ((stripDot f'), sc)))
      | ((Cons ((L.DEFINE, r), s') as f), sc) -> parseSolve' (f, sc)
      | ((Cons ((L.SOLVE, r), s') as f), sc) -> parseSolve' (f, sc)
      | (Cons ((L.QUERY, r0), s'), sc) ->
          let (expected, s1) = parseBound' (LS.expose s') in
          let (try__, s2) = parseBound' (LS.expose s1) in
          let (query, (Cons ((_, r'), _) as f3)) =
            ParseQuery.parseQuery' (LS.expose s2) in
          let r = Paths.join (r0, r') in
          Stream.Cons
            (((Query (expected, try__, query)), r),
              (parseStream ((stripDot f3), sc)))
      | (Cons ((L.FQUERY, r0), s'), sc) ->
          let (query, (Cons ((_, r'), _) as f3)) =
            ParseQuery.parseQuery' (LS.expose s') in
          let r = Paths.join (r0, r') in
          Stream.Cons
            (((FQuery query), r), (parseStream ((stripDot f3), sc)))
      | (Cons ((L.QUERYTABLED, r0), s'), sc) ->
          let (numSol, s1) = parseBound' (LS.expose s') in
          let (try__, s2) = parseBound' (LS.expose s1) in
          let (query, (Cons ((_, r'), _) as f3)) =
            ParseQuery.parseQuery' (LS.expose s2) in
          let r = Paths.join (r0, r') in
          Stream.Cons
            (((Querytabled (numSol, try__, query)), r),
              (parseStream ((stripDot f3), sc)))
      | ((Cons ((L.MODE, r), s') as f), sc) -> parseMode' (f, sc)
      | ((Cons ((L.UNIQUE, r), s') as f), sc) -> parseUnique' (f, sc)
      | ((Cons ((L.COVERS, r), s') as f), sc) -> parseCovers' (f, sc)
      | ((Cons ((L.TOTAL, r), s') as f), sc) -> parseTotal' (f, sc)
      | ((Cons ((L.TERMINATES, r), s') as f), sc) -> parseTerminates' (f, sc)
      | ((Cons ((L.BLOCK, r), s') as f), sc) -> parseConDec' (f, sc)
      | ((Cons ((L.WORLDS, r), s') as f), sc) -> parseWorlds' (f, sc)
      | ((Cons ((L.REDUCES, r), s') as f), sc) -> parseReduces' (f, sc)
      | ((Cons ((L.TABLED, r), s') as f), sc) -> parseTabled' (f, sc)
      | ((Cons ((L.KEEPTABLE, r), s') as f), sc) -> parseKeepTable' (f, sc)
      | ((Cons ((L.THEOREM, r), s') as f), sc) -> parseTheorem' (f, sc)
      | ((Cons ((L.PROVE, r), s') as f), sc) -> parseProve' (f, sc)
      | ((Cons ((L.ESTABLISH, r), s') as f), sc) -> parseEstablish' (f, sc)
      | ((Cons ((L.ASSERT, r), s') as f), sc) -> parseAssert' (f, sc)
      | ((Cons ((L.TRUSTME, r), s') as f), sc) -> parseTrustMe' (f, sc)
      | ((Cons ((L.FREEZE, r), s') as f), sc) -> parseFreeze' (f, sc)
      | ((Cons ((L.SUBORD, r), s') as f), sc) -> parseSubord' (f, sc)
      | ((Cons ((L.THAW, r), s') as f), sc) -> parseThaw' (f, sc)
      | ((Cons ((L.DETERMINISTIC, r), s') as f), sc) ->
          parseDeterministic' (f, sc)
      | ((Cons ((L.COMPILE, r), s') as f), sc) -> parseCompile' (f, sc)
      | ((Cons ((L.CLAUSE, r), s') as f), sc) -> parseClause' (f, sc)
      | ((Cons ((L.SIG, r), s') as f), sc) -> parseSigDef' (f, sc)
      | ((Cons ((L.STRUCT, r), s') as f), sc) -> parseStructDec' (f, sc)
      | ((Cons ((L.INCLUDE, r), s') as f), sc) -> parseInclude' (f, sc)
      | ((Cons ((L.OPEN, r), s') as f), sc) -> parseOpen' (f, sc)
      | ((Cons ((L.USE, r), s') as f), sc) -> parseUse' ((LS.expose s'), sc)
      | ((Cons ((L.EOF, _), _) as f), sc) -> sc f
      | ((Cons ((L.RBRACE, _), _) as f), sc) -> sc f
      | (Cons ((t, r), s'), sc) ->
          Parsing.error
            (r,
              ((^) "Expected constant name or pragma keyword, found "
                 L.toString t))
    let rec parseConDec' ((Cons ((_, r0), _) as f), sc) =
      let (conDec, (Cons ((_, r'), _) as f')) = ParseConDec.parseConDec' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((ConDec conDec), r), (parseStream ((stripDot f'), sc)))
    let rec parseAbbrev' ((Cons ((_, r0), _) as f), sc) =
      let (conDec, (Cons ((_, r'), _) as f')) = ParseConDec.parseAbbrev' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((AbbrevDec conDec), r), (parseStream ((stripDot f'), sc)))
    let rec parseClause' ((Cons ((_, r0), _) as f), sc) =
      let (conDec, (Cons ((_, r'), _) as f')) = ParseConDec.parseClause' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((ClauseDec conDec), r), (parseStream ((stripDot f'), sc)))
    let rec parseFixity' ((Cons ((_, r0), _) as f), sc) =
      let (fdec, (Cons ((_, r'), _) as f')) = ParseFixity.parseFixity' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((FixDec fdec), r), (parseStream ((stripDot f'), sc)))
    let rec parseSolve' ((Cons ((_, r0), _) as f), sc) =
      let (defnssolve, (Cons ((_, r'), _) as f')) = ParseQuery.parseSolve' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((Solve defnssolve), r), (parseStream ((stripDot f'), sc)))
    let rec parseMode' ((Cons ((_, r0), _) as f), sc) =
      let (mdecs, (Cons ((_, r'), _) as f')) = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((ModeDec mdecs), r), (parseStream ((stripDot f'), sc)))
    let rec parseUnique' ((Cons ((_, r0), _) as f), sc) =
      let (mdecs, (Cons ((_, r'), _) as f')) = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((UniqueDec mdecs), r), (parseStream ((stripDot f'), sc)))
    let rec parseCovers' ((Cons ((_, r0), _) as f), sc) =
      let (mdecs, (Cons ((_, r'), _) as f')) = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((CoversDec mdecs), r), (parseStream ((stripDot f'), sc)))
    let rec parseTotal' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseTotal' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((TotalDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseTerminates' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseTerminates' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((TerminatesDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseReduces' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseReduces' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((ReducesDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseTabled' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseTabled' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((TabledDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseKeepTable' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseKeepTable' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((KeepTableDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseWorlds' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseWorlds' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((WorldDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseTheorem' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseTheoremDec' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((TheoremDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseProve' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseProve' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((ProveDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseEstablish' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseEstablish' f in
      let r = Paths.join (r0, r') in
      Stream.Cons
        (((EstablishDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseAssert' ((Cons ((_, r0), _) as f), sc) =
      let (ldec, (Cons ((_, r'), _) as f')) = ParseThm.parseAssert' f in
      let r = Paths.join (r0, r') in
      Stream.Cons (((AssertDec ldec), r), (parseStream ((stripDot f'), sc)))
    let rec parseTrustMe' ((Cons ((_, r0), s) as f), sc) =
      let rec parseNextDec' =
        function
        | Cons ((dec, r), s') -> Stream.Cons (((TrustMe (dec, r)), r0), s')
        | Stream.Empty ->
            Parsing.error (r0, "No declaration after `%trustme'") in
      parseNextDec' (parseStream' ((LS.expose s), sc))
    let rec parseSubord' ((Cons ((_, r0), s) as f), sc) =
      let (qidpairs, (Cons ((_, r'), _) as f')) =
        ParseTerm.parseSubord' (LS.expose s) in
      let r = Paths.join (r0, r') in
      let qidpairs =
        map (function | (qid1, qid2) -> ((Names.Qid qid1), (Names.Qid qid2)))
          qidpairs in
      Stream.Cons
        (((SubordDec qidpairs), r), (parseStream ((stripDot f'), sc)))
    let rec parseFreeze' ((Cons ((_, r0), s) as f), sc) =
      let (qids, (Cons ((_, r'), _) as f')) =
        ParseTerm.parseFreeze' (LS.expose s) in
      let r = Paths.join (r0, r') in
      let qids = map Names.Qid qids in
      Stream.Cons (((FreezeDec qids), r), (parseStream ((stripDot f'), sc)))
    let rec parseThaw' ((Cons ((_, r0), s) as f), sc) =
      let (qids, (Cons ((_, r'), _) as f')) =
        ParseTerm.parseThaw' (LS.expose s) in
      let r = Paths.join (r0, r') in
      let qids = map Names.Qid qids in
      Stream.Cons (((ThawDec qids), r), (parseStream ((stripDot f'), sc)))
    let rec parseDeterministic' ((Cons ((_, r0), s) as f), sc) =
      let (qids, (Cons ((_, r'), _) as f')) =
        ParseTerm.parseDeterministic' (LS.expose s) in
      let r = Paths.join (r0, r') in
      let qids = map Names.Qid qids in
      Stream.Cons
        (((DeterministicDec qids), r), (parseStream ((stripDot f'), sc)))
    let rec parseCompile' ((Cons ((_, r0), s) as f), sc) =
      let (qids, (Cons ((_, r'), _) as f')) =
        ParseTerm.parseCompile' (LS.expose s) in
      let r = Paths.join (r0, r') in
      let qids = map Names.Qid qids in
      Stream.Cons (((Compile qids), r), (parseStream ((stripDot f'), sc)))
    let rec parseSigDef' ((Cons ((_, r1), _) as f), sc) =
      let rec finish (sigdef, (Cons ((_, r2), _) as f')) =
        Stream.Cons
          (((SigDef sigdef), (Paths.join (r1, r2))),
            (parseStream ((stripDot f'), sc))) in
      recParse' (f, ParseModule.parseSigDef', parseStream, finish)
    let rec parseStructDec' ((Cons ((_, r1), _) as f), sc) =
      let rec finish (structdec, (Cons ((_, r2), _) as f')) =
        Stream.Cons
          (((StructDec structdec), (Paths.join (r1, r2))),
            (parseStream ((stripDot f'), sc))) in
      recParse' (f, ParseModule.parseStructDec', parseStream, finish)
    let rec parseInclude' ((Cons ((_, r1), _) as f), sc) =
      let rec finish (sigexp, (Cons ((_, r2), _) as f')) =
        Stream.Cons
          (((Include sigexp), (Paths.join (r1, r2))),
            (parseStream ((stripDot f'), sc))) in
      recParse' (f, ParseModule.parseInclude', parseStream, finish)
    let rec parseOpen' ((Cons ((_, r1), _) as f), sc) =
      let (strexp, (Cons ((_, r2), _) as f')) = ParseModule.parseOpen' f in
      Stream.Cons
        (((Open strexp), (Paths.join (r1, r2))),
          (parseStream ((stripDot f'), sc)))
    let rec parseUse' =
      function
      | (Cons ((ID (_, name), r0), s), sc) ->
          let Cons ((_, r'), _) as f = LS.expose s in
          let r = Paths.join (r0, r') in
          Stream.Cons (((Use name), r), (parseStream ((stripDot f), sc)))
      | (Cons ((_, r), _), sc) ->
          Parsing.error (r, "Constraint solver name expected")
    let rec parseQ s = Stream.delay (function | () -> parseQ' (LS.expose s))
    let rec parseQ' f =
      let (query, f') = ParseQuery.parseQuery' f in
      Stream.Cons (query, (parseQ (stripDot f')))
    let rec parseTLStream instream =
      let rec finish =
        function
        | Cons ((L.EOF, r), s) -> Stream.Empty
        | Cons ((L.RBRACE, r), s) -> Parsing.error (r, "Unmatched `}'") in
      parseStream ((L.lexStream instream), finish)
    (* Everything else should be impossible *)
    (*
    fun stripOptionalDot (LS.Cons ((L.DOT,r), s)) = s
      | stripOptionalDot f = LS.delay (fn () => f)
    *)
    (* pass parseStream as theSigParser in order to be able to use
       this function polymorphically in the definition of parseStream *)
    (* parseStream' : lexResult front -> fileParseResult front *)
    (* parseStream' switches between various specialized parsers *)
    (* -fp *)
    (* -cs *)
    (* -bp *)
    (* -bp *)
    (* -bp *)
    (* -rv *)
    (* -ABP 4/4/03 *)
    (* -fp *)
    (* ABP 4/4/03 *)
    let parseStream = parseTLStream
    let rec parseTerminalQ prompts = parseQ (L.lexTerminal prompts)
  end ;;
