
(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)
module type PARSE_MODE  =
  sig
    (*! structure Parsing : PARSING !*)
    module ExtModes : EXTMODES
    val parseMode' : ExtModes.modedec list Parsing.parser
  end;;




(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)
module ParseMode(ParseMode:sig
                             (*! structure Paths : PATHS !*)
                             (*! structure Parsing' : PARSING !*)
                             (*! sharing Parsing'.Lexer.Paths = Paths !*)
                             module ExtModes' : EXTMODES
                             (*! sharing ExtModes'.Paths = Paths !*)
                             (*! sharing ExtModes'.ExtSyn.Paths = Paths !*)
                             module ParseTerm : PARSE_TERM
                           end) : PARSE_MODE =
  struct
    (*! structure Parsing = Parsing' !*)
    module ExtModes = ExtModes'
    module L = Lexer
    module LS = Lexer.Stream
    module E = ExtModes
    module P = Paths
    let rec extract (s, i) =
      if (=) i String.size s
      then NONE
      else SOME (String.extract (s, i, NONE))
    let rec splitModeId (r, id) =
      match String.sub (id, 0) with
      | '*' -> ((E.star r), (extract (id, 1)))
      | '-' ->
          if ((String.size id) > 1) && ((String.sub (id, 1)) = '1')
          then ((E.minus1 r), (extract (id, 2)))
          else ((E.minus r), (extract (id, 1)))
      | '+' -> ((E.plus r), (extract (id, 1)))
      | _ ->
          Parsing.error
            (r, ("Expected mode `+', `-', `*', or `-1'  found " ^ id))
    let rec validateMArg =
      function
      | (r, ((mode, SOME id) as mId)) ->
          if L.isUpper id
          then mId
          else
            Parsing.error
              (r, ("Expected free uppercase variable, found " ^ id))
      | (r, (_, NONE)) ->
          Parsing.error (r, "Missing variable following mode")
    let rec validateMode =
      function
      | (r, (mode, NONE)) -> mode
      | (r, (_, SOME id)) ->
          Parsing.error
            (r,
              ("Expected simple mode, found mode followed by identifier " ^
                 id))
    let rec stripRParen =
      function
      | Cons ((L.RPAREN, r), s') -> ((LS.expose s'), r)
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected closing `)', found " L.toString t))
    let rec stripRBrace =
      function
      | Cons ((L.RBRACE, r), s') -> ((LS.expose s'), r)
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `}', found " L.toString t))
    let rec parseShortSpine =
      function
      | Cons ((L.DOT, r), s') as f -> ((E.Short.mnil r), f)
      | Cons ((L.RPAREN, r), s') as f -> ((E.Short.mnil r), f)
      | Cons ((ID (_, id), r), s') ->
          let mId = validateMArg (r, (splitModeId (r, id))) in
          let (mS', f') = parseShortSpine (LS.expose s') in
          ((E.Short.mapp (mId, mS')), f')
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected mode or `.', found " L.toString t))
    let rec parseFull =
      function
      | (Cons (((ID (c, id), r0) as t0), s'), r1) ->
          (match LS.expose s' with
           | Cons ((L.LBRACE, r), s'') ->
               let mId = splitModeId (r0, id) in
               let m = validateMode (r0, mId) in
               let ((x, yOpt), f') = ParseTerm.parseDec' (LS.expose s'') in
               let (f'', r') = stripRBrace f' in
               let dec =
                 match yOpt with
                 | NONE -> ParseTerm.ExtSyn.dec0 (x, (P.join (r, r')))
                 | SOME y -> ParseTerm.ExtSyn.dec (x, y, (P.join (r, r'))) in
               let (t', f''') = parseFull (f'', r1) in
               ((E.Full.mpi (m, dec, t')), f''')
           | Cons (TS) ->
               let (t', (Cons ((_, r), s') as f')) =
                 ParseTerm.parseTerm' (LS.Cons (t0, (LS.cons TS))) in
               ((E.Full.mroot (t', (P.join (r, r1)))), f'))
      | (Cons ((L.LPAREN, r0), s'), r1) ->
          let (t', f') = ParseTerm.parseTerm' (LS.expose s') in
          let (f'', r') = stripRParen f' in
          ((E.Full.mroot (t', (P.join (r', r1)))), f'')
      | (Cons ((t, r), s'), _) ->
          Parsing.error
            (r, ((^) "Expected mode or identifier, found " L.toString t))
    let rec parseMode2 =
      function
      | (lexid, Cons (((L.LBRACE, r), s') as BS), r1) ->
          let (t', f') = parseFull ((LS.Cons (lexid, (LS.cons BS))), r1) in
          ((E.Full.toModedec t'), f')
      | ((ID (_, name), r), f, _) ->
          let (mS', f') = parseShortSpine f in
          ((E.Short.toModedec (E.Short.mroot (nil, name, r, mS'))), f')
    let rec parseModeParen =
      function
      | (Cons ((ID (_, name), r0), s'), r) ->
          let (mS', f') = parseShortSpine (LS.expose s') in
          let (f'', r') = stripRParen f' in
          ((E.Short.toModedec
              (E.Short.mroot (nil, name, (P.join (r, r')), mS'))), f'')
      | (Cons ((t, r), s'), _) ->
          Parsing.error (r, ((^) "Expected identifier, found " L.toString t))
    let rec parseMode1 =
      function
      | Cons (((ID _, r) as lexid), s') ->
          parseModeNext (parseMode2 (lexid, (LS.expose s'), r))
      | Cons ((L.LPAREN, r), s') ->
          parseModeNext (parseModeParen ((LS.expose s'), r))
      | Cons ((t, r), _) ->
          Parsing.error
            (r, ((^) "Expected identifier or mode, found " L.toString t))
    let rec parseModeNext =
      function
      | (modedec, (Cons ((L.DOT, _), s') as f)) -> ((modedec :: nil), f)
      | (modedec, f) ->
          let (mdecs, f') = parseMode1 f in ((modedec :: mdecs), f')
    let rec parseMode' =
      function
      | Cons ((L.MODE, r), s') -> parseMode1 (LS.expose s')
      | Cons ((L.UNIQUE, r), s') -> parseMode1 (LS.expose s')
      | Cons ((L.COVERS, r), s') -> parseMode1 (LS.expose s')
    (* extract (s, i) = substring of s starting at index i
       Effect: raises Subscript if i > |s|
    *)
    (* splitModeId (r, id) = (mode, idOpt) where id = "<mode><idOpt>"
       Invariant: id <> ""
    *)
    (* t = `.' or ? *)
    (* parseShortSpine "modeid ... modeid." *)
    (* parseFull "mode {id:term} ... mode {x:term} term" *)
    (* Look ahead one token to decide if quantifier follows *)
    (* found quantifier --- id must be mode *)
    (* no quantifier --- parse atomic type *)
    (* Left paren --- parse atomic type *)
    (* parseMode2 switches between full and short mode declarations *)
    (* lexid could be mode or other identifier *)
    (* parseMode1 parses mdecl *)
    (* parseMode' : lexResult front -> modedec * lexResult front
       Invariant: exposed input stream starts with MODE
    *)
    let parseMode' = parseMode'
  end ;;
