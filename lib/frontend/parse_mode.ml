module type PARSE_MODE  =
  sig
    module ExtModes : EXTMODES
    val parseMode' : ExtModes.modedec list Parsing.parser
  end


module ParseMode(ParseMode:sig
                             module ExtModes' : EXTMODES
                             module ParseTerm : PARSE_TERM
                           end) : PARSE_MODE =
  struct
    module ExtModes = ExtModes'
    module L = Lexer
    module LS = Lexer.Stream
    module E = ExtModes
    module P = Paths
    let rec extract (s, i) = if (=) i String.size s then begin None end
      else begin Some (String.extract (s, i, None)) end
  let rec splitModeId (r, id) =
    begin match String.sub (id, 0) with
    | '*' -> ((E.star r), (extract (id, 1)))
    | '-' ->
        if ((String.size id) > 1) && ((String.sub (id, 1)) = '1')
        then begin ((E.minus1 r), (extract (id, 2))) end
        else begin ((E.minus r), (extract (id, 1))) end
    | '+' -> ((E.plus r), (extract (id, 1)))
    | _ ->
        Parsing.error
          (r, ("Expected mode `+', `-', `*', or `-1'  found " ^ id)) end
let rec validateMArg =
  begin function
  | (r, ((mode, Some id) as mId)) -> if L.isUpper id then begin mId end
      else begin
        Parsing.error (r, ("Expected free uppercase variable, found " ^ id)) end
  | (r, (_, None)) -> Parsing.error (r, "Missing variable following mode") end
let rec validateMode =
  begin function
  | (r, (mode, None)) -> mode
  | (r, (_, Some id)) ->
      Parsing.error
        (r,
          ("Expected simple mode, found mode followed by identifier " ^ id)) end
let rec stripRParen =
  begin function
  | Cons ((L.RPAREN, r), s') -> ((LS.expose s'), r)
  | Cons ((t, r), s') ->
      Parsing.error (r, ((^) "Expected closing `)', found " L.toString t)) end
(* t = `.' or ? *)
let rec stripRBrace =
  begin function
  | Cons ((L.RBRACE, r), s') -> ((LS.expose s'), r)
  | Cons ((t, r), _) ->
      Parsing.error (r, ((^) "Expected `}', found " L.toString t)) end
let rec parseShortSpine =
  begin function
  | Cons ((L.DOT, r), s') as f -> ((E.Short.mnil r), f)
  | Cons ((L.RPAREN, r), s') as f -> ((E.Short.mnil r), f)
  | Cons ((ID (_, id), r), s') ->
      let mId = validateMArg (r, (splitModeId (r, id))) in
      let (mS', f') = parseShortSpine (LS.expose s') in
      ((E.Short.mapp (mId, mS')), f')
  | Cons ((t, r), s') ->
      Parsing.error (r, ((^) "Expected mode or `.', found " L.toString t)) end
let rec parseFull =
  begin function
  | (Cons (((ID (c, id), r0) as t0), s'), r1) ->
      (((begin match LS.expose s' with
         | Cons ((L.LBRACE, r), s'') ->
             let mId = splitModeId (r0, id) in
             let m = validateMode (r0, mId) in
             let ((x, yOpt), f') = ParseTerm.parseDec' (LS.expose s'') in
             let (f'', r') = stripRBrace f' in
             let dec =
               begin match yOpt with
               | None -> ParseTerm.ExtSyn.dec0 (x, (P.join (r, r')))
               | Some y -> ParseTerm.ExtSyn.dec (x, y, (P.join (r, r'))) end in
             let (t', f''') = parseFull (f'', r1) in
             ((E.Full.mpi (m, dec, t')), f''')
      | Cons (TS) ->
          let (t', (Cons ((_, r), s') as f')) =
            ParseTerm.parseTerm' (LS.Cons (t0, (LS.cons TS))) in
          ((E.Full.mroot (t', (P.join (r, r1)))), f') end))
  (* found quantifier --- id must be mode *)(* no quantifier --- parse atomic type *))
  | (Cons ((L.LPAREN, r0), s'), r1) ->
      let (t', f') = ParseTerm.parseTerm' (LS.expose s') in
      let (f'', r') = stripRParen f' in
      ((E.Full.mroot (t', (P.join (r', r1)))), f'')
  | (Cons ((t, r), s'), _) ->
      Parsing.error
        (r, ((^) "Expected mode or identifier, found " L.toString t)) end
(* Left paren --- parse atomic type *)(* Look ahead one token to decide if quantifier follows *)
let rec parseMode2 =
  begin function
  | (lexid, Cons (((L.LBRACE, r), s') as BS), r1) ->
      let (t', f') = parseFull ((LS.Cons (lexid, (LS.cons BS))), r1) in
      ((E.Full.toModedec t'), f')
  | ((ID (_, name), r), f, _) ->
      let (mS', f') = parseShortSpine f in
      ((E.Short.toModedec (E.Short.mroot ([], name, r, mS'))), f') end
let rec parseModeParen =
  begin function
  | (Cons ((ID (_, name), r0), s'), r) ->
      let (mS', f') = parseShortSpine (LS.expose s') in
      let (f'', r') = stripRParen f' in
      ((E.Short.toModedec (E.Short.mroot ([], name, (P.join (r, r')), mS'))),
        f'')
  | (Cons ((t, r), s'), _) ->
      Parsing.error (r, ((^) "Expected identifier, found " L.toString t)) end
let rec parseMode1 =
  begin function
  | Cons (((ID _, r) as lexid), s') ->
      parseModeNext (parseMode2 (lexid, (LS.expose s'), r))
  | Cons ((L.LPAREN, r), s') ->
      parseModeNext (parseModeParen ((LS.expose s'), r))
  | Cons ((t, r), _) ->
      Parsing.error
        (r, ((^) "Expected identifier or mode, found " L.toString t)) end
let rec parseModeNext =
  begin function
  | (modedec, (Cons ((L.DOT, _), s') as f)) -> ((modedec :: []), f)
  | (modedec, f) ->
      let (mdecs, f') = parseMode1 f in ((modedec :: mdecs), f') end
let rec parseMode' =
  begin function
  | Cons ((L.MODE, r), s') -> parseMode1 (LS.expose s')
  | Cons ((L.UNIQUE, r), s') -> parseMode1 (LS.expose s')
  | Cons ((L.COVERS, r), s') -> parseMode1 (LS.expose s') end
let parseMode' = parseMode' end
