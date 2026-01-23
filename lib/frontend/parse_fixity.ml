module type PARSE_FIXITY  =
  sig
    module Names : NAMES
    val parseFixity' :
      ((Names.qid_ * Paths.region) * Names.Fixity.fixity) Parsing.parser
    val parseNamePref' :
      ((Names.qid_ * Paths.region) * (string list * string list))
        Parsing.parser
  end


module ParseFixity(ParseFixity:sig module Names' : NAMES end) : PARSE_FIXITY
  =
  struct
    module Names = Names'
    module L = Lexer
    module LS = Lexer.Stream
    module FX = Names.Fixity
    let rec fixToString (Strength p) = Int.toString p
    let rec idToPrec (r, (_, name)) =
      let prec =
        begin try FX.Strength (L.stringToNat name)
        with | Overflow -> Parsing.error (r, "Precedence too large")
        | NotDigit _ -> Parsing.error (r, "Precedence not a natural number") end in
    if (FX.less (prec, FX.minPrec)) || (FX.less (FX.maxPrec, prec))
    then
      begin Parsing.error
              (r,
                (((^) (((^) "Precedence out of range [" fixToString
                          FX.minPrec)
                         ^ ",")
                    fixToString FX.maxPrec)
                   ^ "]")) end
      else begin prec end
let rec parseFixCon =
  begin function
  | (fixity, Cons ((ID (_, name), r), s')) ->
      ((((Names.Qid ([], name)), r), fixity), (LS.expose s'))
  | (fixity, Cons ((t, r), s')) ->
      Parsing.error
        (r,
          ((^) "Expected identifier to assign fixity, found " L.toString t)) end
let rec parseFixPrec =
  begin function
  | (fixity, Cons ((ID id, r), s')) ->
      parseFixCon ((fixity (idToPrec (r, id))), (LS.expose s'))
  | (fixity, Cons ((t, r), s')) ->
      Parsing.error (r, ((^) "Expected precedence, found " L.toString t)) end
let rec parseInfix =
  begin function
  | Cons ((ID (L.Lower, "none"), r), s') ->
      parseFixPrec ((begin function | p -> FX.Infix (p, FX.None) end),
        (LS.expose s'))
  | Cons ((ID (L.Lower, "left"), r), s') ->
      parseFixPrec ((begin function | p -> FX.Infix (p, FX.Left) end),
        (LS.expose s'))
  | Cons ((ID (L.Lower, "right"), r), s') ->
      parseFixPrec ((begin function | p -> FX.Infix (p, FX.Right) end),
        (LS.expose s'))
| Cons ((t, r), s') ->
    Parsing.error
      (r,
        ((^) "Expected associatitivy `left', `right', or `none', found "
           L.toString t)) end
let rec parsePrefix f = parseFixPrec (FX.Prefix, f)
let rec parsePostfix f = parseFixPrec (FX.Postfix, f)
let rec parseFixity' =
  begin function
  | Cons ((L.INFIX, r), s') -> parseInfix (LS.expose s')
  | Cons ((L.PREFIX, r), s') -> parsePrefix (LS.expose s')
  | Cons ((L.POSTFIX, r), s') -> parsePostfix (LS.expose s') end
let rec parseFixity s = parseFixity' (LS.expose s)
let rec parseName5 =
  begin function
  | (name, r0, prefENames, prefUNames, Cons ((ID (_, prefUName), r), s')) ->
      parseName5
        (name, r0, prefENames, (prefUNames @ [prefUName]), (LS.expose s'))
  | (name, r0, prefENames, prefUNames, Cons ((L.RPAREN, r), s')) ->
      ((((Names.Qid ([], name)), r0), (prefENames, prefUNames)),
        (LS.expose s'))
  | (name, r0, prefENames, prefUNames, Cons ((t, r), s')) ->
      Parsing.error
        (r, ((^) "Expected name preference or ')', found " L.toString t)) end
(* prefUName should be lower case---not enforced *)
let rec parseName3 =
  begin function
  | (name, r0, prefEName, Cons ((ID (_, prefUName), r), s')) ->
      ((((Names.Qid ([], name)), r0), (prefEName, [prefUName])),
        (LS.expose s'))
  | (name, r0, prefEName, Cons ((L.LPAREN, r), s')) ->
      parseName5 (name, r0, prefEName, [], (LS.expose s'))
  | (name, r0, prefEName, f) ->
      ((((Names.Qid ([], name)), r0), (prefEName, [])), f) end(* prefUName should be lower case---not enforced *)
let rec parseName4 =
  begin function
  | (name, r0, prefENames, Cons ((ID (_, prefEName), r), s')) ->
      if L.isUpper prefEName
      then
        begin parseName4
                (name, r0, (prefENames @ [prefEName]), (LS.expose s')) end
      else begin
        Parsing.error
          (r, ("Expected uppercase identifer, found " ^ prefEName)) end
  | (name, r0, prefENames, Cons ((L.RPAREN, r), s')) ->
      parseName3 (name, r0, prefENames, (LS.expose s'))
  | (name, r0, prefENames, Cons ((t, r), s')) ->
      Parsing.error
        (r, ((^) "Expected name preference or ')', found " L.toString t)) end
let rec parseName2 =
  begin function
  | (name, r0, Cons ((ID (_, prefEName), r), s')) ->
      if L.isUpper prefEName
      then begin parseName3 (name, r0, [prefEName], (LS.expose s')) end
      else begin
        Parsing.error
          (r, ("Expected uppercase identifer, found " ^ prefEName)) end
  | (name, r0, Cons ((L.LPAREN, r), s')) ->
      parseName4 (name, r0, [], (LS.expose s'))
  | (name, r0, Cons ((t, r), s')) ->
      Parsing.error
        (r, ((^) "Expected name preference, found " L.toString t)) end
let rec parseName1 =
  begin function
  | Cons ((ID (_, name), r), s') -> parseName2 (name, r, (LS.expose s'))
  | Cons ((t, r), s') ->
      Parsing.error
        (r,
          ((^) "Expected identifer to assign name preference, found "
             L.toString t)) end
let rec parseNamePref' (Cons ((L.NAME, r), s')) = parseName1 (LS.expose s')
let rec parseNamePref s = parseNamePref' (LS.expose s)
let parseFixity' = parseFixity'
let parseNamePref' = parseNamePref' end
