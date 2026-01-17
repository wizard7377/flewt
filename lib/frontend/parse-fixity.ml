
module type PARSE_FIXITY  =
  sig
    module Names :
    ((NAMES)(* Parsing Fixity Declarations *)(* Author: Frank Pfenning *)
    (*! structure Parsing : PARSING !*))
    val parseFixity' :
      ((Names.__Qid * Paths.region) * Names.Fixity.fixity) Parsing.parser
    val parseNamePref' :
      ((Names.__Qid * Paths.region) * (string list * string list))
        Parsing.parser
  end;;




module ParseFixity(ParseFixity:sig
                                 module Names' :
                                 ((NAMES)(* Parsing Fixity and Name Preference Declarations *)
                                 (* Author: Frank Pfenning *)(*! structure Parsing' : PARSING !*))
                               end) : PARSE_FIXITY =
  struct
    module Names =
      ((Names')(*! structure Parsing = Parsing' !*))
    module L = Lexer
    module LS = Lexer.Stream
    module FX = Names.Fixity
    let rec fixToString (Strength p) = Int.toString p
    let rec idToPrec (r, (_, name)) =
      let prec =
        try FX.Strength (L.stringToNat name)
        with | Overflow -> Parsing.error (r, "Precedence too large")
        | NotDigit _ -> Parsing.error (r, "Precedence not a natural number") in
      if (FX.less (prec, FX.minPrec)) || (FX.less (FX.maxPrec, prec))
      then
        Parsing.error
          (r,
            (((^) (((^) "Precedence out of range [" fixToString FX.minPrec) ^
                     ",")
                fixToString FX.maxPrec)
               ^ "]"))
      else prec
    let rec parseFixCon =
      function
      | (fixity, Cons ((ID (_, name), r), s')) ->
          ((((Names.Qid (nil, name)), r), fixity), (LS.expose s'))
      | (fixity, Cons ((t, r), s')) ->
          Parsing.error
            (r,
              ((^) "Expected identifier to assign fixity, found " L.toString
                 t))
    let rec parseFixPrec =
      function
      | (fixity, Cons ((ID id, r), s')) ->
          parseFixCon ((fixity (idToPrec (r, id))), (LS.expose s'))
      | (fixity, Cons ((t, r), s')) ->
          Parsing.error (r, ((^) "Expected precedence, found " L.toString t))
    let rec parseInfix =
      function
      | Cons ((ID (L.Lower, "none"), r), s') ->
          parseFixPrec
            ((function | p -> FX.Infix (p, FX.None)), (LS.expose s'))
      | Cons ((ID (L.Lower, "left"), r), s') ->
          parseFixPrec
            ((function | p -> FX.Infix (p, FX.Left)), (LS.expose s'))
      | Cons ((ID (L.Lower, "right"), r), s') ->
          parseFixPrec
            ((function | p -> FX.Infix (p, FX.Right)), (LS.expose s'))
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected associatitivy `left', `right', or `none', found "
                 L.toString t))
    let rec parsePrefix f = parseFixPrec (FX.Prefix, f)
    let rec parsePostfix f = parseFixPrec (FX.Postfix, f)
    let rec parseFixity' =
      function
      | Cons ((L.INFIX, r), s') -> parseInfix (LS.expose s')
      | Cons ((L.PREFIX, r), s') -> parsePrefix (LS.expose s')
      | Cons ((L.POSTFIX, r), s') -> parsePostfix (LS.expose s')
    let rec parseFixity s = parseFixity' (LS.expose s)
    let rec parseName5 =
      function
      | (name, r0, prefENames, prefUNames, Cons ((ID (_, prefUName), r), s'))
          ->
          parseName5
            (name, r0, prefENames, (prefUNames @ [prefUName]),
              (LS.expose s'))
      | (name, r0, prefENames, prefUNames, Cons ((L.RPAREN, r), s')) ->
          ((((Names.Qid (nil, name)), r0), (prefENames, prefUNames)),
            (LS.expose s'))
      | (name, r0, prefENames, prefUNames, Cons ((t, r), s')) ->
          Parsing.error
            (r, ((^) "Expected name preference or ')', found " L.toString t))
    let rec parseName3 =
      function
      | (name, r0, prefEName, Cons ((ID (_, prefUName), r), s')) ->
          ((((Names.Qid (nil, name)), r0), (prefEName, [prefUName])),
            (LS.expose s'))
      | (name, r0, prefEName, Cons ((L.LPAREN, r), s')) ->
          parseName5 (name, r0, prefEName, nil, (LS.expose s'))
      | (name, r0, prefEName, f) ->
          ((((Names.Qid (nil, name)), r0), (prefEName, nil)), f)
    let rec parseName4 =
      function
      | (name, r0, prefENames, Cons ((ID (_, prefEName), r), s')) ->
          if L.isUpper prefEName
          then
            parseName4 (name, r0, (prefENames @ [prefEName]), (LS.expose s'))
          else
            Parsing.error
              (r, ("Expected uppercase identifer, found " ^ prefEName))
      | (name, r0, prefENames, Cons ((L.RPAREN, r), s')) ->
          parseName3 (name, r0, prefENames, (LS.expose s'))
      | (name, r0, prefENames, Cons ((t, r), s')) ->
          Parsing.error
            (r, ((^) "Expected name preference or ')', found " L.toString t))
    let rec parseName2 =
      function
      | (name, r0, Cons ((ID (_, prefEName), r), s')) ->
          if L.isUpper prefEName
          then parseName3 (name, r0, [prefEName], (LS.expose s'))
          else
            Parsing.error
              (r, ("Expected uppercase identifer, found " ^ prefEName))
      | (name, r0, Cons ((L.LPAREN, r), s')) ->
          parseName4 (name, r0, nil, (LS.expose s'))
      | (name, r0, Cons ((t, r), s')) ->
          Parsing.error
            (r, ((^) "Expected name preference, found " L.toString t))
    let rec parseName1 =
      function
      | Cons ((ID (_, name), r), s') -> parseName2 (name, r, (LS.expose s'))
      | Cons ((t, r), s') ->
          Parsing.error
            (r,
              ((^) "Expected identifer to assign name preference, found "
                 L.toString t))
    let rec parseNamePref' (Cons ((L.NAME, r), s')) =
      parseName1 (LS.expose s')
    let rec parseNamePref s = parseNamePref' (LS.expose s)
    let ((parseFixity')(* some shorthands *)(* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *)
      (*-----------------------------*)(* Parsing fixity declarations *)
      (*-----------------------------*)(* parseFixCon "id" *)
      (* parseFixPrec "n id" where n is precedence *)
      (* parseInfix "none|left|right n id" where n is precedence *)
      (* parsePrefix "n id" where n is precedence *)
      (* parsePostfix "n id" where n is precedence *)
      (* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *)
      (* anything else should be impossible *)(*------------------------------------*)
      (* Parsing name preferences %name ... *)(*------------------------------------*)
      (* parseName5 "string ... )" or ")" *)(* prefUName should be lower case---not enforced *)
      (* parseName3 "string" or "" *)(* prefUName should be lower case---not enforced *)
      (* parseName4 "string ... )" or ")" *)(* parseName2 "string" or "string string"
              or "(string ... ) string"  or " string (string ...)"
              or "(string ... ) (string ...)" *)
      (* parseName1 "id string" or "id string string" *)
      (* parseNamePref' "%name id string" or "%name id string string"
       Invariant: token stream starts with %name
    *))
      = parseFixity'
    let parseNamePref' = parseNamePref'
  end ;;
