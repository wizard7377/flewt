
module type LEXER  =
  sig
    module Stream : STREAM
    type __IdCase =
      | Upper 
      | Lower 
      | Quoted 
    type __Token =
      | EOF 
      | DOT 
      | PATHSEP 
      | COLON 
      | LPAREN 
      | RPAREN 
      | LBRACKET 
      | RBRACKET 
      | LBRACE 
      | RBRACE 
      | BACKARROW 
      | ARROW 
      | TYPE 
      | EQUAL 
      | ID of (__IdCase * string) 
      | UNDERSCORE 
      | INFIX 
      | PREFIX 
      | POSTFIX 
      | NAME 
      | DEFINE 
      | SOLVE 
      | QUERY 
      | FQUERY 
      | COMPILE 
      | QUERYTABLED 
      | MODE 
      | UNIQUE 
      | COVERS 
      | TOTAL 
      | TERMINATES 
      | BLOCK 
      | WORLDS 
      | REDUCES 
      | TABLED 
      | KEEPTABLE 
      | THEOREM 
      | PROVE 
      | ESTABLISH 
      | ASSERT 
      | ABBREV 
      | TRUSTME 
      | FREEZE 
      | THAW 
      | SUBORD 
      | DETERMINISTIC 
      | CLAUSE 
      | SIG 
      | STRUCT 
      | WHERE 
      | INCLUDE 
      | OPEN 
      | USE 
      | STRING of string 
    exception Error of string 
    val lexStream : TextIO.instream -> (__Token * Paths.region) Stream.stream
    val lexTerminal :
      string -> string -> (__Token * Paths.region) Stream.stream
    val toString : __Token -> string
    exception NotDigit of char 
    val stringToNat : string -> int
    val isUpper : string -> bool
  end;;




module Lexer(Lexer:sig module Stream' : STREAM end) : LEXER =
  struct
    module Stream = Stream'
    module P = Paths
    type __IdCase =
      | Upper 
      | Lower 
      | Quoted 
    type __Token =
      | EOF 
      | DOT 
      | PATHSEP 
      | COLON 
      | LPAREN 
      | RPAREN 
      | LBRACKET 
      | RBRACKET 
      | LBRACE 
      | RBRACE 
      | BACKARROW 
      | ARROW 
      | TYPE 
      | EQUAL 
      | ID of (__IdCase * string) 
      | UNDERSCORE 
      | INFIX 
      | PREFIX 
      | POSTFIX 
      | NAME 
      | DEFINE 
      | SOLVE 
      | QUERY 
      | FQUERY 
      | COMPILE 
      | QUERYTABLED 
      | MODE 
      | UNIQUE 
      | COVERS 
      | TOTAL 
      | TERMINATES 
      | REDUCES 
      | TABLED 
      | KEEPTABLE 
      | THEOREM 
      | BLOCK 
      | WORLDS 
      | PROVE 
      | ESTABLISH 
      | ASSERT 
      | ABBREV 
      | TRUSTME 
      | FREEZE 
      | THAW 
      | SUBORD 
      | DETERMINISTIC 
      | CLAUSE 
      | SIG 
      | STRUCT 
      | WHERE 
      | INCLUDE 
      | OPEN 
      | USE 
      | STRING of string 
    exception Error of string 
    let rec error r msg = raise (Error (P.wrap (r, msg)))
    let (isSym : char -> bool) = Char.contains "_!&$^+/<=>?@~|#*`;,-\\"
    let rec isUTF8 c = not (Char.isAscii c)
    let rec isQuote c = c = '\''
    let rec isIdChar c =
      (Char.isLower c) ||
        ((Char.isUpper c) ||
           ((Char.isDigit c) || ((isSym c) || ((isQuote c) || (isUTF8 c)))))
    let rec stringToToken __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Lower, "<-", r) -> (BACKARROW, r)
      | (Lower, "->", r) -> (ARROW, r)
      | (Upper, "_", r) -> (UNDERSCORE, r)
      | (Lower, "=", r) -> (EQUAL, r)
      | (Lower, "type", r) -> (TYPE, r)
      | (idCase, s, r) -> ((ID (idCase, s)), r)
    let rec lex inputFun =
      let s = ref ""
      and left = ref 0
      and right = ref 0 in
      let _ = P.resetLines () in
      let EOFString = String.str '\004' in
      let rec readNext () =
        let nextLine = inputFun (!right) in
        let nextSize = String.size nextLine in
        ((if nextSize = 0
          then
            (((s := EOFString;
               (!) ((:=) left) right;
               ((!) ((:=) right) right) + 1))
            (* fake EOF character string *))
          else
            (s := nextLine;
             (!) ((:=) left) right;
             ((!) ((:=) right) right) + nextSize;
             P.newLine (!left)))
          (* end of file? *)(* remember new line position *)) in
      let rec char i =
        if (!) ((>=) i) right
        then (readNext (); char i)
        else String.sub ((!s), ((!) ((-) i) left)) in
      let rec string i j =
        String.substring ((!s), ((!) ((-) i) left), (j - i)) in
      let rec idToToken idCase (Reg (i, j)) =
        stringToToken (idCase, (string (i, j)), (P.Reg (i, j))) in
      let rec qidToToken (Reg (i, j)) =
        ((ID (Lower, (string (i, (j + 1))))), (P.Reg (i, (j + 1)))) in
      let rec lexInitial __3__ __4__ =
        match (__3__, __4__) with
        | (':', i) -> (COLON, (P.Reg ((i - 1), i)))
        | ('.', i) -> (DOT, (P.Reg ((i - 1), i)))
        | ('(', i) -> (LPAREN, (P.Reg ((i - 1), i)))
        | (')', i) -> (RPAREN, (P.Reg ((i - 1), i)))
        | ('[', i) -> (LBRACKET, (P.Reg ((i - 1), i)))
        | (']', i) -> (RBRACKET, (P.Reg ((i - 1), i)))
        | ('{', i) -> (LBRACE, (P.Reg ((i - 1), i)))
        | ('}', i) -> (RBRACE, (P.Reg ((i - 1), i)))
        | ('%', i) -> lexPercent ((char i), (i + 1))
        | ('_', i) -> lexID (Upper, (P.Reg ((i - 1), i)))
        | ('\'', i) -> lexID (Lower, (P.Reg ((i - 1), i)))
        | ('\004', i) -> (EOF, (P.Reg ((i - 1), (i - 1))))
        | ('"', i) -> lexString (P.Reg ((i - 1), i))
        | (c, i) ->
            if Char.isSpace c
            then lexInitial ((char i), (i + 1))
            else
              if Char.isUpper c
              then lexID (Upper, (P.Reg ((i - 1), i)))
              else
                if Char.isDigit c
                then lexID (Lower, (P.Reg ((i - 1), i)))
                else
                  if Char.isLower c
                  then lexID (Lower, (P.Reg ((i - 1), i)))
                  else
                    if isSym c
                    then lexID (Lower, (P.Reg ((i - 1), i)))
                    else
                      if isUTF8 c
                      then lexID (Lower, (P.Reg ((i - 1), i)))
                      else
                        error
                          ((P.Reg ((i - 1), i)),
                            ((^) "Illegal character " Char.toString c))
      (* lexQUID (i-1,i) *)
      and lexID idCase (Reg (i, j)) =
        let rec lexID' j =
          if isIdChar (char j)
          then lexID' (j + 1)
          else idToToken (idCase, (P.Reg (i, j))) in
        lexID' j
      and lexQUID (Reg (i, j)) =
        ((if Char.isSpace (char j)
          then
            error ((P.Reg (i, (j + 1))), "Whitespace in quoted identifier")
          else
            if isQuote (char j)
            then qidToToken (P.Reg (i, j))
            else lexQUID (P.Reg (i, (j + 1))))
        (* recover by adding implicit quote? *)(* qidToToken (i, j) *))
      and lexPercent __5__ __6__ =
        match (__5__, __6__) with
        | ('.', i) -> (EOF, (P.Reg ((i - 2), i)))
        | ('{', i) -> lexPercentBrace ((char i), (i + 1))
        | ('%', i) -> lexComment ('%', i)
        | (c, i) ->
            if isIdChar c
            then lexPragmaKey (lexID (Quoted, (P.Reg ((i - 1), i))))
            else
              if Char.isSpace c
              then lexComment (c, i)
              else
                error
                  ((P.Reg ((i - 1), i)),
                    "Comment character `%' not followed by white space")
      and lexPragmaKey __7__ __8__ =
        match (__7__, __8__) with
        | (ID (_, "infix"), r) -> (INFIX, r)
        | (ID (_, "prefix"), r) -> (PREFIX, r)
        | (ID (_, "postfix"), r) -> (POSTFIX, r)
        | (ID (_, "mode"), r) -> (MODE, r)
        | (ID (_, "unique"), r) -> (UNIQUE, r)
        | (ID (_, "terminates"), r) -> (TERMINATES, r)
        | (ID (_, "block"), r) -> (BLOCK, r)
        | (ID (_, "worlds"), r) -> (WORLDS, r)
        | (ID (_, "covers"), r) -> (COVERS, r)
        | (ID (_, "total"), r) -> (TOTAL, r)
        | (ID (_, "reduces"), r) -> (REDUCES, r)
        | (ID (_, "tabled"), r) -> (TABLED, r)
        | (ID (_, "keepTable"), r) -> (KEEPTABLE, r)
        | (ID (_, "theorem"), r) -> (THEOREM, r)
        | (ID (_, "prove"), r) -> (PROVE, r)
        | (ID (_, "establish"), r) -> (ESTABLISH, r)
        | (ID (_, "assert"), r) -> (ASSERT, r)
        | (ID (_, "abbrev"), r) -> (ABBREV, r)
        | (ID (_, "name"), r) -> (NAME, r)
        | (ID (_, "define"), r) -> (DEFINE, r)
        | (ID (_, "solve"), r) -> (SOLVE, r)
        | (ID (_, "query"), r) -> (QUERY, r)
        | (ID (_, "fquery"), r) -> (FQUERY, r)
        | (ID (_, "compile"), r) -> (COMPILE, r)
        | (ID (_, "querytabled"), r) -> (QUERYTABLED, r)
        | (ID (_, "trustme"), r) -> (TRUSTME, r)
        | (ID (_, "subord"), r) -> (SUBORD, r)
        | (ID (_, "freeze"), r) -> (FREEZE, r)
        | (ID (_, "thaw"), r) -> (THAW, r)
        | (ID (_, "deterministic"), r) -> (DETERMINISTIC, r)
        | (ID (_, "clause"), r) -> (CLAUSE, r)
        | (ID (_, "sig"), r) -> (SIG, r)
        | (ID (_, "struct"), r) -> (STRUCT, r)
        | (ID (_, "where"), r) -> (WHERE, r)
        | (ID (_, "include"), r) -> (INCLUDE, r)
        | (ID (_, "open"), r) -> (OPEN, r)
        | (ID (_, "use"), r) -> (USE, r)
        | (ID (_, s), r) ->
            error
              (r,
                (("Unknown keyword %" ^ s) ^
                   " (single line comment starts with `%<whitespace>' or `%%')"))
      (* -fp 08/09/02 *)(* -rv 11/27/01 *)(* -gaw 07/11/08 *)
      (* -ABP 4/4/03 *)(* -rv 8/27/01 *)
      (* -bp 20/11/04 *)(* -bp 20/11/01 *)(* -bp 6/5/99 *)
      (* -fp 3/18/01 *)(* -cs 6/3/01 *)
      (* -fp 8/17/03 *)
      and lexComment __9__ __10__ =
        match (__9__, __10__) with
        | ('\n', i) -> lexInitial ((char i), (i + 1))
        | ('%', i) -> lexCommentPercent ((char i), (i + 1))
        | ('\004', i) ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed single-line comment at end of file")
        | (c, i) -> lexComment ((char i), (i + 1))(* recover: (EOF, (i-1,i-1)) *)
      and lexCommentPercent __11__ __12__ =
        match (__11__, __12__) with
        | ('.', i) -> (EOF, (P.Reg ((i - 2), i)))
        | (c, i) -> lexComment (c, i)
      and lexPercentBrace c i = lexDComment (c, 1, i)
      and lexDComment __13__ __14__ __15__ =
        match (__13__, __14__, __15__) with
        | ('}', l, i) -> lexDCommentRBrace ((char i), l, (i + 1))
        | ('%', l, i) -> lexDCommentPercent ((char i), l, (i + 1))
        | ('\004', l, i) ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed delimited comment at end of file")
        | (c, l, i) -> lexDComment ((char i), l, (i + 1))(* recover: (EOF, (i-1,i-1)) *)
      (* pass comment beginning for error message? *)
      and lexDCommentPercent __16__ __17__ __18__ =
        match (__16__, __17__, __18__) with
        | ('{', l, i) -> lexDComment ((char i), (l + 1), (i + 1))
        | ('.', l, i) ->
            error
              ((P.Reg ((i - 2), i)),
                "Unclosed delimited comment at end of file token `%.'")
        | (c, l, i) -> lexDComment (c, l, i)(* recover: (EOF, (i-2,i)) *)
      and lexDCommentRBrace __19__ __20__ __21__ =
        match (__19__, __20__, __21__) with
        | ('%', 1, i) -> lexInitial ((char i), (i + 1))
        | ('%', l, i) -> lexDComment ((char i), (l - 1), (i + 1))
        | (c, l, i) -> lexDComment (c, l, i)
      and lexString (Reg (i, j)) =
        ((match char j with
          | '"' -> ((STRING (string (i, (j + 1)))), (P.Reg (i, (j + 1))))
          | '\n' ->
              error
                ((P.Reg ((i - 1), (i - 1))),
                  "Unclosed string constant at end of line")
          | '\004' ->
              error
                ((P.Reg ((i - 1), (i - 1))),
                  "Unclosed string constant at end of file")
          | _ -> lexString (P.Reg (i, (j + 1))))
        (* recover: (EOL, (i-1,i-1)) *)(* recover: (EOF, (i-1,i-1)) *)) in
      let rec lexContinue j = Stream.delay (fun () -> lexContinue' j)
      and lexContinue' j = lexContinue'' (lexInitial ((char j), (j + 1)))
      and lexContinue'' =
        function
        | (ID _, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinueQualId j))
        | (token, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinue j))
      and lexContinueQualId j = Stream.delay (fun () -> lexContinueQualId' j)
      and lexContinueQualId' j =
        if (char j) = '.'
        then
          (if isIdChar (char (j + 1))
           then
             Stream.Cons
               ((PATHSEP, (P.Reg (j, (j + 1)))), (lexContinue (j + 1)))
           else
             Stream.Cons ((DOT, (P.Reg (j, (j + 1)))), (lexContinue (j + 1))))
        else lexContinue' j in
      ((lexContinue 0)
        (* local state maintained by the lexer *)(* current string (line) *)
        (* position of first character in s *)(* position after last character in s *)
        (* initialize line counter *)(* neither lexer nor parser should ever try to look beyond EOF *)
        (* readNext () = ()
         Effect: read the next line, updating s, left, and right

         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
        (* char (i) = character at position i
         Invariant: i >= !left
         Effects: will read input if i >= !right
      *)
        (* string (i,j) = substring at region including i, excluding j
         Invariant: i >= !left and i < j and j < !right
                    Note that the relevant parts must already have been read!
         Effects: None
      *)
        (* The remaining functions do not access the state or *)
        (* stream directly, using only functions char and string *)
        (* Quote characters are part of the name *)(* Treat quoted identifiers as lowercase, since they no longer *)
        (* override infix state.  Quoted identifiers are now only used *)
        (* inside pragmas *)(* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
        (* recover by ignoring: lexInitial (char(i), i+1) *)
        (* lexQUID is currently not used --- no quoted identifiers *)
        (* comments are now started by %<whitespace> *)
        (*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
        (* functions lexing delimited comments below take nesting level l *))
    let rec lexStream instream = lex (fun i -> Compat.inputLine97 instream)
    let rec lexTerminal prompt0 prompt1 =
      lex
        (function
         | 0 -> (print prompt0; Compat.inputLine97 TextIO.stdIn)
         | i -> (print prompt1; Compat.inputLine97 TextIO.stdIn))
    let rec toString' =
      function
      | DOT -> "."
      | PATHSEP -> "."
      | COLON -> ":"
      | LPAREN -> "("
      | RPAREN -> ")"
      | LBRACKET -> "["
      | RBRACKET -> "]"
      | LBRACE -> "{"
      | RBRACE -> "}"
      | BACKARROW -> "<-"
      | ARROW -> "->"
      | TYPE -> "type"
      | EQUAL -> "="
      | UNDERSCORE -> "_"
      | INFIX -> "%infix"
      | PREFIX -> "%prefix"
      | POSTFIX -> "%postfix"
      | NAME -> "%name"
      | DEFINE -> "%define"
      | SOLVE -> "%solve"
      | QUERY -> "%query"
      | FQUERY -> "%fquery"
      | COMPILE -> "%compile"
      | QUERYTABLED -> "%querytabled"
      | MODE -> "%mode"
      | UNIQUE -> "%unique"
      | COVERS -> "%covers"
      | TOTAL -> "%total"
      | TERMINATES -> "%terminates"
      | BLOCK -> "%block"
      | WORLDS -> "%worlds"
      | REDUCES -> "%reduces"
      | TABLED -> "%tabled"
      | KEEPTABLE -> "%keepTable"
      | THEOREM -> "%theorem"
      | PROVE -> "%prove"
      | ESTABLISH -> "%establish"
      | ASSERT -> "%assert"
      | ABBREV -> "%abbrev"
      | TRUSTME -> "%trustme"
      | SUBORD -> "%subord"
      | FREEZE -> "%freeze"
      | THAW -> "%thaw"
      | DETERMINISTIC -> "%deterministic"
      | CLAUSE -> "%clause"
      | SIG -> "%sig"
      | STRUCT -> "%struct"
      | WHERE -> "%where"
      | INCLUDE -> "%include"
      | OPEN -> "%open"
      | USE -> "%use"(* -fp 08/09/02 *)(* -rv 11/27/01. *)
      (*  -bp 04/11/03. *)(*  -bp 20/11/01. *)
      (*  -bp 6/5/99. *)(* -cs 6/3/01. *)
      (* -ABP 4/4/03 *)(* -rv 8/27/01 *)
    let rec toString =
      function
      | ID (_, s) -> ("identifier `" ^ s) ^ "'"
      | EOF -> "end of file or `%.'"
      | STRING s -> "constant string " ^ s
      | token -> ((^) "`" toString' token) ^ "'"
    exception NotDigit of char 
    let rec charToNat c =
      let digit = (-) (Char.ord c) Char.ord '0' in
      if (digit < 0) || (digit > 9) then raise (NotDigit c) else digit
    let rec stringToNat s =
      let l = String.size s in
      let rec stn i n =
        if i = l
        then n
        else stn ((i + 1), ((+) (10 * n) charToNat (String.sub (s, i)))) in
      stn (0, 0)
    let rec isUpper =
      function
      | "" -> false__
      | s -> let c = String.sub (s, 0) in (Char.isUpper c) || (c = '_')
  end  module Lexer = (Make_Lexer)(struct module Stream' = Stream end);;
