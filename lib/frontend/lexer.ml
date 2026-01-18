
(* Lexer *)
(* Author: Frank Pfenning *)
module type LEXER  =
  sig
    (* Stream is not memoizing for efficiency *)
    module Stream : STREAM
    (*! structure Paths : PATHS !*)
    type __IdCase =
      | Upper 
      | Lower 
      | Quoted 
    (* '<id>', currently unused *)
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
    (* string constants *)
    exception Error of string 
    (* lexer returns an infinite stream, terminated by EOF token *)
    val lexStream : TextIO.instream -> (__Token * Paths.region) Stream.stream
    val lexTerminal :
      (string * string) -> (__Token * Paths.region) Stream.stream
    val toString : __Token -> string
    (* Utilities *)
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
    let rec error (r, msg) = raise (Error (P.wrap (r, msg)))
    let (isSym : char -> bool) = Char.contains "_!&$^+/<=>?@~|#*`;,-\\"
    let rec isUTF8 c = not (Char.isAscii c)
    let rec isQuote c = c = '\''
    let rec isIdChar c =
      (Char.isLower c) ||
        ((Char.isUpper c) ||
           ((Char.isDigit c) || ((isSym c) || ((isQuote c) || (isUTF8 c)))))
    let rec stringToToken =
      function
      | (Lower, "<-", r) -> (BACKARROW, r)
      | (Lower, "->", r) -> (ARROW, r)
      | (Upper, "_", r) -> (UNDERSCORE, r)
      | (Lower, "=", r) -> (EQUAL, r)
      | (Lower, "type", r) -> (TYPE, r)
      | (idCase, s, r) -> ((ID (idCase, s)), r)
    let rec lex (inputFun : int -> string) =
      let s = ref ""
      and left = ref 0
      and right = ref 0 in
      let _ = P.resetLines () in
      let EOFString = String.str '\004' in
      let rec readNext () =
        let nextLine = inputFun (!right) in
        let nextSize = String.size nextLine in
        if nextSize = 0
        then
          (s := EOFString;
           (!) ((:=) left) right;
           ((!) ((:=) right) right) + 1)
        else
          (s := nextLine;
           (!) ((:=) left) right;
           ((!) ((:=) right) right) + nextSize;
           P.newLine (!left)) in
      let rec char i =
        if (!) ((>=) i) right
        then (readNext (); char i)
        else String.sub ((!s), ((!) ((-) i) left)) in
      let rec string (i, j) =
        String.substring ((!s), ((!) ((-) i) left), (j - i)) in
      let rec idToToken (idCase, Reg (i, j)) =
        stringToToken (idCase, (string (i, j)), (P.Reg (i, j))) in
      let rec qidToToken (Reg (i, j)) =
        ((ID (Lower, (string (i, (j + 1))))), (P.Reg (i, (j + 1)))) in
      let rec lexInitial =
        function
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
      and lexID (idCase, Reg (i, j)) =
        let rec lexID' j =
          if isIdChar (char j)
          then lexID' (j + 1)
          else idToToken (idCase, (P.Reg (i, j))) in
        lexID' j
      and lexQUID (Reg (i, j)) =
        if Char.isSpace (char j)
        then error ((P.Reg (i, (j + 1))), "Whitespace in quoted identifier")
        else
          if isQuote (char j)
          then qidToToken (P.Reg (i, j))
          else lexQUID (P.Reg (i, (j + 1)))
      and lexPercent =
        function
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
      and lexPragmaKey =
        function
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
      and lexComment =
        function
        | ('\n', i) -> lexInitial ((char i), (i + 1))
        | ('%', i) -> lexCommentPercent ((char i), (i + 1))
        | ('\004', i) ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed single-line comment at end of file")
        | (c, i) -> lexComment ((char i), (i + 1))
      and lexCommentPercent =
        function
        | ('.', i) -> (EOF, (P.Reg ((i - 2), i)))
        | (c, i) -> lexComment (c, i)
      and lexPercentBrace (c, i) = lexDComment (c, 1, i)
      and lexDComment =
        function
        | ('}', l, i) -> lexDCommentRBrace ((char i), l, (i + 1))
        | ('%', l, i) -> lexDCommentPercent ((char i), l, (i + 1))
        | ('\004', l, i) ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed delimited comment at end of file")
        | (c, l, i) -> lexDComment ((char i), l, (i + 1))
      and lexDCommentPercent =
        function
        | ('{', l, i) -> lexDComment ((char i), (l + 1), (i + 1))
        | ('.', l, i) ->
            error
              ((P.Reg ((i - 2), i)),
                "Unclosed delimited comment at end of file token `%.'")
        | (c, l, i) -> lexDComment (c, l, i)
      and lexDCommentRBrace =
        function
        | ('%', 1, i) -> lexInitial ((char i), (i + 1))
        | ('%', l, i) -> lexDComment ((char i), (l - 1), (i + 1))
        | (c, l, i) -> lexDComment (c, l, i)
      and lexString (Reg (i, j)) =
        match char j with
        | '"' -> ((STRING (string (i, (j + 1)))), (P.Reg (i, (j + 1))))
        | '\n' ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed string constant at end of line")
        | '\004' ->
            error
              ((P.Reg ((i - 1), (i - 1))),
                "Unclosed string constant at end of file")
        | _ -> lexString (P.Reg (i, (j + 1))) in
      let rec lexContinue j = Stream.delay (function | () -> lexContinue' j)
      and lexContinue' j = lexContinue'' (lexInitial ((char j), (j + 1)))
      and lexContinue'' =
        function
        | (ID _, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinueQualId j))
        | (token, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinue j))
      and lexContinueQualId j =
        Stream.delay (function | () -> lexContinueQualId' j)
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
      lexContinue 0
    let rec lexStream instream =
      lex (function | i -> Compat.inputLine97 instream)
    let rec lexTerminal (prompt0, prompt1) =
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
      | USE -> "%use"
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
      let rec stn (i, n) =
        if i = l
        then n
        else stn ((i + 1), ((+) (10 * n) charToNat (String.sub (s, i)))) in
      stn (0, 0)
    let rec isUpper =
      function
      | "" -> false__
      | s -> let c = String.sub (s, 0) in (Char.isUpper c) || (c = '_')
  end  (* Lexer *)
(* Author: Frank Pfenning *)
(* Modified: Brigitte Pientka *)
(*! structure Paths' : PATHS !*)
(*! structure Paths = Paths' !*)
(* [A-Z]<id> or _<id> *)
(* any other <id> *)
(* '<id>', currently unused *)
(* end of file or stream, also `%.' *)
(* `.' *) (* `.' between <id>s *)
(* `:' *) (* `(' `)' *)
(* `[' `]' *) (* `{' `}' *)
(* `<-' `->' *) (* `type' *)
(* `=' *) (* identifer *)
(* `_' *)
(* `%infix' `%prefix' `%postfix' *)
(* `%name' *) (* `%define' *)
(* -rv 8/27/01 *) (* `%solve' *)
(* `%query' *) (* `%fquery' *)
(* '%compile' *) (* -ABP 4/4/03 *)
(* `%querytabled *) (* `%mode' *)
(* `%unique' *) (* -fp 8/17/03 *)
(* `%covers' *) (* -fp 3/7/01 *)
(* `%total' *) (* -fp 3/18/01 *)
(* `%terminates' *) (* `%reduces' *)
(* -bp  6/05/99 *) (* `%tabled' *)
(* -bp 11/20/01 *) (* `%keepTable' *)
(* -bp 11/20/01 *) (* `%theorem' *)
(* `%block' *) (* -cs 5/29/01 *)
(* `%worlds' *) (* `%prove' *)
(* `%establish' *) (* `%assert' *)
(* `%abbrev' *) (* `%trustme' *)
(* -fp 8/26/05 *) (* `%freeze' *)
(* `%thaw' *) (* `%subord' *)
(* -gaw 07/11/08 *)
(* `%deterministic' *)
(* -rv 11/27/01 *) (* `%clause' *)
(* -fp 8/9/02 *) (* `%sig' *)
(* `%struct' *) (* `%where' *)
(* `%include' *) (* `%open' *)
(* `%use' *) (* string constants *)
(* isSym (c) = B iff c is a legal symbolic identifier constituent *)
(* excludes quote character and digits, which are treated specially *)
(* Char.contains stages its computation *)
(* isUFT8 (c) = assume that if a character is not ASCII it must be
     part of a UTF8 Unicode encoding.  Treat these as lowercase
     identifiers.  Somewhat of a hack until there is native Unicode
     string support. *)
(* isQuote (c) = B iff c is the quote character *)
(* isIdChar (c) = B iff c is legal identifier constituent *)
(* stringToToken (idCase, string, region) = (token, region)
     converts special identifiers into tokens, returns ID token otherwise
  *)
(* lex (inputFun) = (token, region) stream

     inputFun maintains state, reading input one line at a time and
     returning a string terminated by <newline> each time.
     The end of the stream is signalled by a string consisting only of ^__d
     Argument to inputFun is the character position.
  *)
(* local state maintained by the lexer *)
(* current string (line) *)
(* position of first character in s *)
(* position after last character in s *)
(* initialize line counter *)
(* neither lexer nor parser should ever try to look beyond EOF *)
(* readNext () = ()
         Effect: read the next line, updating s, left, and right

         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
(* end of file? *)
(* fake EOF character string *)
(* remember new line position *)
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
(* Quote characters are part of the name *)
(* Treat quoted identifiers as lowercase, since they no longer *)
(* override infix state.  Quoted identifiers are now only used *)
(* inside pragmas *)
(* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
(* lexQUID (i-1,i) *)
(* recover by ignoring: lexInitial (char(i), i+1) *)
(* lexQUID is currently not used --- no quoted identifiers *)
(* recover by adding implicit quote? *)
(* qidToToken (i, j) *)
(* -fp 8/17/03 *) (* -cs 6/3/01 *)
(* -fp 3/18/01 *) (* -bp 6/5/99 *)
(* -bp 20/11/01 *) (* -bp 20/11/04 *)
(* -rv 8/27/01 *) (* -ABP 4/4/03 *)
(* -gaw 07/11/08 *) (* -rv 11/27/01 *)
(* -fp 08/09/02 *)
(* comments are now started by %<whitespace> *)
(*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
(* recover: (EOF, (i-1,i-1)) *)
(* functions lexing delimited comments below take nesting level l *)
(* pass comment beginning for error message? *)
(* recover: (EOF, (i-1,i-1)) *)
(* recover: (EOF, (i-2,i)) *)
(* recover: (EOL, (i-1,i-1)) *)
(* recover: (EOF, (i-1,i-1)) *)
(* fun lex (inputFun) = let ... in ... end *)
(* -rv 8/27/01 *) (* -ABP 4/4/03 *)
(* -cs 6/3/01. *) (*  -bp 6/5/99. *)
(*  -bp 20/11/01. *)
(*  -bp 04/11/03. *)
(* -rv 11/27/01. *) (* -fp 08/09/02 *)
(* charToNat(c) = n converts character c to decimal equivalent *)
(* raises NotDigit(c) if c is not a digit 0-9 *)
(* stringToNat(s) = n converts string s to a natural number *)
(* raises NotDigit(c) if s contains character c which is not a digit *)
(* isUpper (s) = true, if s is a string starting with an uppercase
     letter or underscore (_).
  *)
(* local ... *) (* functor Lexer *)
module Lexer = (Make_Lexer)(struct module Stream' = Stream end);;
