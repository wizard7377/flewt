module type LEXER  =
  sig
    module Stream : STREAM
    type idCase_ =
      | Upper 
      | Lower 
      | Quoted 
    type token_ =
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
      | ID of (idCase_ * string) 
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
    val lexStream : TextIO.instream -> (token_ * Paths.region) Stream.stream
    val lexTerminal :
      (string * string) -> (token_ * Paths.region) Stream.stream
    val toString : token_ -> string
    exception NotDigit of char 
    val stringToNat : string -> int
    val isUpper : string -> bool
  end


module Lexer(Lexer:sig module Stream' : STREAM end) : LEXER =
  struct
    module Stream = Stream'
    module P = Paths
    type idCase_ =
      | Upper 
      | Lower 
      | Quoted 
    type token_ =
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
      | ID of (idCase_ * string) 
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
      begin function
      | (Lower, "<-", r) -> (BACKARROW, r)
      | (Lower, "->", r) -> (ARROW, r)
      | (Upper, "_", r) -> (UNDERSCORE, r)
      | (Lower, "=", r) -> (EQUAL, r)
      | (Lower, "type", r) -> (TYPE, r)
      | (idCase, s, r) -> ((ID (idCase, s)), r) end
    let rec lex (inputFun : int -> string) =
      let s = ref ""
      and left = ref 0
      and right = ref 0 in
      let _ = P.resetLines () in
      let EOFString = String.str '\004' in
      let rec readNext () =
        let nextLine = inputFun !right in
        let nextSize = String.size nextLine in
        ((if nextSize = 0
          then
            begin (((begin s := EOFString;
                     (!) ((:=) left) right;
                     ((!) ((:=) right) right) + 1 end))
          (* fake EOF character string *)) end
          else begin
            (begin s := nextLine;
             (!) ((:=) left) right;
             ((!) ((:=) right) right) + nextSize;
             P.newLine !left end) end)
        (* end of file? *)(* remember new line position *)) in
    let rec char i =
      if (!) ((>=) i) right then begin (begin readNext (); char i end) end
      else begin String.sub (!s, ((!) ((-) i) left)) end in
  let rec string (i, j) = String.substring (!s, ((!) ((-) i) left), (j - i)) in
  let rec idToToken (idCase, Reg (i, j)) =
    stringToToken (idCase, (string (i, j)), (P.Reg (i, j))) in
  let rec qidToToken (Reg (i, j)) =
    ((ID (Lower, (string (i, (j + 1))))), (P.Reg (i, (j + 1)))) in
  let rec lexInitial =
    begin function
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
        if Char.isSpace c then begin lexInitial ((char i), (i + 1)) end
        else begin
          if Char.isUpper c
          then begin lexID (Upper, (P.Reg ((i - 1), i))) end
          else begin
            if Char.isDigit c
            then begin lexID (Lower, (P.Reg ((i - 1), i))) end
            else begin
              if Char.isLower c
              then begin lexID (Lower, (P.Reg ((i - 1), i))) end
              else begin
                if isSym c then begin lexID (Lower, (P.Reg ((i - 1), i))) end
                else begin
                  if isUTF8 c
                  then begin lexID (Lower, (P.Reg ((i - 1), i))) end
                  else begin
                    error
                      ((P.Reg ((i - 1), i)),
                        ((^) "Illegal character " Char.toString c)) end end end end end end end
(* lexQUID (i-1,i) *)
and lexID (idCase, Reg (i, j)) =
  let rec lexID' j = if isIdChar (char j) then begin lexID' (j + 1) end
    else begin idToToken (idCase, (P.Reg (i, j))) end in lexID' j
and lexQUID (Reg (i, j)) =
  ((if Char.isSpace (char j)
    then
      begin error ((P.Reg (i, (j + 1))), "Whitespace in quoted identifier") end
  else begin if isQuote (char j) then begin qidToToken (P.Reg (i, j)) end
    else begin lexQUID (P.Reg (i, (j + 1))) end end)
(* recover by adding implicit quote? *)(* qidToToken (i, j) *))
and lexPercent =
  begin function
  | ('.', i) -> (EOF, (P.Reg ((i - 2), i)))
  | ('{', i) -> lexPercentBrace ((char i), (i + 1))
  | ('%', i) -> lexComment ('%', i)
  | (c, i) ->
      if isIdChar c
      then begin lexPragmaKey (lexID (Quoted, (P.Reg ((i - 1), i)))) end
      else begin if Char.isSpace c then begin lexComment (c, i) end
        else begin
          error
            ((P.Reg ((i - 1), i)),
              "Comment character `%' not followed by white space") end end end
and lexPragmaKey =
  begin function
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
             " (single line comment starts with `%<whitespace>' or `%%')")) end
(* -fp 08/09/02 *)(* -rv 11/27/01 *)
(* -gaw 07/11/08 *)(* -ABP 4/4/03 *)
(* -rv 8/27/01 *)(* -bp 20/11/04 *)
(* -bp 20/11/01 *)(* -bp 6/5/99 *)
(* -fp 3/18/01 *)(* -cs 6/3/01 *)
(* -fp 8/17/03 *)
and lexComment =
  begin function
  | ('\n', i) -> lexInitial ((char i), (i + 1))
  | ('%', i) -> lexCommentPercent ((char i), (i + 1))
  | ('\004', i) ->
      error
        ((P.Reg ((i - 1), (i - 1))),
          "Unclosed single-line comment at end of file")
  | (c, i) -> lexComment ((char i), (i + 1)) end(* recover: (EOF, (i-1,i-1)) *)
and lexCommentPercent =
  begin function
  | ('.', i) -> (EOF, (P.Reg ((i - 2), i)))
  | (c, i) -> lexComment (c, i) end
and lexPercentBrace (c, i) = lexDComment (c, 1, i)
and lexDComment =
  begin function
  | ('}', l, i) -> lexDCommentRBrace ((char i), l, (i + 1))
  | ('%', l, i) -> lexDCommentPercent ((char i), l, (i + 1))
  | ('\004', l, i) ->
      error
        ((P.Reg ((i - 1), (i - 1))),
          "Unclosed delimited comment at end of file")
  | (c, l, i) -> lexDComment ((char i), l, (i + 1)) end(* recover: (EOF, (i-1,i-1)) *)
(* pass comment beginning for error message? *)
and lexDCommentPercent =
  begin function
  | ('{', l, i) -> lexDComment ((char i), (l + 1), (i + 1))
  | ('.', l, i) ->
      error
        ((P.Reg ((i - 2), i)),
          "Unclosed delimited comment at end of file token `%.'")
  | (c, l, i) -> lexDComment (c, l, i) end(* recover: (EOF, (i-2,i)) *)
and lexDCommentRBrace =
  begin function
  | ('%', 1, i) -> lexInitial ((char i), (i + 1))
  | ('%', l, i) -> lexDComment ((char i), (l - 1), (i + 1))
  | (c, l, i) -> lexDComment (c, l, i) end
and lexString (Reg (i, j)) =
  ((begin match char j with
    | '"' -> ((STRING (string (i, (j + 1)))), (P.Reg (i, (j + 1))))
    | '\n' ->
        error
          ((P.Reg ((i - 1), (i - 1))),
            "Unclosed string constant at end of line")
    | '\004' ->
        error
          ((P.Reg ((i - 1), (i - 1))),
            "Unclosed string constant at end of file")
    | _ -> lexString (P.Reg (i, (j + 1))) end)
(* recover: (EOL, (i-1,i-1)) *)(* recover: (EOF, (i-1,i-1)) *)) in
let rec lexContinue j =
Stream.delay (begin function | () -> lexContinue' j end)
and lexContinue' j = lexContinue'' (lexInitial ((char j), (j + 1)))
and lexContinue'' =
  begin function
  | (ID _, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinueQualId j))
  | (token, Reg (i, j)) as mt -> Stream.Cons (mt, (lexContinue j)) end
and lexContinueQualId j =
  Stream.delay (begin function | () -> lexContinueQualId' j end)
and lexContinueQualId' j =
  if (char j) = '.'
  then
    begin (if isIdChar (char (j + 1))
           then
             begin Stream.Cons
                     ((PATHSEP, (P.Reg (j, (j + 1)))), (lexContinue (j + 1))) end
    else begin
      Stream.Cons ((DOT, (P.Reg (j, (j + 1)))), (lexContinue (j + 1))) end) end
else begin lexContinue' j end in ((lexContinue 0)
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
(* lexQUID is currently not used --- no quoted identifiers *)(* comments are now started by %<whitespace> *)
(*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
(* functions lexing delimited comments below take nesting level l *))
let rec lexStream instream =
  lex (begin function | i -> Compat.inputLine97 instream end)
let rec lexTerminal (prompt0, prompt1) =
  lex
    (begin function
     | 0 -> (begin print prompt0; Compat.inputLine97 TextIO.stdIn end)
    | i -> (begin print prompt1; Compat.inputLine97 TextIO.stdIn end) end)
let rec toString' =
  begin function
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
  | USE -> "%use" end(* -fp 08/09/02 *)(* -rv 11/27/01. *)
(*  -bp 04/11/03. *)(*  -bp 20/11/01. *)
(*  -bp 6/5/99. *)(* -cs 6/3/01. *)
(* -ABP 4/4/03 *)(* -rv 8/27/01 *)
let rec toString =
  begin function
  | ID (_, s) -> ("identifier `" ^ s) ^ "'"
  | EOF -> "end of file or `%.'"
  | STRING s -> "constant string " ^ s
  | token -> ((^) "`" toString' token) ^ "'" end
exception NotDigit of char 
let rec charToNat c =
  let digit = (-) (Char.ord c) Char.ord '0' in
  if (digit < 0) || (digit > 9) then begin raise (NotDigit c) end
    else begin digit end
let rec stringToNat s =
  let l = String.size s in
  let rec stn (i, n) = if i = l then begin n end
    else begin stn ((i + 1), ((+) (10 * n) charToNat (String.sub (s, i)))) end in
stn (0, 0)
let rec isUpper =
  begin function
  | "" -> false
  | s -> let c = String.sub (s, 0) in (Char.isUpper c) || (c = '_') end end 
module Lexer = (Lexer)(struct module Stream' = Stream end)