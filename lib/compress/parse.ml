
module Parse =
  struct
    open Parsing
    open Tok
    let ` = literal
    type mode =
      | mMINUS [@sml.renamed "mMINUS"][@sml.renamed "mMINUS"]
      | mPLUS [@sml.renamed "mPLUS"][@sml.renamed "mPLUS"]
      | mOMIT [@sml.renamed "mOMIT"][@sml.renamed "mOMIT"]
    type term =
      | Id of string 
      | App of (term * term) 
      | Lam of ((string * term option) * term) 
      | Type 
      | Pi of (mode * (string * term option) * term) 
      | Arrow of (term * term) 
      | PlusArrow of (term * term) 
      | Ascribe of (term * term) 
      | Omit 
    let rec PiMinus ((s, to__), t) = Pi (mMINUS, (s, to__), t)
    let rec PiPlus ((s, to__), t) = Pi (mPLUS, (s, to__), t)
    let rec PiOmit ((s, to__), t) = Pi (mOMIT, (s, to__), t)
    let rec modeToString =
      function | mMINUS -> "" | mPLUS -> "+ " | mOMIT -> "* "
    let rec termToString =
      function
      | Id s -> s
      | App (t, u) ->
          ((("(" ^ (termToString t)) ^ " ") ^ (termToString u)) ^ ")"
      | Lam (vd, t) ->
          (("[" ^ (vardecToString vd)) ^ "] ") ^ (termToString t)
      | Pi (m, vd, t) ->
          ((("{" ^ (modeToString m)) ^ (vardecToString vd)) ^ "} ") ^
            (termToString t)
      | Type -> "type"
      | Arrow (t, u) ->
          ((("(" ^ (termToString t)) ^ " -> ") ^ (termToString u)) ^ ")"
      | PlusArrow (t, u) ->
          ((("(" ^ (termToString t)) ^ " +> ") ^ (termToString u)) ^ ")"
      | Ascribe (t, u) ->
          ((("(" ^ (termToString t)) ^ " : ") ^ (termToString u)) ^ ")"
      | Omit -> "*"
    let rec vardecToString =
      function | (v, SOME t) -> (v ^ ":") ^ (termToString t) | (v, NONE) -> v
    let id = maybe (function | ID s -> SOME s | _ -> NONE)
    let rec swap (x, y) = (y, x)
    let rec vardec () =
      (||) ((` ((<<) id) COLON) && (($) term wth SOME)) id wth
        (function | s -> (s, NONE))
    let rec term () =
      parsefixityadj
        (alt
           [id wth (Atm o Id);
           ` ((<<) (((>>) (` LPAREN)) $ term)) RPAREN wth Atm;
           `
             ((<<) (((&&) (` ((<<) (((>>) (` LPAREN)) $ term)) COLON)) $ term))
             RPAREN wth (Atm o Ascribe);
           ($) ((&&) (` ((<<) (((>>) (` LBRACKET)) $ vardec)) RBRACKET)) term
             wth (Atm o Lam);
           ($) ((&&) (` ((<<) (((>>) (` ((>>) (` LBRACE)) STAR)) $ vardec))
                        RBRACE))
             term wth (Atm o PiOmit);
           ($) ((&&) (` ((<<) (((>>) (` ((>>) (` LBRACE)) PLUS)) $ vardec))
                        RBRACE))
             term wth (Atm o PiPlus);
           ($) ((&&) (` ((<<) (((>>) (` LBRACE)) $ vardec)) RBRACE)) term wth
             (Atm o PiMinus);
           ` TYPE return (Atm Type);
           ` ARROW return Opr (Infix (Right, 5, Arrow));
           ` PLUSARROW return Opr (Infix (Right, 5, PlusArrow));
           ` BACKARROW return Opr (Infix (Left, 5, (Arrow o swap)));
           ` STAR return (Atm Omit)]) Left App
    let condec =
      `
        ((<<) (((&&) (`
                        ((<<) ((opt (` MINUS) wth (not o Option.isSome)) &&
                                 id)) COLON))
                 $ term)) DOT
    let rec parseof x =
      Stream.toList
        (Parsing.transform (($) term)
           (Parsing.transform (!! tok)
              (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
  end;;
