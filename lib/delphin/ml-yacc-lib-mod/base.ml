module type STREAMM  =
  sig
    type nonrec 'xa stream
    val streamify : (unit -> '_a) -> '_a stream
    val cons : ('_a * '_a stream) -> '_a stream
    val get : '_a stream -> ('_a * '_a stream)
  end
module type LR_TABLE  =
  sig
    type ('a, 'b) pairlist =
      | EMPTY 
      | PAIR of ('a * 'b * ('a, 'b) pairlist) 
    type state =
      | STATE of int 
    type term =
      | t_ of int 
    type nonterm =
      | NT of int 
    type action =
      | SHIFT of state 
      | REDUCE of int 
      | ACCEPT 
      | ERROR 
    type nonrec table
    val numStates : table -> int
    val numRules : table -> int
    val describeActions :
      table -> state -> ((term, action) pairlist * action)
    val describeGoto : table -> state -> (nonterm, state) pairlist
    val action : table -> (state * term) -> action
    val goto : table -> (state * nonterm) -> state
    val initialState : table -> state
    exception Goto of (state * nonterm) 
    val mkLrTable :
      <
        actions: ((term, action) pairlist * action) array  ;gotos: (nonterm,
                                                                    state)
                                                                    pairlist
                                                                    array  ;
        numStates: int  ;numRules: int  ;initialState: state   >  -> 
        table
  end
module type TOKEN  =
  sig
    module LrTable : LR_TABLE
    type ('a, 'b) token =
      | TOKEN of (LrTable.term * ('a * 'b * 'b)) 
    val sameToken : (('a, 'b) token * ('a, 'b) token) -> bool
  end
module type LR_PARSER  =
  sig
    module Streamm : STREAMM
    module LrTable : LR_TABLE
    module Token : TOKEN
    exception ParseError 
    val parse :
      ((<
          table: LrTable.table  ;lexer: ('_b, '_c) Token.token Streamm.stream
                                    ;arg: 'arg  ;saction: (int * '_c *
                                                            (LrTable.state *
                                                            ('_b * '_c *
                                                            '_c)) list *
                                                            'arg) ->
                                                            (LrTable.nonterm
                                                              * ('_b * '_c *
                                                              '_c) *
                                                              (LrTable.state
                                                              * ('_b * '_c *
                                                              '_c)) list)  ;
          void: '_b  ;ec: <
                            is_keyword: LrTable.term -> bool  ;noShift: 
                                                                 LrTable.term
                                                                   -> 
                                                                   bool  ;
                            preferred_change: (LrTable.term list *
                                                LrTable.term list) list  ;
                            errtermvalue: LrTable.term -> '_b  ;showTerminal: 
                                                                  LrTable.term
                                                                    -> 
                                                                    string  ;
                            terms: LrTable.term list  ;error: (string * '_c *
                                                                '_c) -> 
                                                                unit   >   ;
          lookahead: int   > )(* error correction *)
        (* max amount of lookahead used in *)) ->
        ('_b * ('_b, '_c) Token.token Streamm.stream)
  end
module type LEXERR  =
  sig
    module UserDeclarations :
    sig type nonrec ('a, 'b) token type nonrec pos type nonrec svalue end
    val makeLexer :
      (int -> string) ->
        unit ->
          (UserDeclarations.svalue, UserDeclarations.pos)
            UserDeclarations.token
  end
module type ARG_LEXER  =
  sig
    module UserDeclarations :
    sig
      type nonrec ('a, 'b) token
      type nonrec pos
      type nonrec svalue
      type nonrec arg
    end
    val makeLexer :
      (int -> string) ->
        UserDeclarations.arg ->
          unit ->
            (UserDeclarations.svalue, UserDeclarations.pos)
              UserDeclarations.token
  end
module type PARSER_DATA  =
  sig
    type nonrec pos
    type nonrec svalue
    type nonrec arg
    type nonrec result
    module LrTable : LR_TABLE
    module Token : TOKEN
    module Actions :
    sig
      val actions :
        (int * pos * (LrTable.state * (svalue * pos * pos)) list * arg) ->
          (LrTable.nonterm * (svalue * pos * pos) * (LrTable.state * (svalue
            * pos * pos)) list)
      val void : svalue
      val extract : svalue -> result
    end
    module EC :
    sig
      val is_keyword : LrTable.term -> bool
      val noShift : LrTable.term -> bool
      val preferred_change : (LrTable.term list * LrTable.term list) list
      val errtermvalue : LrTable.term -> svalue
      val showTerminal : LrTable.term -> string
      val terms : LrTable.term list
    end
    val table : LrTable.table
  end
module type PARSERR  =
  sig
    module Token : TOKEN
    module Streamm : STREAMM
    exception ParseError 
    type nonrec pos
    type nonrec result
    type nonrec arg
    type nonrec svalue
    val makeLexer :
      (int -> string) -> (svalue, pos) Token.token Streamm.stream
    val parse :
      (int * (svalue, pos) Token.token Streamm.stream *
        ((string * pos * pos) -> unit) * arg) ->
        (result * (svalue, pos) Token.token Streamm.stream)
    val sameToken :
      ((svalue, pos) Token.token * (svalue, pos) Token.token) -> bool
  end
module type ARG_PARSER  =
  sig
    module Token : TOKEN
    module Streamm : STREAMM
    exception ParseError 
    type nonrec arg
    type nonrec lexarg
    type nonrec pos
    type nonrec result
    type nonrec svalue
    val makeLexer :
      (int -> string) -> lexarg -> (svalue, pos) Token.token Streamm.stream
    val parse :
      (int * (svalue, pos) Token.token Streamm.stream *
        ((string * pos * pos) -> unit) * arg) ->
        (result * (svalue, pos) Token.token Streamm.stream)
    val sameToken :
      ((svalue, pos) Token.token * (svalue, pos) Token.token) -> bool
  end