
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
      | T of int 
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
      <
        table: LrTable.table  ;lexer: ('_b, '_c) Token.token Streamm.stream  ;
        arg: 'arg  ;saction: (int * '_c * (LrTable.state * ('_b * '_c * '_c))
                               list * 'arg) ->
                               (LrTable.nonterm * ('_b * '_c * '_c) *
                                 (LrTable.state * ('_b * '_c * '_c)) list)  ;
        void: '_b  ;ec: <
                          is_keyword: LrTable.term -> bool  ;noShift: 
                                                               LrTable.term
                                                                 -> bool  ;
                          preferred_change: (LrTable.term list * LrTable.term
                                              list) list  ;errtermvalue: 
                                                             LrTable.term ->
                                                               '_b  ;
                          showTerminal: LrTable.term -> string  ;terms: 
                                                                   LrTable.term
                                                                    list  ;
                          error: (string * '_c * '_c) -> unit   >   ;
        lookahead: int   >  -> ('_b * ('_b, '_c) Token.token Streamm.stream)
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
    module Token :
    ((TOKEN)(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: not supported by cvs2svn $
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.1.1.1  1997/01/14 01:38:04  george
 *   Version 109.24
 *
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)
    (* base.sig: Base signature file for SML-Yacc.  This file contains signatures
   that must be loaded before any of the files produced by ML-Yacc are loaded
*)
    (* STREAM: signature for a lazy stream.*)(* LR_TABLE: signature for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)
    (* TOKEN: signature revealing the internal structure of a token. This signature
   TOKEN distinct from the signature {parser name}_TOKENS produced by ML-Yacc.
   The {parser name}_TOKENS structures contain some types and functions to
    construct tokens from values and positions.

   The representation of token was very carefully chosen here to allow the
   polymorphic parser to work without knowing the types of semantic values
   or line numbers.

   This has had an impact on the TOKENS structure produced by SML-Yacc, which
   is a structure parameter to lexer functors.  We would like to have some
   type 'a token which functions to construct tokens would create.  A
   constructor function for a integer token might be

	  INT: int * 'a * 'a -> 'a token.
 
   This is not possible because we need to have tokens with the representation
   given below for the polymorphic parser.

   Thus our constructur functions for tokens have the form:

	  INT: int * 'a * 'a -> (svalue,'a) token

   This in turn has had an impact on the signature that lexers for SML-Yacc
   must match and the types that a user must declare in the user declarations
   section of lexers.
*)
    (* LR_PARSER: signature for a polymorphic LR parser *)
    (* max amount of lookahead used in *)(* error correction *)
    (* LEXERR: a signature that most lexers produced for use with SML-Yacc's
   output will match.  The user is responsible for declaring type token,
   type pos, and type svalue in the UserDeclarations section of a lexer.

   Note that type token is abstract in the lexer.  This allows SML-Yacc to
   create a TOKENS signature for use with lexers produced by ML-Lex that
   treats the type token abstractly.  Lexers that are functors parametrized by
   a Tokens structure matching a TOKENS signature cannot examine the structure
   of tokens.
*)
    (* ARG_LEXER: the %arg option of ML-Lex allows users to produce lexers which
   also take an argument before yielding a function from unit to a token
*)
    (* PARSER_DATA: the signature of ParserData structures in {parser name}LrValsFun
   produced by  SML-Yacc.  All such structures match this signature.  

   The {parser name}LrValsFun produces a structure which contains all the values
   except for the lexer needed to call the polymorphic parser mentioned
   before.

*)
    (* the type of line numbers *)(* the type of semantic values *)
    (* the type of the user-supplied argument to the parser *)(* the intended type of the result of the parser.  This value is
	   produced by applying extract from the structure Actions to the
	   final semantic value resultiing from a parse.
	 *)
    (* structure Actions contains the functions which mantain the
	   semantic values stack in the parser.  Void is used to provide
	   a default value for the semantic stack.
	 *)
    (* structure EC contains information used to improve error
	   recovery in an error-correcting parser *)
    (* table is the LR table for the parser *)(* signature PARSER is the signature that most user parsers created by 
   SML-Yacc will match.
*)
    (* type pos is the type of line numbers *)(* type result is the type of the result from the parser *)
    (* the type of the user-supplied argument to the parser *)(* type svalue is the type of semantic values for the semantic value
	   stack
	 *)
    (* val makeLexer is used to create a stream of tokens for the parser *)
    (* val parse takes a stream of tokens and a function to print
	   errors and returns a value of type result and a stream containing
	   the unused tokens
	 *)
    (* signature ARG_PARSER is the signature that will be matched by parsers whose
    lexer takes an additional argument.
*))
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
  end;;
