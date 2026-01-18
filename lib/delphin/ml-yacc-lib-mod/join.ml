
module Join(Join:sig
                   module Lex : LEXERR
                   module ParserData : PARSER_DATA
                   module LrParser : LR_PARSER
                 end) : PARSERR =
  struct
    module Token = ParserData.Token
    module Streamm = LrParser.Streamm
    exception ParseError = LrParser.ParseError
    type nonrec arg = ParserData.arg
    type nonrec pos = ParserData.pos
    type nonrec result = ParserData.result
    type nonrec svalue = ParserData.svalue
    let makeLexer = LrParser.Streamm.streamify o Lex.makeLexer
    let parse =
      function
      | (lookahead, lexer, error, arg) ->
          ((function | (a, b) -> ((ParserData.Actions.extract a), b)))
            (LrParser.parse
               {
                 table = ParserData.table;
                 lexer;
                 lookahead;
                 saction = ParserData.Actions.actions;
                 arg;
                 void = ParserData.Actions.void;
                 ec =
                   {
                     is_keyword = ParserData.EC.is_keyword;
                     noShift = ParserData.EC.noShift;
                     preferred_change = ParserData.EC.preferred_change;
                     errtermvalue = ParserData.EC.errtermvalue;
                     error;
                     showTerminal = ParserData.EC.showTerminal;
                     terms = ParserData.EC.terms
                   }
               })
    let sameToken = Token.sameToken
  end 
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
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
(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)
(* functor JoinWithArg creates a variant of the parser structure produced 
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)
module JoinWithArg(JoinWithArg:sig
                                 module Lex : ARG_LEXER
                                 module ParserData : PARSER_DATA
                                 module LrParser : LR_PARSER
                               end) : ARG_PARSER =
  struct
    module Token = ParserData.Token
    module Streamm = LrParser.Streamm
    exception ParseError = LrParser.ParseError
    type nonrec arg = ParserData.arg
    type nonrec lexarg = Lex.UserDeclarations.arg
    type nonrec pos = ParserData.pos
    type nonrec result = ParserData.result
    type nonrec svalue = ParserData.svalue
    let makeLexer =
      function
      | s ->
          (function | arg -> LrParser.Streamm.streamify (Lex.makeLexer s arg))
    let parse =
      function
      | (lookahead, lexer, error, arg) ->
          ((function | (a, b) -> ((ParserData.Actions.extract a), b)))
            (LrParser.parse
               {
                 table = ParserData.table;
                 lexer;
                 lookahead;
                 saction = ParserData.Actions.actions;
                 arg;
                 void = ParserData.Actions.void;
                 ec =
                   {
                     is_keyword = ParserData.EC.is_keyword;
                     noShift = ParserData.EC.noShift;
                     preferred_change = ParserData.EC.preferred_change;
                     errtermvalue = ParserData.EC.errtermvalue;
                     error;
                     showTerminal = ParserData.EC.showTerminal;
                     terms = ParserData.EC.terms
                   }
               })
    let sameToken = Token.sameToken
  end ;;
