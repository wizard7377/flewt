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
      begin function
      | (lookahead, lexer, error, arg) ->
          ((begin function | (a, b) -> ((ParserData.Actions.extract a), b) end))
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
             }) end
  let sameToken = Token.sameToken end 
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
      begin function
      | s ->
          (begin function
           | arg -> LrParser.Streamm.streamify (Lex.makeLexer s arg) end) end
  let parse =
    begin function
    | (lookahead, lexer, error, arg) ->
        ((begin function | (a, b) -> ((ParserData.Actions.extract a), b) end))
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
           }) end
let sameToken = Token.sameToken end
