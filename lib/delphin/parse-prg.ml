
module type PARSE  =
  sig
    module DextSyn :
    ((DEXTSYN)(* The Parser *)(* Author: Richard Fontana *))
    val fparse : string -> unit
    val gparse : string -> DextSyn.__Ast
    val sparse : unit -> DextSyn.__Ast
  end;;




module Parse(Parse:sig
                     module DextSyn : DEXTSYN
                     module Interface : INTERFACE
                     module Parserr : PARSERR
                     module Tokens :
                     ((Delphin_TOKENS)(* The Parser *)
                     (* Author: Richard Fontana *))
                   end) : PARSE =
  struct
    module DextSyn = DextSyn
    module Interface = Interface
    module Parserr = Parserr
    module Tokens = Tokens
    module Streamm = Parserr.Streamm
    module Token = Parserr.Token
    let rec invoke
      ((lexstream)(* Given a lexer, invoke parser *)) =
      Parserr.parse (0, lexstream, Interface.error, Interface.nothing)
    let rec fparse ((fname)(* Parse a named input file *)) =
      let _ = Interface.init_line () in
      let infile = TextIO.openIn fname in
      let lexer =
        Parserr.makeLexer (function | _ -> Compat.inputLine97 infile) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        if Parserr.sameToken (nextToken, dummyEOF) then () else loop lexer;
        ((())
        (* DextSyn.printAst result; *)(* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
        (* DextSyn.termparse result; *)) in
      loop lexer
    let rec sparse () =
      let _ = Interface.init_line () in
      let infile = TextIO.openString (TextIO.input TextIO.stdIn) in
      let lexer =
        Parserr.makeLexer (function | _ -> Compat.inputLine97 infile) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        if Parserr.sameToken (nextToken, dummyEOF)
        then result
        else loop ((lexer)(* () *)) in
      loop lexer
    let rec gparse fname =
      let _ = Interface.init_line () in
      let infile = TextIO.openIn fname in
      let lexer =
        Parserr.makeLexer (function | _ -> Compat.inputLine97 infile) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        ((if Parserr.sameToken (nextToken, dummyEOF)
          then result
          else loop ((lexer)(* () *)))
          (* DextSyn.printAst result; *)(* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
          (* DextSyn.termparse result; *)(*   ()  *)) in
      loop lexer
  end ;;
