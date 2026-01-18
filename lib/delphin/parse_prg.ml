
(* The Parser *)
(* Author: Richard Fontana *)
module type PARSE  =
  sig
    module DextSyn : DEXTSYN
    val fparse : string -> unit
    val gparse : string -> DextSyn.__Ast
    val sparse : unit -> DextSyn.__Ast
  end;;




(* The Parser *)
(* Author: Richard Fontana *)
module Parse(Parse:sig
                     module DextSyn : DEXTSYN
                     module Interface : INTERFACE
                     module Parserr : PARSERR
                     module Tokens : Delphin_TOKENS
                   end) : PARSE =
  struct
    module DextSyn = DextSyn
    module Interface = Interface
    module Parserr = Parserr
    module Tokens = Tokens
    module Streamm = Parserr.Streamm
    module Token = Parserr.Token
    (* Given a lexer, invoke parser *)
    let rec invoke lexstream =
      Parserr.parse (0, lexstream, Interface.error, Interface.nothing)
    (* Parse a named input file *)
    let rec fparse fname =
      let _ = Interface.init_line () in
      let infile = TextIO.openIn fname in
      let lexer =
        Parserr.makeLexer (function | _ -> Compat.inputLine97 infile) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let rec loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        ((if Parserr.sameToken (nextToken, dummyEOF) then () else loop lexer;
          ())
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
      let rec loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        ((if Parserr.sameToken (nextToken, dummyEOF)
          then result
          else loop lexer)(* () *)) in
      loop lexer
    let rec gparse fname =
      let _ = Interface.init_line () in
      let infile = TextIO.openIn fname in
      let lexer =
        Parserr.makeLexer (function | _ -> Compat.inputLine97 infile) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let rec loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        ((if Parserr.sameToken (nextToken, dummyEOF)
          then result
          else loop lexer)
          (* () *)(* DextSyn.printAst result; *)
          (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
          (* DextSyn.termparse result; *)(*   ()  *)) in
      loop lexer
  end ;;
