module type PARSE  =
  sig
    module DextSyn : DEXTSYN
    val fparse : string -> unit
    val gparse : string -> DextSyn.ast_
    val sparse : unit -> DextSyn.ast_
  end


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
    let rec invoke lexstream =
      Parserr.parse (0, lexstream, Interface.error, Interface.nothing)
    let rec fparse fname =
      let _ = Interface.init_line () in
      let infile = TextIO.openIn fname in
      let lexer =
        Parserr.makeLexer
          (begin function | _ -> Compat.inputLine97 infile end) in
      let empty = !Interface.line in
      let dummyEOF = Tokens.EOF (empty, empty) in
      let rec loop lexer =
        let (result, lexer) = invoke lexer in
        let (nextToken, lexer) = Parserr.Streamm.get lexer in
        ((begin if Parserr.sameToken (nextToken, dummyEOF) then begin () end
          else begin loop lexer end; () end)
        (* DextSyn.printAst result; *)(* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
        (* DextSyn.termparse result; *)) in
      loop lexer
let rec sparse () =
  let _ = Interface.init_line () in
  let infile = TextIO.openString (TextIO.input TextIO.stdIn) in
  let lexer =
    Parserr.makeLexer (begin function | _ -> Compat.inputLine97 infile end) in
  let empty = !Interface.line in
  let dummyEOF = Tokens.EOF (empty, empty) in
  let rec loop lexer =
    let (result, lexer) = invoke lexer in
    let (nextToken, lexer) = Parserr.Streamm.get lexer in
    ((if Parserr.sameToken (nextToken, dummyEOF) then begin result end
      else begin loop lexer end)
    (* () *)) in
  loop lexer
let rec gparse fname =
  let _ = Interface.init_line () in
  let infile = TextIO.openIn fname in
  let lexer =
    Parserr.makeLexer (begin function | _ -> Compat.inputLine97 infile end) in
  let empty = !Interface.line in
  let dummyEOF = Tokens.EOF (empty, empty) in
  let rec loop lexer =
    let (result, lexer) = invoke lexer in
    let (nextToken, lexer) = Parserr.Streamm.get lexer in
    ((if Parserr.sameToken (nextToken, dummyEOF) then begin result end
      else begin loop lexer end)
    (* () *)(* DextSyn.printAst result; *)
    (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
    (* DextSyn.termparse result; *)(*   ()  *)) in
  loop lexer end
