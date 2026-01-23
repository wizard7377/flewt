module type DELPHIN  =
  sig
    val version : string
    val loadFile : (string * string) -> unit
    val top : unit -> unit
    val runSimpleTest : string -> string list -> string list -> unit
    val eval : Tomega.prg_ -> Tomega.prg_
  end


module Delphin(Delphin:sig
                         module Parser : PARSER
                         module DextSyn : DEXTSYN
                         module Parse : PARSE
                         module Twelf : TWELF
                         module Trans : TRANS
                       end) : DELPHIN =
  struct
    let version = "Delphin, Version 0.5, July 2003"
    let prompt = "> "
    exception What of Tomega.prg_ 
    module I = IntSyn
    module T = Tomega
    let rec chatter chlev f =
      if !Global.chatter >= chlev then begin print (f ()) end
      else begin () end
  let rec loadFile (s1, s2) =
    let _ = Twelf.reset () in
    let _ = Twelf.loadFile s1 in
    let _ =
      chatter 1 (begin function | () -> ("[Opening file " ^ s2) ^ "]\n" end) in
    let _ = Trans.internalizeSig () in
    let _ = chatter 4 (begin function | () -> "[Parsing ..." end) in
    let Ast (EDs) = Parse.gparse s2 in
    let _ = chatter 4 (begin function | () -> "]\n[Translation ..." end) in
    let p_ = Trans.transDecs EDs in
    let _ = chatter 4 (begin function | () -> "]\n[Externalization ..." end) in
    let p'_ = Trans.externalizePrg p_ in
    let _ = chatter 4 (begin function | () -> "]\n" end) in
    let _ =
      chatter 4 (begin function | () -> "[Operational Semantics ..." end) in
    let v_ = Opsem.topLevel p'_ in
    let _ = chatter 4 (begin function | () -> "]\n" end) in
    let _ =
      chatter 1 (begin function | () -> ("[Closing file " ^ s2) ^ "]\n" end) in
    ((v_)
      (*      val _ = print "* Type reconstruction done\n" *)
      (*      val _ = raise What P'
        val _ = print "* Externalization done\n" *)
      (*      val _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P', Tomega.True))
        val _ = print "* Typechecking done\n"
*)
      (* was evalPrg --cs Mon Jun 30 12:09:21 2003*)
      (*      val _ = print "* Operational semantics done\n" *))
let rec top () = loop ()
let rec loop () =
  let _ = print prompt in
  let Ast (ED) = Parse.sparse () in ((loop ())
    (*         val res = Trans.transDecs ED    *))
let rec runSimpleTest sourcesFile funcList args =
  let rec test =
    begin function
    | name::[] as names ->
        let La =
          map
            (begin function
             | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))) end)
          names in
      let (lemma, projs, sels) = Converter.installPrg La in
      let p_ = Tomega.lemmaDef lemma in
      let f_ = Converter.convertFor La in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
      let _ =
        TextIO.print
          (((^) "\n" TomegaPrint.funToString
              (((map
                   (begin function
                    | cid -> IntSyn.conDecName (IntSyn.sgnLookup cid) end) La),
                projs),
              p_)) ^ "\n") in
      (((p_, f_))
        (*           val P = Redundant.convert (Tomega.lemmaDef lemma) *))
    | names ->
        let La =
          map
            (begin function
             | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))) end)
          names in
      let (lemma, projs, sels) = Converter.installPrg La in
      let p_ = Redundant.convert (Tomega.lemmaDef lemma) in
      let f_ = Converter.convertFor La in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
      let _ =
        TextIO.print
          (((^) "\n" TomegaPrint.funToString
              (((map
                   (begin function
                    | cid -> IntSyn.conDecName (IntSyn.sgnLookup cid) end) La),
                projs),
              p_)) ^ "\n") in
      ((((Tomega.lemmaDef (List.hd sels)), f_))
        (* val P = Tomega.lemmaDef lemma *)) end in
let rec checkDec (u, (UDec (Dec (_, v_)) as d_)) =
begin print "$"; TypeCheck.typeCheck (I.Null, (u, v_)) end in
let rec makeSpine =
begin function
| ([], f_) -> (T.Nil, f_)
| (x::l_, (And (f1_, f2_) as f'_)) ->
    let (s'_, f'_) =
      makeSpine
        (l_,
          (T.forSub
             (f'_, (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
    ((T.AppExp ((I.Root ((I.Def x), I.Nil)), s'_)), f'_)
| (x::l_, All ((d_, _), f'_)) ->
    let _ = checkDec ((I.Root ((I.Def x), I.Nil)), d_) in
    let (s'_, f'_) =
      makeSpine
        (l_,
          (T.forSub
             (f'_, (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
    ((T.AppExp ((I.Root ((I.Def x), I.Nil)), s'_)), f'_) end in
let _ = Twelf.make sourcesFile in
let (p_, f_) = test funcList in
let _ = print ((TomegaPrint.forToString (I.Null, f_)) ^ "\n") in
let xs =
map
  (begin function
   | a -> valOf (Names.constLookup (valOf (Names.stringToQid a))) end)
args in
let (s'_, f'_) = makeSpine (xs, f_) in
let p'_ = T.Redex (p_, s'_) in
let _ = TomegaTypeCheck.checkPrg (I.Null, (p'_, f'_)) in
let result = Opsem.evalPrg p'_ in
let _ = TextIO.print "\n\nEOC\n\n" in
let _ = TextIO.print (TomegaPrint.prgToString (I.Null, result)) in
let _ = TextIO.print "\n" in ((())
(*        | checkDec (u, D as PDec (_, T.All (D, F')))) = ???  *)
(*      val _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)
(*      val P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.
Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil)))
*)
(*
        val _ = TextIO.print "\n"
        val _ = TextIO.print (TomegaPrint.prgToString (I.Null, P'))
        val _ = TextIO.print "\n"
           *)
(*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *))
let rec eval (p_) = let v_ = Opsem.evalPrg p_ in v_
let version = version
let loadFile = loadFile
let top = top
let runSimpleTest = runSimpleTest
let eval = eval end



module DextSyn : DEXTSYN =
  (DextSyn)(struct
                   module Stream' = Stream
                   module ParseTerm' = ParseTerm
                   module ExtSyn' = ParseTerm.ExtSyn
                   module Parsing' = Parsing
                   module Lexer' = Lexer
                 end) 
module DelphinLrVals : Delphin_LRVALS =
  (DelphinLrValsFun)(struct
                            module Token = LrParser.Token
                            module DextSyn' = DextSyn
                            module Stream = Stream
                            module Lexer' = Lexer
                            module Parsing' = Parsing
                          end) 
module Interface : INTERFACE = (Interface)(struct  end) 
module DelphinLex : LEXERR =
  (DelphinLexFun)(struct
                         module Tokens = DelphinLrVals.Tokens
                         module Interface = Interface
                         module Lexer = Lexer
                       end) 
module DelphinParser : PARSERR =
  (Join)(struct
                module ParserData = DelphinLrVals.ParserData
                module Lex = DelphinLex
                module LrParser = LrParser
              end) 
module Parse : PARSE =
  (Parse)(struct
                 module DextSyn = DextSyn
                 module Interface = Interface
                 module Parserr = DelphinParser
                 module Tokens = DelphinLrVals.Tokens
               end) 
module Trans : TRANS = (Trans)(struct module DextSyn' = DextSyn end) 
module Delphin =
  (Delphin)(struct
                   module Twelf = Twelf
                   module Parse = Parse
                   module DextSyn = DextSyn
                   module Trans = Trans
                   module Parser = Parser
                 end)