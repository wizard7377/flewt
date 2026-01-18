
(* Delphin Frontend *)
(* Author: Carsten Schuermann *)
module type DELPHIN  =
  sig
    val version : string
    val loadFile : (string * string) -> unit
    val top : unit -> unit
    val runSimpleTest : string -> string list -> string list -> unit
    val eval : Tomega.__Prg -> Tomega.__Prg
  end;;




(* Delphin Frontend *)
(* Author: Carsten Schuermann *)
module Delphin(Delphin:sig
                         (* structure Tomega : TOMEGA *)
                         module Parser : PARSER
                         module DextSyn : DEXTSYN
                         module Parse : PARSE
                         module Twelf : TWELF
                         module Trans : TRANS
                       end) : DELPHIN =
  struct
    let version = "Delphin, Version 0.5, July 2003"
    let prompt = "> "
    exception What of Tomega.__Prg 
    module I = IntSyn
    module T = Tomega
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec loadFile (s1, s2) =
      let _ = Twelf.reset () in
      let _ = Twelf.loadFile s1 in
      let _ = chatter 1 (function | () -> ("[Opening file " ^ s2) ^ "]\n") in
      let _ = Trans.internalizeSig () in
      let _ = chatter 4 (function | () -> "[Parsing ...") in
      let Ast (EDs) = Parse.gparse s2 in
      let _ = chatter 4 (function | () -> "]\n[Translation ...") in
      let P = Trans.transDecs EDs in
      let _ = chatter 4 (function | () -> "]\n[Externalization ...") in
      let P' = Trans.externalizePrg P in
      let _ = chatter 4 (function | () -> "]\n") in
      let _ = chatter 4 (function | () -> "[Operational Semantics ...") in
      let V = Opsem.topLevel P' in
      let _ = chatter 4 (function | () -> "]\n") in
      let _ = chatter 1 (function | () -> ("[Closing file " ^ s2) ^ "]\n") in
      V
    let rec top () = loop ()
    let rec loop () =
      let _ = print prompt in let Ast (ED) = Parse.sparse () in loop ()
    let rec runSimpleTest sourcesFile funcList args =
      let rec test =
        function
        | name::[] as names ->
            let La =
              map
                (function
                 | x ->
                     valOf (Names.constLookup (valOf (Names.stringToQid x))))
                names in
            let (lemma, projs, sels) = Converter.installPrg La in
            let P = Tomega.lemmaDef lemma in
            let F = Converter.convertFor La in
            let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
            let _ =
              TextIO.print
                (((^) "\n" TomegaPrint.funToString
                    (((map
                         (function
                          | cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                         La), projs), P))
                   ^ "\n") in
            (P, F)
        | names ->
            let La =
              map
                (function
                 | x ->
                     valOf (Names.constLookup (valOf (Names.stringToQid x))))
                names in
            let (lemma, projs, sels) = Converter.installPrg La in
            let P = Redundant.convert (Tomega.lemmaDef lemma) in
            let F = Converter.convertFor La in
            let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
            let _ =
              TextIO.print
                (((^) "\n" TomegaPrint.funToString
                    (((map
                         (function
                          | cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                         La), projs), P))
                   ^ "\n") in
            ((Tomega.lemmaDef (hd sels)), F) in
      let rec checkDec (u, (UDec (Dec (_, V)) as D)) =
        print "$"; TypeCheck.typeCheck (I.Null, (u, V)) in
      let rec makeSpine =
        function
        | ([], F) -> (T.Nil, F)
        | (x::L, (And (F1, F2) as F')) ->
            let (S', F') =
              makeSpine
                (L,
                  (T.forSub
                     (F',
                       (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
            ((T.AppExp ((I.Root ((I.Def x), I.Nil)), S')), F')
        | (x::L, All ((D, _), F')) ->
            let _ = checkDec ((I.Root ((I.Def x), I.Nil)), D) in
            let (S', F') =
              makeSpine
                (L,
                  (T.forSub
                     (F',
                       (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
            ((T.AppExp ((I.Root ((I.Def x), I.Nil)), S')), F') in
      let _ = Twelf.make sourcesFile in
      let (P, F) = test funcList in
      let _ = print ((TomegaPrint.forToString (I.Null, F)) ^ "\n") in
      let xs =
        map
          (function
           | a -> valOf (Names.constLookup (valOf (Names.stringToQid a))))
          args in
      let (S', F') = makeSpine (xs, F) in
      let P' = T.Redex (P, S') in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (P', F')) in
      let result = Opsem.evalPrg P' in
      let _ = TextIO.print "\n\nEOC\n\n" in
      let _ = TextIO.print (TomegaPrint.prgToString (I.Null, result)) in
      let _ = TextIO.print "\n" in ()
    let rec eval (P) = let V = Opsem.evalPrg P in V
    (* Added by ABP - Temporary to run tests *)
    (*      val _ = print "* Type reconstruction done\n" *)
    (*      val _ = raise What P'
        val _ = print "* Externalization done\n" *)
    (*      val _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P', Tomega.True))
        val _ = print "* Typechecking done\n"
*)
    (* was evalPrg --cs Mon Jun 30 12:09:21 2003*)
    (*      val _ = print "* Operational semantics done\n" *)
    (*         val res = Trans.transDecs ED    *)
    (* input:
      sourcesFile = .elf file to load
      funcList = list of functions that need to be loaded
                 first element is the function that will be called
      arg = LF object which is the argument
   *)
    (*           val P = Redundant.convert (Tomega.lemmaDef lemma) *)
    (* val P = Tomega.lemmaDef lemma *)
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
    (*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *)
    (* **************************************** *)
    let version = version
    let loadFile = loadFile
    let top = top
    let runSimpleTest = runSimpleTest
    let eval = eval
  end ;;




(* Delphin Front End Interface *)
(* Author: Carsten Schuermann *)
module DextSyn : DEXTSYN =
  (Make_DextSyn)(struct
                   module Stream' = Stream
                   module ParseTerm' = ParseTerm
                   module ExtSyn' = ParseTerm.ExtSyn
                   module Parsing' = Parsing
                   module Lexer' = Lexer
                 end) 
module DelphinLrVals : Delphin_LRVALS =
  (Make_DelphinLrValsFun)(struct
                            module Token = LrParser.Token
                            module DextSyn' = DextSyn
                            module Stream = Stream
                            module Lexer' = Lexer
                            module Parsing' = Parsing
                          end) 
module Interface : INTERFACE = (Make_Interface)(struct  end) 
module DelphinLex : LEXERR =
  (Make_DelphinLexFun)(struct
                         module Tokens = DelphinLrVals.Tokens
                         module Interface = Interface
                         module Lexer = Lexer
                       end) 
module DelphinParser : PARSERR =
  (Make_Join)(struct
                module ParserData = DelphinLrVals.ParserData
                module Lex = DelphinLex
                module LrParser = LrParser
              end) 
module Parse : PARSE =
  (Make_Parse)(struct
                 module DextSyn = DextSyn
                 module Interface = Interface
                 module Parserr = DelphinParser
                 module Tokens = DelphinLrVals.Tokens
               end) 
module Trans : TRANS = (Make_Trans)(struct module DextSyn' = DextSyn end) 
module Delphin =
  (Make_Delphin)(struct
                   (* structure Tomega = Tomega *)
                   module Twelf = Twelf
                   module Parse = Parse
                   module DextSyn = DextSyn
                   module Trans = Trans
                   module Parser = Parser
                 end);;
