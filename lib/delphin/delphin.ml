
module type DELPHIN  =
  sig
    val version : string
    val loadFile : string -> string -> unit
    val top : unit -> unit
    val runSimpleTest : string -> string list -> string list -> unit
    val eval : Tomega.__Prg -> Tomega.__Prg
  end;;




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
    exception What of Tomega.__Prg 
    module I = IntSyn
    module T = Tomega
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec loadFile s1 s2 =
      let _ = Twelf.reset () in
      let _ = Twelf.loadFile s1 in
      let _ = chatter 1 (fun () -> ("[Opening file " ^ s2) ^ "]\n") in
      let _ = Trans.internalizeSig () in
      let _ = chatter 4 (fun () -> "[Parsing ...") in
      let Ast (EDs) = Parse.gparse s2 in
      let _ = chatter 4 (fun () -> "]\n[Translation ...") in
      let __P = Trans.transDecs EDs in
      let _ = chatter 4 (fun () -> "]\n[Externalization ...") in
      let __P' = Trans.externalizePrg __P in
      let _ = chatter 4 (fun () -> "]\n") in
      let _ = chatter 4 (fun () -> "[Operational Semantics ...") in
      let __V = Opsem.topLevel __P' in
      let _ = chatter 4 (fun () -> "]\n") in
      let _ = chatter 1 (fun () -> ("[Closing file " ^ s2) ^ "]\n") in ((__V)
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
        function
        | name::[] as names ->
            let La =
              map
                (fun x ->
                   valOf (Names.constLookup (valOf (Names.stringToQid x))))
                names in
            let (lemma, projs, sels) = Converter.installPrg La in
            let __P = Tomega.lemmaDef lemma in
            let __F = Converter.convertFor La in
            let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F)) in
            let _ =
              TextIO.print
                (((^) "\n" TomegaPrint.funToString
                    (((map
                         (fun cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                         La), projs), __P))
                   ^ "\n") in
            (((__P, __F))
              (*           val P = Redundant.convert (Tomega.lemmaDef lemma) *))
        | names ->
            let La =
              map
                (fun x ->
                   valOf (Names.constLookup (valOf (Names.stringToQid x))))
                names in
            let (lemma, projs, sels) = Converter.installPrg La in
            let __P = Redundant.convert (Tomega.lemmaDef lemma) in
            let __F = Converter.convertFor La in
            let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F)) in
            let _ =
              TextIO.print
                (((^) "\n" TomegaPrint.funToString
                    (((map
                         (fun cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                         La), projs), __P))
                   ^ "\n") in
            ((((Tomega.lemmaDef (hd sels)), __F))
              (* val P = Tomega.lemmaDef lemma *)) in
      let rec checkDec u (UDec (Dec (_, __V)) as D) =
        print "$"; TypeCheck.typeCheck (I.Null, (u, __V)) in
      let rec makeSpine __0__ __1__ =
        match (__0__, __1__) with
        | ([], __F) -> (T.Nil, __F)
        | (x::__L, (And (__F1, __F2) as F')) ->
            let (__S', __F') =
              makeSpine
                (__L,
                  (T.forSub
                     (__F',
                       (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
            ((T.AppExp ((I.Root ((I.Def x), I.Nil)), __S')), __F')
        | (x::__L, All ((__D, _), __F')) ->
            let _ = checkDec ((I.Root ((I.Def x), I.Nil)), __D) in
            let (__S', __F') =
              makeSpine
                (__L,
                  (T.forSub
                     (__F',
                       (T.Dot ((T.Exp (I.Root ((I.Def x), I.Nil))), T.id))))) in
            ((T.AppExp ((I.Root ((I.Def x), I.Nil)), __S')), __F') in
      let _ = Twelf.make sourcesFile in
      let (__P, __F) = test funcList in
      let _ = print ((TomegaPrint.forToString (I.Null, __F)) ^ "\n") in
      let xs =
        map
          (fun a -> valOf (Names.constLookup (valOf (Names.stringToQid a))))
          args in
      let (__S', __F') = makeSpine (xs, __F) in
      let __P' = T.Redex (__P, __S') in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (__P', __F')) in
      let result = Opsem.evalPrg __P' in
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
    let rec eval (__P) = let __V = Opsem.evalPrg __P in __V
    let version = version
    let loadFile = loadFile
    let top = top
    let runSimpleTest = runSimpleTest
    let eval = eval
  end ;;




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
                   module Twelf = Twelf
                   module Parse = Parse
                   module DextSyn = DextSyn
                   module Trans = Trans
                   module Parser = Parser
                 end);;
