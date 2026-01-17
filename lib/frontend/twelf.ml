
module type TWELF  =
  sig
    module Print :
    sig
      val implicit :
        ((bool)(* Author: Frank Pfenning *)(* Front End Interface *))
          ref
      val printInfix :
        ((bool)(* false, print implicit args *)) ref
      val depth :
        ((int)(* false, print fully explicit form infix when possible *))
          option ref
      val length :
        ((int)(* NONE, limit print depth *)) option ref
      val indent :
        ((int)(* NONE, limit argument length *)) ref
      val width :
        ((int)(* 3, indentation of subterms *)) ref
      val noShadow : ((bool)(* 80, line width *)) ref
      val sgn :
        unit ->
          ((unit)(* if true, don't print shadowed constants as "%const%" *))
      val prog : unit -> ((unit)(* print signature *))
      val subord :
        unit -> ((unit)(* print signature as program *))
      val def :
        unit -> ((unit)(* print subordination relation *))
      val domains :
        unit ->
          ((unit)(* print information about definitions *))
      module TeX :
      sig
        val sgn :
          unit ->
            ((unit)(* print in TeX format *)(* print available constraint domains *))
        val prog : unit -> ((unit)(* print signature *))
      end
    end
    module Trace :
    sig
      type 'a __Spec =
        | None 
        | Some of
        (('a)(* no tracing, default *)(* trace and breakpoint spec *)
        (* print signature as program *)) list 
        | All 
      val trace :
        string __Spec ->
          ((unit)(* trace all clauses and families *)
          (* list of clauses and families *))
      val break :
        string __Spec ->
          ((unit)(* trace clauses and families *))
      val detail :
        ((int)(* break at clauses and families *)) ref
      val show :
        unit ->
          ((unit)(* 0 = none, 1 = default, 2 = unify *))
      val reset :
        unit -> ((unit)(* show trace, break, and detail *))
    end
    module Table :
    sig
      type __Strategy =
        | Variant 
        | Subsumption (* reset trace, break, and detail *)
      val strategy :
        ((__Strategy)(* Variant | Subsumption *)) ref
      val strengthen :
        ((bool)(* strategy used for %querytabled *)) ref
      val resetGlobalTable :
        unit -> ((unit)(* strengthenng used %querytabled *))
      val top :
        unit -> ((unit)(* reset global table           *))
    end
    module Timers :
    sig
      val show :
        unit ->
          ((unit)(* top-level for interactive tabled queries *))
      val reset :
        unit -> ((unit)(* show and reset timers *))
      val check : unit -> ((unit)(* reset timers *))
    end
    module OS :
    sig
      val chDir :
        string -> ((unit)(* display, but not no reset *))
      val getDir :
        unit -> ((string)(* change working directory *))
      val exit : unit -> ((unit)(* get working directory *))
    end
    module Compile :
    sig
      type __Opt =
        | No 
        | LinearHeads 
        | Indexing (* exit Twelf and ML *)
      val optimize : __Opt ref
    end
    module Recon :
    sig
      type __TraceMode =
        | Progressive 
        | Omniscient 
      val trace : bool ref
      val traceMode : __TraceMode ref
    end
    module Prover :
    sig
      type __Strategy =
        | RFS 
        | FRS 
      val strategy :
        ((__Strategy)(* F=Filling, R=Recursion, S=Splitting *))
          ref
      val maxSplit :
        ((int)(* FRS, strategy used for %prove *)) ref
      val maxRecurse :
        ((int)(* 2, bound on splitting  *)) ref
    end
    val chatter : ((int)(* 10, bound on recursion *)) ref
    val doubleCheck : ((bool)(* 3, chatter level *)) ref
    val unsafe :
      ((bool)(* false, check after reconstruction *)) ref
    val autoFreeze : ((bool)(* false, allows %assert *)) ref
    val timeLimit :
      ((Time.time)(* false, freezes families in meta-theorems *))
        option ref
    type __Status =
      | OK 
      | ABORT (* NONEe, allows timeLimit in seconds *)
    val reset : unit -> ((unit)(* return status *))
    val loadFile :
      string -> ((__Status)(* reset global signature *))
    val loadString : string -> ((__Status)(* load file *))
    val readDecl : unit -> ((__Status)(* load string *))
    val decl :
      string ->
        ((__Status)(* read declaration interactively *))
    val top :
      unit -> ((unit)(* print declaration of constant *))
    module Config :
    sig
      type nonrec config(* top-level for interactive queries *)
      val suffix : ((string)(* configuration *)) ref
      val read :
        string ->
          ((config)(* suffix of configuration files *))
      val readWithout :
        (string * config) ->
          ((config)(* read config file *))
      val load :
        config ->
          ((__Status)(* read config file, minus contents of another *))
      val append :
        config ->
          ((__Status)(* reset and load configuration *))
      val define :
        string list ->
          ((config)(* load configuration (w/o reset) *))
    end
    val make :
      string ->
        ((__Status)(* explicitly define configuration *))
    val version :
      ((string)(* read and load configuration *))
  end;;




module Twelf(Twelf:sig
                     module Global : GLOBAL
                     module Timers : TIMERS
                     module Whnf : WHNF
                     module Print : PRINT
                     module Names : NAMES
                     module Origins : ORIGINS
                     module Lexer : LEXER
                     module Parser : PARSER
                     module TypeCheck : TYPECHECK
                     module Strict : STRICT
                     module Constraints : CONSTRAINTS
                     module Abstract : ABSTRACT
                     module ReconTerm : RECON_TERM
                     module ReconConDec : RECON_CONDEC
                     module ReconQuery : RECON_QUERY
                     module ModeTable : MODETABLE
                     module ModeCheck : MODECHECK
                     module ReconMode : RECON_MODE
                     module ModePrint : MODEPRINT
                     module ModeDec : MODEDEC
                     module StyleCheck : STYLECHECK
                     module Unique : UNIQUE
                     module UniqueTable : MODETABLE
                     module Cover : COVER
                     module Converter : CONVERTER
                     module TomegaPrint : TOMEGAPRINT
                     module TomegaCoverage : TOMEGACOVERAGE
                     module TomegaTypeCheck : TOMEGATYPECHECK
                     module Total : TOTAL
                     module Reduces : REDUCES
                     module Index : INDEX
                     module IndexSkolem : INDEX
                     module Subordinate : SUBORDINATE
                     module Compile : COMPILE
                     module AbsMachine : ABSMACHINE
                     module Tabled : TABLED
                     module Solve : SOLVE
                     module Fquery : FQUERY
                     module ThmSyn : THMSYN
                     module Thm : THM
                     module ReconThm : RECON_THM
                     module ThmPrint : THMPRINT
                     module TabledSyn : TABLEDSYN
                     module WorldSyn : WORLDSYN
                     module Worldify : WORLDIFY
                     module ModSyn : MODSYN
                     module ReconModule : RECON_MODULE
                     module MetaGlobal : METAGLOBAL
                     module Skolem : SKOLEM
                     module Prover : PROVER
                     module ClausePrint : CLAUSEPRINT
                     module Trace : TRACE
                     module PrintTeX : PRINT
                     module ClausePrintTeX : CLAUSEPRINT
                     module CSManager : CS_MANAGER
                     module CSInstaller : CS_INSTALLER
                     module Compat : COMPAT
                     module UnknownExn : UNKNOWN_EXN
                     module Msg :
                     ((MSG)(* Front End Interface *)
                     (* Author: Frank Pfenning *)(* Modified: Carsten Schuermann, Jeff Polakow *)
                     (* Modified: Brigitte Pientka, Roberto Virga *)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! structure Paths : PATHS !*)
                     (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Lexer.Paths = Paths !*)
                     (*! structure Parsing : PARSING !*)
                     (*! sharing Lexer = Lexer !*)(*! sharing Parser.ExtSyn.Paths = Paths !*)
                     (*! sharing Strict.IntSyn = IntSyn' !*)
                     (*! sharing Strict.Paths = Paths !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)(*! sharing ReconTerm.IntSyn = IntSyn' !*)
                     (*! sharing ReconTerm.Paths = Paths !*)
                     (* sharing type ReconTerm.Paths.occConDec = Origins.Paths.occConDec *)
                     (*! sharing ReconConDec.IntSyn = IntSyn' !*)
                     (*! sharing ReconConDec.Paths = Paths !*)(*! sharing ModeSyn.IntSyn = IntSyn' !*)
                     (*! sharing ModeCheck.IntSyn = IntSyn' !*)(*! sharing ModeCheck.ModeSyn = ModeSyn !*)
                     (*! sharing ModeCheck.Paths = Paths !*)
                     (*! sharing ReconMode.ModeSyn = ModeSyn !*)
                     (*! sharing ReconMode.Paths = Paths !*)
                     (*! sharing ModePrint.ModeSyn = ModeSyn !*)
                     (*! sharing ModeDec.ModeSyn = ModeSyn !*)(*! sharing ModeDec.Paths = Paths !*)
                     (*! sharing Unique.ModeSyn = ModeSyn !*)(*! sharing Cover.IntSyn = IntSyn' !*)
                     (*! sharing Cover.ModeSyn = ModeSyn !*)
                     (*! sharing Converter.IntSyn = IntSyn' !*)(*! sharing Converter.Tomega = Tomega !*)
                     (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
                     (*! sharing TomegaPrint.Tomega = Tomega !*)
                     (*! sharing TomegaCoverage.IntSyn = IntSyn' !*)
                     (*! sharing TomegaCoverage.Tomega = Tomega !*)
                     (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
                     (*! sharing TomegaTypeCheck.Tomega = Tomega !*)
                     (*! sharing Total.IntSyn = IntSyn' !*)
                     (*! sharing Reduces.IntSyn = IntSyn' !*)(*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
                     (*! sharing Subordinate.IntSyn = IntSyn' !*)
                     (*! structure CompSyn' : COMPSYN !*)
                     (*! sharing CompSyn'.IntSyn = IntSyn' !*)(*! sharing Compile.IntSyn = IntSyn' !*)
                     (*! sharing Compile.CompSyn = CompSyn' !*)(*! sharing AbsMachine.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachine.CompSyn = CompSyn' !*)
                     (*! structure TableParam : TABLEPARAM !*)(*! sharing Tabled.IntSyn = IntSyn' !*)
                     (*! sharing Tabled.CompSyn = CompSyn' !*)(*! sharing Solve.IntSyn = IntSyn' !*)
                     (*! sharing Fquery.IntSyn = IntSyn' !*)
                     (*! sharing Solve.Paths = Paths !*)
                     (*! sharing ThmSyn.Paths = Paths !*)
                     (*! sharing Thm.Paths = Paths !*)
                     (*! sharing ReconThm.Paths = Paths !*)
                     (*! sharing ReconThm.ThmSyn.ModeSyn = ModeSyn !*)
                     (* -bp *)(* -bp *)
                     (* -bp *)(*! sharing TabledSyn.IntSyn = IntSyn' !*)
                     (*! sharing WorldSyn.IntSyn = IntSyn' !*)(*   structure WorldPrint : WORLDPRINT *)
                     (*! sharing WorldPrint.Tomega = Tomega !*)(*! sharing ModSyn.IntSyn = IntSyn' !*)
                     (*! sharing ModSyn.Paths = Paths !*)
                     (*! structure FunSyn : FUNSYN !*)
                     (*! sharing FunSyn.IntSyn = IntSyn' !*)
                     (*! sharing Skolem.IntSyn = IntSyn' !*)
                     (*! sharing Prover.IntSyn = IntSyn' !*)
                     (*! sharing ClausePrint.IntSyn = IntSyn' !*)
                     (*! sharing PrintTeX.IntSyn = IntSyn' !*)(*! sharing ClausePrintTeX.IntSyn = IntSyn' !*)
                     (*! sharing CSManager.IntSyn = IntSyn' !*)(*! sharing CSManager.ModeSyn = ModeSyn !*))
                   end) : TWELF =
  struct
    module S = Parser.Stream
    let rec msg s = Msg.message s
    let rec chmsg n s = Global.chMessage n s msg
    let rec fileOpenMsg fileName =
      match !Global.chatter with
      | 0 -> ()
      | 1 -> msg (("[Loading file " ^ fileName) ^ " ...")
      | _ -> msg (("[Opening file " ^ fileName) ^ "]\n")
    let rec fileCloseMsg fileName =
      match !Global.chatter with
      | 0 -> ()
      | 1 -> msg "]\n"
      | _ -> msg (("[Closing file " ^ fileName) ^ "]\n")
    type 'a __Result =
      | Value of 'a 
      | Exception of exn 
    let rec withOpenIn fileName scope =
      let instream = TextIO.openIn fileName in
      let _ = fileOpenMsg fileName in
      let result = try Value (scope instream) with | exn -> Exception exn in
      let _ = fileCloseMsg fileName in
      let _ = TextIO.closeIn instream in
      match result with | Value x -> x | Exception exn -> raise exn
    let rec evarInstToString (Xs) =
      if (!Global.chatter) >= 3 then Print.evarInstToString Xs else ""
    let rec expToString (GU) =
      if (!Global.chatter) >= 3 then Print.expToString GU else ""
    let rec printProgTeX () =
      msg "\\begin{bigcode}\n";
      ClausePrintTeX.printSgn ();
      msg "\\end{bigcode}\n"
    let rec printSgnTeX () =
      msg "\\begin{bigcode}\n"; PrintTeX.printSgn (); msg "\\end{bigcode}\n"
    type __Status =
      | OK 
      | ABORT 
    let rec abort chlev msg = chmsg chlev (function | () -> msg); ABORT
    let rec abortFileMsg chlev (fileName, msg) =
      abort chlev (((fileName ^ ":") ^ msg) ^ "\n")
    let rec abortIO =
      function
      | (fileName,
         { cause = SysErr (m, _); function__ = f; name = n; function__ = f;
           name = n; name = n })
          ->
          (msg (((("IO Error on file " ^ fileName) ^ ":\n") ^ m) ^ "\n");
           ABORT)
      | (fileName, { function__ = f }) ->
          (msg
             (((("IO Error on file " ^ fileName) ^ " from function ") ^ f) ^
                "\n");
           ABORT)
    let rec joinregion =
      function
      | (r, nil) -> r
      | (r, r'::rs) -> joinregion ((Paths.join (r, r')), rs)
    let rec joinregions (r::rs) = joinregion (r, rs)
    let rec constraintsMsg cnstrL =
      (^) "Typing ambiguous -- unresolved constraints\n" Print.cnstrsToString
        cnstrL
    let rec handleExceptions chlev fileName (f : 'a -> __Status) (x : 'a) =
      try f x
      with | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg ->
          abort 0
            ((("Double-checking types fails: " ^ msg) ^ "\n") ^
               "This indicates a bug in Twelf.\n")
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abort chlev (msg ^ "\n")
      | Error msg -> abort chlev (msg ^ "\n")
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abort chlev (msg ^ "\n")
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abort chlev (("Signature error: " ^ msg) ^ "\n")
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | AbortQuery msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abort chlev (msg ^ "\n")
      | Error msg -> abort chlev (msg ^ "\n")
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg -> abortFileMsg chlev (fileName, msg)
      | Error msg ->
          abort chlev (("Constraint Solver Manager error: " ^ msg) ^ "\n")
      | exn -> (abort 0 (UnknownExn.unknownExn exn); raise exn)
    let (context : Names.namespace option ref) = ref NONE
    let rec installConst fromCS (cid, fileNameocOpt) =
      let _ = Origins.installOrigin (cid, fileNameocOpt) in
      let _ = Index.install fromCS (IntSyn.Const cid) in
      let _ = IndexSkolem.install fromCS (IntSyn.Const cid) in
      let _ = Timers.time Timers.compiling Compile.install fromCS cid in
      let _ = Timers.time Timers.subordinate Subordinate.install cid in
      let _ = Timers.time Timers.subordinate Subordinate.installDef cid in ()
    let rec installConDec fromCS
      (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
      let _ =
        Timers.time Timers.modes ModeCheck.checkD (conDec, fileName, ocOpt) in
      let cid = IntSyn.sgnAdd conDec in
      let _ =
        try
          match (fromCS, (!context)) with
          | (IntSyn.Ordinary, SOME namespace) ->
              Names.insertConst (namespace, cid)
          | (IntSyn.Clause, SOME namespace) ->
              Names.insertConst (namespace, cid)
          | _ -> ()
        with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
      let _ = Names.installConstName cid in
      let _ =
        try installConst fromCS (cid, fileNameocOpt)
        with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
      let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
      let _ = if (!Global.style) >= 1 then StyleCheck.checkConDec cid else () in
      cid
    let rec installBlockDec fromCS
      (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
      let cid = IntSyn.sgnAdd conDec in
      let _ =
        try
          match (fromCS, (!context)) with
          | (IntSyn.Ordinary, SOME namespace) ->
              Names.insertConst (namespace, cid)
          | _ -> ()
        with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
      let _ = Names.installConstName cid in
      let _ =
        try Timers.time Timers.subordinate Subordinate.installBlock cid
        with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
      let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
      cid
    let rec installBlockDef fromCS
      (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
      let cid = IntSyn.sgnAdd conDec in
      let _ =
        try
          match (fromCS, (!context)) with
          | (IntSyn.Ordinary, SOME namespace) ->
              Names.insertConst (namespace, cid)
          | _ -> ()
        with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
      let _ = Names.installConstName cid in
      let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
      cid
    let rec installStrDec (strdec, module__, r, isDef) =
      let installAction ((cid, _) as data) =
        installConst IntSyn.Ordinary data;
        if (!Global.chatter) >= 4
        then msg ((Print.conDecToString (IntSyn.sgnLookup cid)) ^ "\n")
        else () in
      let _ =
        try
          ModSyn.installStruct
            (strdec, module__, (!context), installAction, isDef)
        with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
      ()
    let rec includeSig (module__, r, isDef) =
      let installAction ((cid, _) as data) =
        installConst IntSyn.Ordinary data;
        if (!Global.chatter) >= 4
        then msg ((Print.conDecToString (IntSyn.sgnLookup cid)) ^ "\n")
        else () in
      let _ =
        try ModSyn.installSig (module__, (!context), installAction, isDef)
        with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
      ()
    let rec cidToString a = Names.qidToString (Names.constQid a)
    let rec invalidate uninstallFun cids msg =
      let uninstalledCids = List.filter (function | a -> uninstallFun a) cids in
      let _ =
        match uninstalledCids with
        | nil -> ()
        | _ ->
            chmsg 4
              (function
               | () ->
                   (^) (("Invalidated " ^ msg) ^ " properties of families")
                     List.foldr
                     ((function | (a, s) -> ((^) " " cidToString a) ^ s))
                     "\n" uninstalledCids) in
      ()
    let rec install1 =
      function
      | (fileName, (ConDec condec, r)) ->
          (try
             let (optConDec, ocOpt) =
               ReconConDec.condecToConDec
                 (condec, (Paths.Loc (fileName, r)), false__) in
             let icd =
               function
               | SOME (BlockDec _ as conDec) ->
                   let cid =
                     installBlockDec IntSyn.Ordinary
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | SOME (BlockDef _ as conDec) ->
                   let cid =
                     installBlockDef IntSyn.Ordinary
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | SOME conDec ->
                   let cid =
                     installConDec IntSyn.Ordinary
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | NONE -> () in
             icd optConDec
           with
           | Error eqns ->
               raise
                 (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))))
      | (fileName, (AbbrevDec condec, r)) ->
          (try
             let (optConDec, ocOpt) =
               ReconConDec.condecToConDec
                 (condec, (Paths.Loc (fileName, r)), true__) in
             let icd =
               function
               | SOME conDec ->
                   let cid =
                     installConDec IntSyn.Ordinary
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | NONE -> () in
             icd optConDec
           with
           | Error eqns ->
               raise
                 (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))))
      | (fileName, (ClauseDec condec, r)) ->
          (try
             let (optConDec, ocOpt) =
               ReconConDec.condecToConDec
                 (condec, (Paths.Loc (fileName, r)), false__) in
             let icd =
               function
               | SOME conDec ->
                   let cid =
                     installConDec IntSyn.Clause
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | NONE -> () in
             icd optConDec
           with
           | Error eqns ->
               raise
                 (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))))
      | (fileName, (Solve (defines, solve), r)) ->
          (try
             let conDecL =
               try Solve.solve (defines, solve, (Paths.Loc (fileName, r)))
               with
               | AbortQuery msg ->
                   raise (Solve.AbortQuery (Paths.wrap (r, msg))) in
             let icd (conDec, ocOpt) =
               let cid =
                 installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in
               () in
             List.app icd conDecL
           with
           | Error eqns ->
               raise
                 (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))))
      | (fileName, (Query (expected, try__, query), r)) ->
          (try
             Solve.query
               ((expected, try__, query), (Paths.Loc (fileName, r)))
           with
           | AbortQuery msg -> raise (Solve.AbortQuery (Paths.wrap (r, msg))))
      | (fileName, (FQuery query, r)) ->
          (try Fquery.run (query, (Paths.Loc (fileName, r)))
           with
           | AbortQuery msg ->
               raise (Fquery.AbortQuery (Paths.wrap (r, msg))))
      | (fileName, (Querytabled (numSol, try__, query), r)) ->
          (try
             Solve.querytabled
               ((numSol, try__, query), (Paths.Loc (fileName, r)))
           with
           | AbortQuery msg -> raise (Solve.AbortQuery (Paths.wrap (r, msg))))
      | (fileName, (TrustMe (dec, r'), r)) ->
          let _ =
            if not (!Global.unsafe)
            then raise (Thm.Error "%trustme not safe: Toggle `unsafe' flag")
            else () in
          let _ = chmsg 3 (function | () -> "[%trustme ...\n") in
          let _ =
            match handleExceptions 4 fileName
                    (function | args -> (install1 args; OK))
                    (fileName, (dec, r))
            with
            | OK -> chmsg 3 (function | () -> "trustme subject succeeded\n")
            | ABORT ->
                chmsg 3
                  (function | () -> "trustme subject failed; continuing\n") in
          let _ = chmsg 3 (function | () -> "%]\n") in ()
      | (fileName, (SubordDec qidpairs, r)) ->
          let toCid qid =
            match Names.constLookup qid with
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in subord declaration"))
            | SOME cid -> cid in
          let cidpairs =
            try
              List.map
                (function | (qid1, qid2) -> ((toCid qid1), (toCid qid2)))
                qidpairs
            with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
          let _ =
            try List.app Subordinate.addSubord cidpairs
            with
            | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
          if (!Global.chatter) >= 3
          then
            msg
              ((^) "%subord" List.foldr
                 (function
                  | ((a1, a2), s) ->
                      (((^) (((^) " (" Names.qidToString (Names.constQid a1))
                               ^ " ")
                          Names.qidToString (Names.constQid a2))
                         ^ ")")
                        ^ s)
                 ".\n" cidpairs)
          else ()
      | (fileName, (FreezeDec qids, r)) ->
          let toCid qid =
            match Names.constLookup qid with
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in freeze declaration"))
            | SOME cid -> cid in
          let cids =
            try List.map toCid qids
            with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
          let frozen =
            try Subordinate.freeze cids
            with
            | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
          (if (!Global.chatter) >= 3
           then
             msg
               ((^) "%freeze" List.foldr
                  (function
                   | (a, s) ->
                       ((^) " " Names.qidToString (Names.constQid a)) ^ s)
                  ".\n" cids)
           else ();
           if (!Global.chatter) >= 4
           then
             msg
               ((^) "Frozen:" List.foldr
                  (function
                   | (a, s) ->
                       ((^) " " Names.qidToString (Names.constQid a)) ^ s)
                  "\n" frozen)
           else ())
      | (fileName, (ThawDec qids, r)) ->
          let _ =
            if not (!Global.unsafe)
            then raise (ThmSyn.Error "%thaw not safe: Toggle `unsafe' flag")
            else () in
          let toCid qid =
            match Names.constLookup qid with
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in thaw declaration"))
            | SOME cid -> cid in
          let cids =
            try List.map toCid qids
            with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
          let thawed =
            try Subordinate.thaw cids
            with
            | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                ((^) "%thaw" List.foldr
                   (function | (a, s) -> ((^) " " cidToString a) ^ s) ".\n"
                   cids)
            else () in
          let _ =
            if (!Global.chatter) >= 4
            then
              msg
                ((^) "Thawed" List.foldr
                   (function | (a, s) -> ((^) " " cidToString a) ^ s) "\n"
                   thawed)
            else () in
          let _ = invalidate WorldSyn.uninstall thawed "world" in
          let _ = invalidate Thm.uninstallTerminates thawed "termination" in
          let _ = invalidate Thm.uninstallReduces thawed "reduction" in
          let _ = invalidate UniqueTable.uninstallMode thawed "uniqueness" in
          let _ = invalidate Total.uninstall thawed "totality" in ()
      | (fileName, (DeterministicDec qids, r)) ->
          let toCid qid =
            match Names.constLookup qid with
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in deterministic declaration"))
            | SOME cid -> cid in
          let insertCid cid = CompSyn.detTableInsert (cid, true__) in
          let cids =
            try List.map toCid qids
            with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
          (List.map insertCid cids;
           if (!Global.chatter) >= 3
           then
             msg
               ((^) ((if (!Global.chatter) >= 4 then "%" else "") ^
                       "%deterministic")
                  List.foldr
                  (function
                   | (a, s) ->
                       ((^) " " Names.qidToString (Names.constQid a)) ^ s)
                  ".\n" cids)
           else ())
      | (fileName, (Compile qids, r)) ->
          let toCid qid =
            match Names.constLookup qid with
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in compile assertion"))
            | SOME cid -> cid in
          let cids =
            try List.map toCid qids
            with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in
          let checkFreeOut =
            function
            | nil -> ()
            | a::La ->
                let SOME ms = ModeTable.modeLookup a in
                let _ = ModeCheck.checkFreeOut (a, ms) in checkFreeOut La in
          let _ = checkFreeOut cids in
          let (lemma, projs, sels) = Converter.installPrg cids in
          let P = Tomega.lemmaDef lemma in
          let F = Converter.convertFor cids in
          let _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F)) in
          let f cid = IntSyn.conDecName (IntSyn.sgnLookup cid) in
          let _ =
            if (!Global.chatter) >= 2
            then
              msg
                (((^) "\n" TomegaPrint.funToString (((map f cids), projs), P))
                   ^ "\n")
            else () in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                ((^) ((if (!Global.chatter) >= 4 then "%" else "") ^
                        "%compile")
                   List.foldr
                   (function
                    | (a, s) ->
                        ((^) " " Names.qidToString (Names.constQid a)) ^ s)
                   ".\n" cids)
            else () in
          ()
      | (fileName, (FixDec ((qid, r), fixity), _)) ->
          (match Names.constLookup qid with
           | NONE ->
               raise
                 (Names.Error
                    (((^) "Undeclared identifier " Names.qidToString
                        (valOf (Names.constUndef qid)))
                       ^ " in fixity declaration"))
           | SOME cid ->
               (try
                  Names.installFixity (cid, fixity);
                  if (!Global.chatter) >= 3
                  then
                    msg
                      (((^) (((^) (if (!Global.chatter) >= 4 then "%" else "")
                                Names.Fixity.toString fixity)
                               ^ " ")
                          Names.qidToString (Names.constQid cid))
                         ^ ".\n")
                  else ()
                with | Error msg -> raise (Names.Error (Paths.wrap (r, msg)))))
      | (fileName, (NamePref ((qid, r), namePref), _)) ->
          (match Names.constLookup qid with
           | NONE ->
               raise
                 (Names.Error
                    (((^) "Undeclared identifier " Names.qidToString
                        (valOf (Names.constUndef qid)))
                       ^ " in name preference"))
           | SOME cid ->
               (try Names.installNamePref (cid, namePref)
                with | Error msg -> raise (Names.Error (Paths.wrap (r, msg)))))
      | (fileName, (ModeDec mterms, r)) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          let _ = ReconTerm.checkErrors r in
          let _ =
            List.app
              (function
               | (((a, _) as mdec), r) ->
                   (match ModeTable.modeLookup a with
                    | NONE -> ()
                    | SOME _ ->
                        if Subordinate.frozen [a]
                        then
                          raise
                            (ModeTable.Error
                               (Paths.wrap
                                  (r,
                                    ((^) "Cannot redeclare mode for frozen constant "
                                       Names.qidToString (Names.constQid a)))))
                        else ())) mdecs in
          let _ =
            List.app
              (function
               | (((a, _) as mdec), r) ->
                   (try
                      match IntSyn.conDecStatus (IntSyn.sgnLookup a) with
                      | IntSyn.Normal -> ModeTable.installMode mdec
                      | _ ->
                          raise
                            (ModeTable.Error
                               "Cannot declare modes for foreign constants")
                    with
                    | Error msg ->
                        raise (ModeTable.Error (Paths.wrap (r, msg))))) mdecs in
          let _ = List.app (function | mdec -> ModeDec.checkPure mdec) mdecs in
          let _ =
            List.app
              (function
               | (mdec, r) ->
                   (try ModeCheck.checkMode mdec
                    with | Error msg -> raise (ModeCheck.Error msg))) mdecs in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((^) "%mode " ModePrint.modesToString
                    (List.map (function | (mdec, r) -> mdec) mdecs))
                   ^ ".\n")
            else () in
          ()
      | (fileName, (UniqueDec mterms, r)) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          let _ = ReconTerm.checkErrors r in
          let _ =
            List.app
              (function
               | (((a, _) as mdec), r) ->
                   (try
                      match IntSyn.conDecStatus (IntSyn.sgnLookup a) with
                      | IntSyn.Normal -> UniqueTable.installMode mdec
                      | _ ->
                          raise
                            (UniqueTable.Error
                               "Cannot declare modes for foreign constants")
                    with
                    | Error msg -> raise (Unique.Error (Paths.wrap (r, msg)))))
              mdecs in
          let _ =
            List.app
              (function
               | (mdec, r) ->
                   (try Timers.time Timers.coverage Unique.checkUnique mdec
                    with
                    | Error msg -> raise (Unique.Error (Paths.wrap (r, msg)))))
              mdecs in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((^) "%unique " ModePrint.modesToString
                    (List.map (function | (mdec, r) -> mdec) mdecs))
                   ^ ".\n")
            else () in
          ()
      | (fileName, (CoversDec mterms, r)) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          let _ = ReconTerm.checkErrors r in
          let _ = List.app (function | mdec -> ModeDec.checkPure mdec) mdecs in
          let _ =
            List.app
              (function
               | (mdec, r) ->
                   (try Timers.time Timers.coverage Cover.checkCovers mdec
                    with
                    | Error msg -> raise (Cover.Error (Paths.wrap (r, msg)))))
              mdecs in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((^) "%covers " ModePrint.modesToString
                    (List.map (function | (mdec, r) -> mdec) mdecs))
                   ^ ".\n")
            else () in
          ()
      | (fileName, (TotalDec lterm, r)) ->
          let (T, ((r, rs) as rrs)) = ReconThm.tdeclTotDecl lterm in
          let La = Thm.installTotal (T, rrs) in
          let _ = map Total.install La in
          let _ =
            try map Total.checkFam La
            with | Error msg -> raise (Total.Error msg)
            | Error msg -> raise (Cover.Error (Paths.wrap (r, msg)))
            | Error msg -> raise (Reduces.Error msg)
            | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) in
          let _ =
            if (!Global.chatter) >= 3
            then msg (((^) "%total " ThmPrint.tDeclToString T) ^ ".\n")
            else () in
          ()
      | (fileName, (TerminatesDec lterm, _)) ->
          let (T, ((r, rs) as rrs)) = ReconThm.tdeclTotDecl lterm in
          let TDecl (_, Callpats callpats) = T in
          let La = Thm.installTerminates (T, rrs) in
          let _ = map (Timers.time Timers.terminate Reduces.checkFam) La in
          let _ =
            if !Global.autoFreeze then (Subordinate.freeze La; ()) else () in
          let _ =
            if (!Global.chatter) >= 3
            then msg (((^) "%terminates " ThmPrint.tDeclToString T) ^ ".\n")
            else () in
          ()
      | (fileName, (ReducesDec lterm, _)) ->
          let (R, ((r, rs) as rrs)) = ReconThm.rdeclTorDecl lterm in
          let RDecl (_, Callpats callpats) = R in
          let La = Thm.installReduces (R, rrs) in
          let _ =
            map (Timers.time Timers.terminate Reduces.checkFamReduction) La in
          let _ =
            if !Global.autoFreeze then (Subordinate.freeze La; ()) else () in
          let _ =
            if (!Global.chatter) >= 3
            then msg (((^) "%reduces " ThmPrint.rDeclToString R) ^ ".\n")
            else () in
          ()
      | (fileName, (TabledDec tdecl, _)) ->
          let (T, r) = ReconThm.tableddeclTotabledDecl tdecl in
          let La = Thm.installTabled T in
          let _ =
            if (!Global.chatter) >= 3
            then msg (((^) "%tabled " ThmPrint.tabledDeclToString T) ^ ".\n")
            else () in
          ()
      | (fileName, (KeepTableDec tdecl, _)) ->
          let (T, r) = ReconThm.keepTabledeclToktDecl tdecl in
          let La = Thm.installKeepTable T in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((^) "%keeptabled " ThmPrint.keepTableDeclToString T) ^
                   ".\n")
            else () in
          ()
      | (fileName, (TheoremDec tdec, r)) ->
          let Tdec = ReconThm.theoremDecToTheoremDec tdec in
          let _ = ReconTerm.checkErrors r in
          let (GBs, (ConDec (name, _, k, _, V, L) as E)) =
            ThmSyn.theoremDecToConDec (Tdec, r) in
          let _ = FunSyn.labelReset () in
          let _ =
            List.foldr
              (function
               | ((G1, G2), k) ->
                   FunSyn.labelAdd
                     (FunSyn.LabelDec
                        ((Int.toString k), (FunSyn.ctxToList G1),
                          (FunSyn.ctxToList G2)))) 0 GBs in
          let cid = installConDec IntSyn.Ordinary (E, (fileName, NONE), r) in
          let MS = ThmSyn.theoremDecToModeSpine (Tdec, r) in
          let _ = ModeTable.installMode (cid, MS) in
          let _ =
            if (!Global.chatter) >= 3
            then msg (((^) "%theorem " Print.conDecToString E) ^ "\n")
            else () in
          ()
      | (fileName, (ProveDec lterm, r)) ->
          let (PDecl (depth, T), rrs) = ReconThm.proveToProve lterm in
          let La = Thm.installTerminates (T, rrs) in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((("%prove " ^ (Int.toString depth)) ^ " ") ^
                    (ThmPrint.tDeclToString T))
                   ^ ".\n")
            else () in
          let _ = Prover.init (depth, La) in
          let _ =
            if (!Global.chatter) >= 3
            then
              map
                (function
                 | a ->
                     msg
                       (("%mode " ^
                           (ModePrint.modeToString
                              (a, (valOf (ModeTable.modeLookup a)))))
                          ^ ".\n")) La
            else [()] in
          let _ =
            try Prover.auto ()
            with
            | Error msg ->
                raise (Prover.Error (Paths.wrap ((joinregion rrs), msg))) in
          let _ = if (!Global.chatter) >= 3 then msg "%QED\n" else () in
          (Prover.install
             (function
              | E -> installConDec IntSyn.Ordinary (E, (fileName, NONE), r));
           Skolem.install La)
      | (fileName, (EstablishDec lterm, r)) ->
          let (PDecl (depth, T), rrs) = ReconThm.establishToEstablish lterm in
          let La = Thm.installTerminates (T, rrs) in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((("%prove " ^ (Int.toString depth)) ^ " ") ^
                    (ThmPrint.tDeclToString T))
                   ^ ".\n")
            else () in
          let _ = Prover.init (depth, La) in
          let _ =
            if (!Global.chatter) >= 3
            then
              map
                (function
                 | a ->
                     msg
                       (("%mode " ^
                           (ModePrint.modeToString
                              (a, (valOf (ModeTable.modeLookup a)))))
                          ^ ".\n")) La
            else [()] in
          let _ =
            try Prover.auto ()
            with
            | Error msg ->
                raise (Prover.Error (Paths.wrap ((joinregion rrs), msg))) in
          Prover.install
            (function
             | E -> installConDec IntSyn.Ordinary (E, (fileName, NONE), r))
      | (fileName, (AssertDec aterm, _)) ->
          let _ =
            if not (!Global.unsafe)
            then
              raise (ThmSyn.Error "%assert not safe: Toggle `unsafe' flag")
            else () in
          let ((Callpats (L) as cp), rrs) = ReconThm.assertToAssert aterm in
          let La = map (function | (c, P) -> c) L in
          let _ =
            if (!Global.chatter) >= 3
            then msg (("%assert " ^ (ThmPrint.callpatsToString cp)) ^ ".\n")
            else () in
          let _ =
            if (!Global.chatter) >= 3
            then
              map
                (function
                 | a ->
                     msg
                       (("%mode " ^
                           (ModePrint.modeToString
                              (a, (valOf (ModeTable.modeLookup a)))))
                          ^ ".\n")) La
            else [()] in
          Skolem.install La
      | (fileName, (WorldDec wdecl, _)) ->
          let (WDecl (qids, (Callpats cpa as cp)), rs) =
            ReconThm.wdeclTowDecl wdecl in
          let _ =
            ListPair.app
              (function
               | ((a, _), r) ->
                   if Subordinate.frozen [a]
                   then
                     raise
                       (WorldSyn.Error
                          (Paths.wrapLoc
                             ((Paths.Loc (fileName, r)),
                               ((^) "Cannot declare worlds for frozen family "
                                  Names.qidToString (Names.constQid a)))))
                   else ()) (cpa, rs) in
          let flatten arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (nil, F) -> F
            | (cid::L, F) ->
                (match IntSyn.sgnLookup cid with
                 | BlockDec _ -> flatten L (cid :: F)
                 | BlockDef (_, _, L') -> flatten (L @ L') F) in
          let W =
            Tomega.Worlds
              (flatten
                 (List.map
                    (function
                     | qid ->
                         (match Names.constLookup qid with
                          | NONE ->
                              raise
                                (Names.Error
                                   (((^) "Undeclared label "
                                       Names.qidToString
                                       (valOf (Names.constUndef qid)))
                                      ^ "."))
                          | SOME cid -> cid)) qids) nil) in
          let _ =
            try List.app (function | (a, _) -> WorldSyn.install (a, W)) cpa
            with
            | Error msg ->
                raise
                  (WorldSyn.Error
                     (Paths.wrapLoc
                        ((Paths.Loc (fileName, (joinregions rs))), msg))) in
          let _ =
            if !Global.autoFreeze
            then
              (Subordinate.freeze (List.map (function | (a, _) -> a) cpa); ())
            else () in
          let _ =
            if (!Global.chatter) >= 3
            then
              msg
                (((^) (((^) "%worlds " Print.worldsToString W) ^ " ")
                    ThmPrint.callpatsToString cp)
                   ^ ".\n")
            else () in
          (Timers.time Timers.worlds
             (map (function | (a, _) -> WorldSyn.worldcheck W a)) cpa;
           ())
      | (fileName, ((SigDef _, _) as declr)) ->
          install1WithSig (fileName, NONE, declr)
      | (fileName, ((StructDec _, _) as declr)) ->
          install1WithSig (fileName, NONE, declr)
      | (fileName, ((Include _, _) as declr)) ->
          install1WithSig (fileName, NONE, declr)
      | (fileName, ((Open _, _) as declr)) ->
          install1WithSig (fileName, NONE, declr)
      | (fileName, (Use name, r)) ->
          (match !context with
           | NONE -> CSManager.useSolver name
           | _ ->
               raise
                 (ModSyn.Error
                    (Paths.wrap
                       (r, "%use declaration needs to be at top level"))))
    let rec install1WithSig =
      function
      | (fileName, moduleOpt, (SigDef sigdef, r)) ->
          let (idOpt, module__, wherecls) =
            ReconModule.sigdefToSigdef (sigdef, moduleOpt) in
          let module' =
            foldl
              (function
               | (inst, module__) -> ReconModule.moduleWhere (module__, inst))
              module__ wherecls in
          let name =
            try
              match idOpt with
              | SOME id -> (ModSyn.installSigDef (id, module'); id)
              | NONE -> "_"
            with | Error msg -> raise (ModSyn.Error (Paths.wrap (r, msg))) in
          let _ =
            if (!Global.chatter) >= 3
            then msg (("%sig " ^ name) ^ " = { ... }.\n")
            else () in
          ()
      | (fileName, moduleOpt, (StructDec structdec, r)) ->
          (match ReconModule.structdecToStructDec (structdec, moduleOpt) with
           | StructDec (idOpt, module__, wherecls) ->
               let module' =
                 foldl
                   (function
                    | (inst, module__) ->
                        ReconModule.moduleWhere (module__, inst)) module__
                   wherecls in
               let name =
                 match idOpt with
                 | SOME id ->
                     (installStrDec
                        ((IntSyn.StrDec (id, NONE)), module', r, false__);
                      id)
                 | NONE -> "_" in
               let _ =
                 if (!Global.chatter) = 3
                 then msg (("%struct " ^ name) ^ " : { ... }.\n")
                 else () in
               ()
           | StructDef (idOpt, mid) ->
               let ns = Names.getComponents mid in
               let module__ = ModSyn.abstractModule (ns, (SOME mid)) in
               let name =
                 match idOpt with
                 | SOME id ->
                     (installStrDec
                        ((IntSyn.StrDec (id, NONE)), module__, r, true__);
                      id)
                 | NONE -> "_" in
               let _ =
                 if (!Global.chatter) = 3
                 then
                   msg
                     (((^) (("%struct " ^ name) ^ " = ") Names.qidToString
                         (Names.structQid mid))
                        ^ ".\n")
                 else () in
               ())
      | (fileName, moduleOpt, (Include sigexp, r)) ->
          let (module__, wherecls) =
            ReconModule.sigexpToSigexp (sigexp, moduleOpt) in
          let module' =
            foldl
              (function
               | (inst, module__) -> ReconModule.moduleWhere (module__, inst))
              module__ wherecls in
          let _ = includeSig (module', r, false__) in
          let _ =
            if (!Global.chatter) = 3 then msg "%include { ... }.\n" else () in
          ()
      | (fileName, NONE, (Open strexp, r)) ->
          let mid = ReconModule.strexpToStrexp strexp in
          let ns = Names.getComponents mid in
          let module__ = ModSyn.abstractModule (ns, (SOME mid)) in
          let _ = includeSig (module__, r, true__) in
          let _ =
            if (!Global.chatter) = 3
            then
              msg
                (((^) "%open " Names.qidToString (Names.structQid mid)) ^
                   ".\n")
            else () in
          ()
    let rec installSubsig (fileName, s) =
      let namespace = Names.newNamespace () in
      let (mark, markStruct) = IntSyn.sgnSize () in
      let markSigDef = ModSyn.sigDefSize () in
      let oldContext = !context in
      let _ = (:=) context SOME namespace in
      let _ =
        if (!Global.chatter) >= 4 then msg "\n% begin subsignature\n" else () in
      let install s = install' (Timers.time Timers.parsing S.expose s)
      and install' =
        function
        | Cons ((Parser.BeginSubsig, _), s') ->
            install (installSubsig (fileName, s'))
        | Cons ((Parser.EndSubsig, _), s') -> s'
        | Cons (declr, s') -> (install1 (fileName, declr); install s') in
      let result =
        try
          let s' = install s in
          let module__ = ModSyn.abstractModule (namespace, NONE) in
          let _ =
            if (!Global.chatter) >= 4
            then msg "% end subsignature\n\n"
            else () in
          Value (module__, s')
        with | exn -> Exception exn in
      let _ = context := oldContext in
      let _ = Names.resetFrom (mark, markStruct) in
      let _ = Index.resetFrom mark in
      let _ = IndexSkolem.resetFrom mark in
      let _ = ModSyn.resetFrom markSigDef in
      match result with
      | Value (module__, s') ->
          let Cons (declr, s'') = Timers.time Timers.parsing S.expose s' in
          (install1WithSig (fileName, (SOME module__), declr); s'')
      | Exception exn -> raise exn
    let rec loadFile fileName =
      handleExceptions 0 fileName (withOpenIn fileName)
        (function
         | instream ->
             let _ = ReconTerm.resetErrors fileName in
             let install s = install' (Timers.time Timers.parsing S.expose s)
             and install' =
               function
               | S.Empty -> OK
               | Cons ((Parser.BeginSubsig, _), s') ->
                   install (installSubsig (fileName, s'))
               | Cons (decl, s') -> (install1 (fileName, decl); install s') in
             install (Parser.parseStream instream))
    let rec loadString str =
      handleExceptions 0 "string"
        (function
         | () ->
             let _ = ReconTerm.resetErrors "string" in
             let install s = install' (Timers.time Timers.parsing S.expose s)
             and install' =
               function
               | S.Empty -> OK
               | Cons ((Parser.BeginSubsig, _), s') ->
                   (installSubsig ("string", s'); install s')
               | Cons (decl, s') -> (install1 ("string", decl); install s') in
             install (Parser.parseStream (TextIO.openString str))) ()
    let rec sLoop () = if Solve.qLoop () then OK else ABORT
    let rec topLoop () =
      match handleExceptions 0 "stdIn" sLoop () with
      | ABORT -> topLoop ()
      | OK -> ()
    let rec top () = topLoop ()
    let rec installCSMDec (conDec, optFixity, mdecL) =
      let _ = ModeCheck.checkD (conDec, "%use", NONE) in
      let cid =
        installConDec IntSyn.FromCS (conDec, ("", NONE), (Paths.Reg (0, 0))) in
      let _ =
        if (!Global.chatter) >= 3
        then msg ((Print.conDecToString conDec) ^ "\n")
        else () in
      let _ =
        match optFixity with
        | SOME fixity ->
            (Names.installFixity (cid, fixity);
             if (!Global.chatter) >= 3
             then
               msg
                 (((^) (((^) (if (!Global.chatter) >= 4 then "%" else "")
                           Names.Fixity.toString fixity)
                          ^ " ")
                     Names.qidToString (Names.constQid cid))
                    ^ ".\n")
             else ())
        | NONE -> () in
      let _ =
        List.app (function | mdec -> ModeTable.installMmode (cid, mdec))
          mdecL in
      cid
    let _ = CSManager.setInstallFN installCSMDec
    let rec reset () =
      IntSyn.sgnReset ();
      Names.reset ();
      Origins.reset ();
      ModeTable.reset ();
      UniqueTable.reset ();
      Index.reset ();
      IndexSkolem.reset ();
      Subordinate.reset ();
      Total.reset ();
      WorldSyn.reset ();
      Reduces.reset ();
      TabledSyn.reset ();
      FunSyn.labelReset ();
      CompSyn.sProgReset ();
      CompSyn.detTableReset ();
      Compile.sProgReset ();
      ModSyn.reset ();
      CSManager.resetSolvers ();
      context := NONE
    let rec readDecl () =
      handleExceptions 0 "stdIn"
        (function
         | () ->
             let _ = ReconTerm.resetErrors "stdIn" in
             let install s = install' (Timers.time Timers.parsing S.expose s)
             and install' =
               function
               | S.Empty -> ABORT
               | Cons ((Parser.BeginSubsig, _), s') ->
                   (installSubsig ("stdIn", s'); OK)
               | Cons (decl, s') -> (install1 ("stdIn", decl); OK) in
             install (Parser.parseStream TextIO.stdIn)) ()
    let rec decl id =
      match Names.stringToQid id with
      | NONE ->
          (msg (id ^ " is not a well-formed qualified identifier\n"); ABORT)
      | SOME qid ->
          (match Names.constLookup qid with
           | NONE ->
               (msg
                  ((Names.qidToString (valOf (Names.constUndef qid))) ^
                     " has not been declared\n");
                ABORT)
           | SOME cid -> decl' cid)
    let rec decl' cid =
      let conDec = IntSyn.sgnLookup cid in
      msg ((Print.conDecToString conDec) ^ "\n"); OK
    module ModFile :
      sig
        type nonrec mfile
        val create : string -> mfile
        val fileName : mfile -> string
        val editName : (string -> string) -> mfile -> mfile
        val modified : mfile -> bool
        val makeModified : mfile -> unit
        val makeUnmodified : mfile -> unit
      end =
      struct
        type nonrec mfile = (string * Time.time option ref)
        let rec create file = (file, (ref NONE))
        let rec fileName (file, _) = file
        let rec editName edit (file, mtime) = ((edit file), mtime)
        let rec modified =
          function
          | (_, ref (NONE)) -> true__
          | (file, ref (SOME time)) ->
              (match Time.compare (time, (OS.FileSys.modTime file)) with
               | EQUAL -> false__
               | _ -> true__)
        let rec makeModified (_, mtime) = mtime := NONE
        let rec makeUnmodified (file, mtime) =
          (:=) mtime SOME (OS.FileSys.modTime file)
      end 
    module Config =
      struct
        type nonrec config = (string * ModFile.mfile list)
        let suffix = ref "cfg"
        let rec mkRel (prefix, path) =
          OS.Path.mkCanonical
            (if OS.Path.isAbsolute path
             then path
             else OS.Path.concat (prefix, path))
        let rec read config =
          let appendUniq (l1, l2) =
            let appendUniq' =
              function
              | x::l2 ->
                  if List.exists (function | y -> x = y) l1
                  then appendUniq' l2
                  else (::) x appendUniq' l2
              | nil -> List.rev l1 in
            List.rev (appendUniq' (List.rev l2)) in
          let isConfig item =
            let suffix_size = (String.size (!suffix)) + 1 in
            let suffix_start = (String.size item) - suffix_size in
            (suffix_start >= 0) &&
              ((String.substring (item, suffix_start, suffix_size)) =
                 ((!) ((^) ".") suffix)) in
          let fromUnixPath path =
            let vol = OS.Path.getVolume config in
            let isAbs = String.isPrefix "/" path in
            let arcs = String.tokens (function | c -> c = '/') path in
            OS.Path.toString { isAbs; vol; arcs } in
          let read' (sources, configs) config =
            withOpenIn config
              (function
               | instream ->
                   let { dir = configDir; file = _; file = _ } =
                     OS.Path.splitDirFile config in
                   let parseItem (sources, configs) item =
                     if isConfig item
                     then
                       (if
                          List.exists (function | config' -> item = config')
                            configs
                        then (sources, configs)
                        else read' (sources, (item :: configs)) item)
                     else
                       if
                         List.exists (function | source' -> item = source')
                           sources
                       then (sources, configs)
                       else ((sources @ [item]), configs) in
                   let parseLine (sources, configs) line =
                     if Substring.isEmpty line
                     then (sources, configs)
                     else
                       (let line' = Substring.dropl Char.isSpace line in
                        parseLine' (sources, configs) line')
                   and parseLine' (sources, configs) line =
                     if
                       (Substring.isEmpty line) ||
                         ((Substring.sub (line, 0)) = '%')
                     then parseStream (sources, configs)
                     else
                       (let line' =
                          Substring.string
                            (Substring.takel (not o Char.isSpace) line) in
                        let item = mkRel (configDir, (fromUnixPath line')) in
                        parseStream (parseItem (sources, configs) item))
                   and parseStream (sources, configs) =
                     let line =
                       Compat.Substring.full (Compat.inputLine97 instream) in
                     parseLine (sources, configs) line in
                   parseStream (sources, configs)) in
          let pwdir = OS.FileSys.getDir () in
          (pwdir,
            (List.map ModFile.create
               ((fun r -> r.1) (read' (nil, [config]) config))))
        let rec readWithout (s, c) =
          let (d, fs) = read s in
          let (d', fs') = c in
          let fns' =
            map (function | m -> mkRel (d', (ModFile.fileName m))) fs' in
          let redundant m =
            let n = mkRel (d, (ModFile.fileName m)) in
            List.exists (function | n' -> n = n') fns' in
          (d, (List.filter (not o redundant) fs))
        let rec loadAbort =
          function
          | (mfile, OK) ->
              let status = loadFile (ModFile.fileName mfile) in
              ((match status with
                | OK -> ModFile.makeUnmodified mfile
                | _ -> ());
               status)
          | (_, ABORT) -> ABORT
        let rec load ((_, sources) as config) =
          reset (); List.app ModFile.makeModified sources; append config
        let rec append (pwdir, sources) =
          let fromFirstModified =
            function
            | nil -> nil
            | x::xs as sources ->
                if ModFile.modified x then sources else fromFirstModified xs in
          let mkAbsolute p =
            Compat.OS.Path.mkAbsolute { path = p; relativeTo = pwdir } in
          let sources' =
            if (=) pwdir OS.FileSys.getDir ()
            then sources
            else List.map (ModFile.editName mkAbsolute) sources in
          let sources'' = fromFirstModified sources' in
          List.foldl loadAbort OK sources''
        let rec define sources =
          ((OS.FileSys.getDir ()), (List.map ModFile.create sources))
      end
    let rec make fileName = Config.load (Config.read fileName)
    module Print :
      sig
        val implicit : bool ref
        val printInfix : bool ref
        val depth : int option ref
        val length : int option ref
        val indent : int ref
        val width : int ref
        val noShadow : bool ref
        val sgn : unit -> unit
        val prog : unit -> unit
        val subord : unit -> unit
        val def : unit -> unit
        val domains : unit -> unit
        module TeX : sig val sgn : unit -> unit val prog : unit -> unit end
      end =
      struct
        let ((implicit)(*! structure IntSyn = IntSyn' !*)
          (* result of a computation *)(* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
          (* withOpenIn fileName (fn instream => body) = x
       opens fileName for input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)
          (* evarInstToString Xs = msg
       formats instantiated EVars as a substitution.
       Abbreviate as empty string if chatter level is < 3.
    *)
          (* expToString (g, U) = msg
       formats expression as a string.
       Abbreviate as empty string if chatter level is < 3.
    *)
          (* status ::= OK | ABORT  is the return status of various operations *)
          (* should move to paths, or into the prover module... but not here! -cs *)
          (* val handleExceptions : int -> string -> ('a -> Status) -> 'a -> Status *)
          (* handleExceptions chlev filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued if chatter level is greater or equal to chlev.
       Unrecognized exceptions are re-raised.
    *)
          (* | Constraints.Error (cnstrL) => abortFileMsg (fileName, constraintsMsg cnstrL) *)
          (* Total includes filename *)(* Reduces includes filename *)
          (* ModeCheck includes filename *)(* - Not supported in polyML ABP - 4/20/03
              * | IO.Io (ioError) => abortIO (fileName, ioError)
              *)
          (* includes filename *)(* includes filename *)
          (* During elaboration of a signature expression, each constant
       that that the user declares is added to this table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)
          (* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)
          (* (Clause, _) should be impossible *)(* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
          (* (Clause, _) should be impossible *)(* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
          (* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
          (* Constant declarations c : V, c : V = U plus variations *)
          (* allocate new cid. *)(* allocate new cid. *)
          (* names are assigned in ReconConDec *)(* val conDec' = nameConDec (conDec) *)
          (* should print here, not in ReconConDec *)
          (* allocate new cid after checking modes! *)
          (* anonymous definition for type-checking *)
          (* Abbreviations %abbrev c = U and %abbrev c : V = U *)
          (* names are assigned in ReconConDec *)(* val conDec' = nameConDec (conDec) *)
          (* should print here, not in ReconConDec *)
          (* allocate new cid after checking modes! *)
          (* anonymous definition for type-checking *)
          (* Clauses %clause c = U or %clause c : V = U or %clause c : V *)
          (* these are like definitions, but entered into the program table *)
          (* val _ = print "%clause " *)(* anonymous definition for type-checking: ignore %clause *)
          (* Solve declarations %solve c : A *)(* should print here, not in ReconQuery *)
          (* allocate new cid after checking modes! *)
          (* allocate cid after strictness has been checked! *)(* %query <expected> <try> A or %query <expected> <try> X : A *)
          (* Solve.query might raise Solve.AbortQuery (msg) *)(* %fquery <expected> <try> A or %fquery <expected> <try> X : A *)
          (* Solve.query might raise Fquery.AbortQuery (msg) *)(* %queryTabled <expected> <try> A or %query <expected> <try> X : A *)
          (* Solve.query might raise Solve.AbortQuery (msg) *)(* %trustme <decl> *)
          (* %subord (<qid> <qid>) ... *)(* %freeze <qid> ... *)
          (* Subordinate.installFrozen cids *)(* %thaw <qid> ... *)
          (* invalidate prior meta-theoretic properteis of signatures *)
          (* exempt only %mode [incremental], %covers [not stored] *)
          (* %deterministic <qid> ... *)(* %compile <qids> *)
          (* -ABP 4/4/03 *)(* MOVED -- ABP 4/4/03 *)
          (* ******************************************* *)
          (* ******************************************* *)
          (* Fixity declaration for operator precedence parsing *)
          (* Name preference declaration for printing *)
          (* Mode declaration *)(* exception comes with location *)
          (* Unique declaration *)(* convert all UniqueTable.Error to Unique.Error *)
          (* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
          (* %unique does not auto-freeze, since family must already be frozen *)
          (* Coverage declaration *)(* MERGE Fri Aug 22 13:43:12 2003 -cs *)
          (* Total declaration *)(* time activities separately in total.fun *)
          (* Mon Dec  2 17:20:18 2002 -fp *)(* coverage checker appears to be safe now *)
          (*
          val _ = if not (!Global.unsafe)
                    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "%total not safe: Toggle `unsafe' flag"))
                  else ()
          *)
          (* ******************************************* *)
          (*  Temporarily disabled -- cs Thu Oct 30 12:46:44 2003
          fun checkFreeOut nil = ()
            | checkFreeOut (a :: La) =
              let
                val SOME ms = ModeTable.modeLookup a
                val _ = ModeCheck.checkFreeOut (a, ms)
              in
                checkFreeOut La
              end
          val _ = checkFreeOut La
          val (lemma, projs, sels) = Converter.installPrg La


           ABP 2/28/03 -- factoring *)
          (*      val result1 = NONE *)(* pre-install for recursive checking *)
          (* include region and file *)(*                     | Cover.Error (msg) => covererror (result1, msg)  disabled -cs Thu Jan 29 16:35:13 2004 *)
          (* includes filename *)(*        val _ = case (result1)
                    of NONE => ()
                     | SOME msg => raise Cover.Error (Paths.wrap (r, "Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] " ^ msg))
*)
          (* %total does not auto-freeze, since the predicate must already be frozen *)
          (* Termination declaration *)(* allow re-declaration since safe? *)
          (* Thu Mar 10 13:45:42 2005 -fp *)(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookup a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare termination order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
          (* -bp *)(* Reduces declaration *)(* allow re-declaration since safe? *)
          (* Thu Mar 10 14:06:13 2005 -fp *)(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare reduction order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
          (*  -bp6/12/99.   *)(* Tabled declaration *)
          (*  -bp6/12/99.   *)(* %keepTable declaration *)
          (* Theorem declaration *)(* Prove declaration *)
          (* La is the list of type constants *)(* mode must be declared!*)
          (* times itself *)(* Establish declaration *)
          (* La is the list of type constants *)(* mode must be declared!*)
          (* times itself *)(* Assert declaration *)
          (* La is the list of type constants *)(* mode must be declared!*)
          (* error location inaccurate here *)(*if !Global.doubleCheck
             then (map (fn (a,_) => Worldify.worldify a) cpa; ())
           else  ()  --cs Sat Aug 27 22:04:29 2005 *)
          (* Signature declaration *)(* FIX: should probably time this -kw *)
          (* anonymous *)(* Structure declaration *)
          (* anonymous *)(* anonymous *)
          (* Include declaration *)(* Open declaration *)
          (* val _ = ModeTable.resetFrom mark *)(* val _ = Total.resetFrom mark *)
          (* val _ = Subordinate.resetFrom mark  ouch! *)
          (* val _ = Reduces.resetFrom mark *)(* Origins, CompSyn, FunSyn harmless? -kw *)
          (* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for now -kw *)
          (* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
          (* Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) *)
          (* now done in installConDec *)(* loadString (str) = status
       reads and processes declarations from str, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
          (* Interactive Query Top Level *)(* "stdIn" as fake fileName *)
          (* top () = () starts interactive query loop *)
          (* put a more reasonable region here? -kw *)
          (* reset () = () clears all global tables, including the signature *)
          (* -fp Wed Mar  9 20:24:45 2005 *)(* -fp *)
          (* -fp *)(* -bp *)(* -bp *)
          (* necessary? -fp; yes - bp*)(*  -bp *)
          (* resetting substitution trees *)(* decl (id) = () prints declaration of constant id *)
          (* val fixity = Names.getFixity (cid) *)(* can't get name preference right now *)
          (* val mode = ModeTable.modeLookup (cid) *)
          (* can't get termination declaration *)(* Support tracking file modification times for smart re-appending. *)
          (* config = ["fileName1",...,"fileName<n>"] *)
          (* Files will be read in the order given! *)
          (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names (which are interpreted
         relative to pwdir) along with their modification times.
         pwdir will be the current working directory
         when a configuration is loaded, which may not be same as the
         directory in which the configuration file is located.

         This representation allows shorter file names in chatter and
         error messages.
      *)
          (* suffix of configuration files: "cfg" by default *)
          (* mkRel transforms a relative path into an absolute one
               by adding the specified prefix. If the path is already
               absolute, no prefix is added to it.
            *)
          (* more efficient recursive version  Sat 08/26/2002 -rv *)
          (* appendUniq (list1, list2) appends list2 to list1, removing all
               elements of list2 which are already in list1.
            *)
          (* isConfig (item) is true iff item has the suffix of a
               configuration file.
            *)
          (* fromUnixPath path transforms path (assumed to be in Unix form)
               to the local OS conventions.
            *)
          (* we have already read this one *)(* we have already collected this one *)
          (* end of file *)(* empty line *)
          (* comment *)(*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *)
          (* Read a config file s but omit everything that is already in config c
         XXX: naive and inefficient implementation *)
          (* load (config) = Status
         resets the global signature and then reads the files in config
         in order, stopping at the first error.
      *)
          (* append (config) = Status
         reads the files in config in order, beginning at the first
         modified file, stopping at the first error.
      *)
          (* allow shorter messages if safe *)(* structure Config *)
          (* make (configFile)
       read and then load configuration from configFile
    *)
          (* re-exporting environment parameters and utilities defined elsewhere *)
          (* false, print implicit args *)(* false, print fully explicit form infix when possible *)
          (* NONE, limit print depth *)(* NONE, limit argument length *)
          (* 3, indentation of subterms *)(* 80, line width *)
          (* if true, don't print shadowed constants as "%const%" *)
          (* print signature *)(* print signature as program *)
          (* print subordination relation *)(* print information about definitions *)
          (* print available constraint domains *)(* print in TeX format *)
          (* print signature *)(* print signature as program *))
          = Print.implicit
        let printInfix = Print.printInfix
        let depth = Print.printDepth
        let length = Print.printLength
        let indent = Print.Formatter.Indent
        let width = Print.Formatter.Pagewidth
        let noShadow = Print.noShadow
        let rec sgn () = Print.printSgn ()
        let rec prog () = ClausePrint.printSgn ()
        let rec subord () = Subordinate.show ()
        let rec def () = Subordinate.showDef ()
        let rec domains () = msg CSInstaller.version
        module TeX =
          struct
            let rec sgn () = printSgnTeX ()
            let rec prog () = printProgTeX ()
          end
      end 
    module Trace :
      sig
        type 'a __Spec =
          | None 
          | Some of 'a list 
          | All 
        val trace : string __Spec -> unit
        val break : string __Spec -> unit
        val detail : int ref
        val show : unit -> unit
        val reset : unit -> unit
      end =
      ((Trace)(* trace specification *)(* no tracing *)
      (* list of clauses and families *)(* trace all clauses and families *)
      (* clauses and families *)(* clauses and families *)
      (* 0 = none, 1 = default, 2 = unify *)(* show trace, break, and detail *)
      (* reset trace, break, and detail *)) 
    module Timers :
      sig
        val show : unit -> unit
        val reset : unit -> unit
        val check : unit -> unit
      end =
      ((Timers)(* show and reset timers *)(* reset timers *)
      (* display, but not no reset *)) 
    module OS :
      sig
        val chDir : string -> unit
        val getDir : unit -> string
        val exit : unit -> unit
      end =
      struct
        let ((chDir)(* change working directory *)(* get working directory *)
          (* exit Twelf and ML *)) = OS.FileSys.chDir
        let getDir = OS.FileSys.getDir
        let rec exit () = OS.Process.exit OS.Process.success
      end 
    module Compile :
      sig type __Opt = CompSyn.__Opt val optimize : __Opt ref end =
      struct type __Opt = CompSyn.__Opt
             let optimize = CompSyn.optimize end 
    module Recon :
      sig
        type __TraceMode = ReconTerm.__TraceMode
        val trace : bool ref
        val traceMode : __TraceMode ref
      end =
      struct
        type __TraceMode = ReconTerm.__TraceMode
        let trace = ReconTerm.trace
        let traceMode = ReconTerm.traceMode
      end 
    module Recon :
      sig
        type __TraceMode = ReconTerm.__TraceMode
        val trace : bool ref
        val traceMode : __TraceMode ref
      end =
      struct
        type __TraceMode = ReconTerm.__TraceMode
        let trace = ReconTerm.trace
        let traceMode = ReconTerm.traceMode
      end 
    module Prover :
      sig
        type __Strategy = MetaGlobal.__Strategy
        val strategy : __Strategy ref
        val maxSplit : int ref
        val maxRecurse : int ref
      end =
      struct
        type __Strategy = MetaGlobal.__Strategy(* 10, bound on recursion *)
        (* 2, bound on splitting  *)(* FRS, strategy used for %prove *)
        (* FRS or RFS *)(* F=Filling, R=Recursion, S=Splitting *)
        let ((strategy)(* FRS or RFS *)) =
          MetaGlobal.strategy
        let maxSplit = MetaGlobal.maxSplit
        let maxRecurse = MetaGlobal.maxRecurse
      end 
    let (chatter : int ref) = Global.chatter
    let (doubleCheck : bool ref) = Global.doubleCheck
    let (unsafe : bool ref) = Global.unsafe
    let (autoFreeze : bool ref) = Global.autoFreeze
    let (timeLimit : Time.time option ref) = Global.timeLimit
    type __Status = __Status
    let reset = reset
    let loadFile = loadFile
    let loadString = loadString
    let readDecl = readDecl
    let decl = decl
    let top = top
    module Config :
      sig
        type nonrec config
        val suffix : string ref
        val read : string -> config
        val readWithout : (string * config) -> config
        val load : config -> __Status
        val append : config -> __Status
        val define : string list -> config
      end =
      ((Config)(* configuration *)(* suffix of configuration files *)
      (* read configuration from config file *)(* read config file, minus contents of another *)
      (* reset and load configuration *)(* load configuration (w/o reset) *)
      (* explicitly define configuration *)) 
    let make = make
    let version = Version.version_string
    module Table :
      sig
        type __Strategy = TableParam.__Strategy
        val strategy : __Strategy ref
        val strengthen : bool ref
        val resetGlobalTable : unit -> unit
        val top : unit -> unit
      end =
      struct
        type __Strategy = TableParam.__Strategy
        let strategy = TableParam.strategy
        let strengthen = TableParam.strengthen
        let resetGlobalTable = TableParam.resetGlobalTable
        let rec top
          ((())(* top () = () starts interactive query loop *))
          =
          let sLoopT () = if Solve.qLoopT () then OK else ABORT in
          let topLoopT () =
            match handleExceptions 0 "stdIn" sLoopT () with
            | ABORT ->
                topLoopT ((())
                  (* "stdIn" as fake fileName *))
            | OK -> () in
          topLoopT ()
      end 
  end ;;
