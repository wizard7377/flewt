module type TWELF  =
  sig
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
    end
    module Trace :
    sig
      type 'a spec_ =
        | None 
        | Some of 'a list 
        | All 
      val trace : string spec_ -> unit
      val break : string spec_ -> unit
      val detail : int ref
      val show : unit -> unit
      val reset : unit -> unit
    end
    module Table :
    sig
      type strategy_ =
        | Variant 
        | Subsumption 
      val strategy : strategy_ ref
      val strengthen : bool ref
      val resetGlobalTable : unit -> unit
      val top : unit -> unit
    end
    module Timers :
    sig
      val show : unit -> unit
      val reset : unit -> unit
      val check : unit -> unit
    end
    module OS :
    sig
      val chDir : string -> unit
      val getDir : unit -> string
      val exit : unit -> unit
    end
    module Compile :
    sig type opt_ =
          | No 
          | LinearHeads 
          | Indexing  val optimize : opt_ ref end
    module Recon :
    sig
      type traceMode_ =
        | Progressive 
        | Omniscient 
      val trace : bool ref
      val traceMode : traceMode_ ref
    end
    module Prover :
    sig
      type strategy_ =
        | RFS 
        | FRS 
      val strategy : strategy_ ref
      val maxSplit : int ref
      val maxRecurse : int ref
    end
    val chatter : int ref
    val doubleCheck : bool ref
    val unsafe : bool ref
    val autoFreeze : bool ref
    val timeLimit : Time.time option ref
    type status_ =
      | OK 
      | ABORT 
    val reset : unit -> unit
    val loadFile : string -> status_
    val loadString : string -> status_
    val readDecl : unit -> status_
    val decl : string -> status_
    val top : unit -> unit
    module Config :
    sig
      type nonrec config
      val suffix : string ref
      val read : string -> config
      val readWithout : (string * config) -> config
      val load : config -> status_
      val append : config -> status_
      val define : string list -> config
    end
    val make : string -> status_
    val version : string
  end


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
                     module Msg : MSG
                   end) : TWELF =
  struct
    module S = Parser.Stream
    let rec msg s = Msg.message s
    let rec chmsg n s = Global.chMessage n s msg
    let rec fileOpenMsg fileName =
      begin match !Global.chatter with
      | 0 -> ()
      | 1 -> msg (("[Loading file " ^ fileName) ^ " ...")
      | _ -> msg (("[Opening file " ^ fileName) ^ "]\n") end
    let rec fileCloseMsg fileName =
      begin match !Global.chatter with
      | 0 -> ()
      | 1 -> msg "]\n"
      | _ -> msg (("[Closing file " ^ fileName) ^ "]\n") end
  type 'a result_ =
    | Value of 'a 
    | Exception of exn 
  let rec withOpenIn fileName scope =
    let instream = TextIO.openIn fileName in
    let _ = fileOpenMsg fileName in
    let result =
      begin try Value (scope instream) with | exn -> Exception exn end in
    let _ = fileCloseMsg fileName in
    let _ = TextIO.closeIn instream in
    begin match result with | Value x -> x | Exception exn -> raise exn end
let rec evarInstToString (xs_) =
  if !Global.chatter >= 3 then begin Print.evarInstToString xs_ end
  else begin "" end
let rec expToString (GU) =
  if !Global.chatter >= 3 then begin Print.expToString GU end
  else begin "" end
let rec printProgTeX () =
  begin msg "\\begin{bigcode}\n";
  ClausePrintTeX.printSgn ();
  msg "\\end{bigcode}\n" end
let rec printSgnTeX () =
  begin msg "\\begin{bigcode}\n";
  PrintTeX.printSgn ();
  msg "\\end{bigcode}\n" end
type status_ =
  | OK 
  | ABORT 
let rec abort chlev msg = begin chmsg chlev (begin function | () -> msg end);
  ABORT end
let rec abortFileMsg chlev (fileName, msg) =
  abort chlev (((fileName ^ ":") ^ msg) ^ "\n")
let rec abortIO =
  begin function
  | (fileName,
     { cause = SysErr (m, _); function___ = f; name = n; function___ = f;
       name = n; name = n })
      ->
      (begin msg (((("IO Error on file " ^ fileName) ^ ":\n") ^ m) ^ "\n");
       ABORT end)
  | (fileName, { function___ = f }) ->
      (begin msg
               (((("IO Error on file " ^ fileName) ^ " from function ") ^ f)
                  ^ "\n");
       ABORT end) end
let rec joinregion =
  begin function
  | (r, []) -> r
  | (r, r'::rs) -> joinregion ((Paths.join (r, r')), rs) end
let rec joinregions (r::rs) = joinregion (r, rs)
let rec constraintsMsg cnstrL =
  (^) "Typing ambiguous -- unresolved constraints\n" Print.cnstrsToString
    cnstrL
let rec handleExceptions chlev fileName (f : 'a -> status_) (x : 'a) =
  ((begin try f x
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
    | exn -> (begin abort 0 (UnknownExn.unknownExn exn); raise exn end) end)
(* | Constraints.Error (cnstrL) => abortFileMsg (fileName, constraintsMsg cnstrL) *)
(* Total includes filename *)(* Reduces includes filename *)
(* ModeCheck includes filename *)(* - Not supported in polyML ABP - 4/20/03
              * | IO.Io (ioError) => abortIO (fileName, ioError)
              *)
(* includes filename *)(* includes filename *))
let (context : Names.namespace option ref) = ref None
let rec installConst fromCS (cid, fileNameocOpt) =
  let _ = Origins.installOrigin (cid, fileNameocOpt) in
  let _ = Index.install fromCS (IntSyn.Const cid) in
  let _ = IndexSkolem.install fromCS (IntSyn.Const cid) in
  let _ = Timers.time Timers.compiling Compile.install fromCS cid in
  let _ = Timers.time Timers.subordinate Subordinate.install cid in
  let _ = Timers.time Timers.subordinate Subordinate.installDef cid in ()
let rec installConDec fromCS
  (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
  let _ = Timers.time Timers.modes ModeCheck.checkD (conDec, fileName, ocOpt) in
  let cid = IntSyn.sgnAdd conDec in
  let _ =
    begin try
            begin match (fromCS, !context) with
            | (IntSyn.Ordinary, Some namespace) ->
                Names.insertConst (namespace, cid)
            | (IntSyn.Clause, Some namespace) ->
                Names.insertConst (namespace, cid)
            | _ -> () end
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
  let _ = Names.installConstName cid in
  let _ =
    begin try installConst fromCS (cid, fileNameocOpt)
    with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end in
  let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
  let _ = if !Global.style >= 1 then begin StyleCheck.checkConDec cid end
    else begin () end in
  cid
let rec installBlockDec fromCS
  (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
  let cid = IntSyn.sgnAdd conDec in
  let _ =
    begin try
            ((begin match (fromCS, !context) with
              | (IntSyn.Ordinary, Some namespace) ->
                  Names.insertConst (namespace, cid)
              | _ -> () end)
    (* (Clause, _) should be impossible *))
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
let _ = Names.installConstName cid in
let _ =
  begin try Timers.time Timers.subordinate Subordinate.installBlock cid
  with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end in
let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
((cid)
  (* val _ = Origins.installOrigin (cid, fileNameocOpt) *))
let rec installBlockDef fromCS
  (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
  let cid = IntSyn.sgnAdd conDec in
  let _ =
    begin try
            ((begin match (fromCS, !context) with
              | (IntSyn.Ordinary, Some namespace) ->
                  Names.insertConst (namespace, cid)
              | _ -> () end)
    (* (Clause, _) should be impossible *))
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
let _ = Names.installConstName cid in
let _ = Origins.installLinesInfo (fileName, (Paths.getLinesInfo ())) in
((cid)
  (* val _ = Origins.installOrigin (cid, fileNameocOpt) *))
let rec installStrDec (strdec, module_, r, isDef) =
  let rec installAction ((cid, _) as data) =
    begin installConst IntSyn.Ordinary data;
    if !Global.chatter >= 4
    then begin msg ((Print.conDecToString (IntSyn.sgnLookup cid)) ^ "\n") end
    else begin () end end in
let _ =
begin try
        ModSyn.installStruct
          (strdec, module_, !context, installAction, isDef)
with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
()
let rec includeSig (module_, r, isDef) =
  let rec installAction ((cid, _) as data) =
    begin installConst IntSyn.Ordinary data;
    if !Global.chatter >= 4
    then begin msg ((Print.conDecToString (IntSyn.sgnLookup cid)) ^ "\n") end
    else begin () end end in
let _ =
begin try ModSyn.installSig (module_, !context, installAction, isDef)
with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
()
let rec cidToString a = Names.qidToString (Names.constQid a)
let rec invalidate uninstallFun cids msg =
  let uninstalledCids =
    List.filter (begin function | a -> uninstallFun a end) cids in
let _ =
  begin match uninstalledCids with
  | [] -> ()
  | _ ->
      chmsg 4
        (begin function
         | () ->
             (^) (("Invalidated " ^ msg) ^ " properties of families")
               List.foldr
               ((begin function | (a, s) -> ((^) " " cidToString a) ^ s end))
             "\n" uninstalledCids end) end in
()
let rec install1 =
  begin function
  | (fileName, (ConDec condec, r)) ->
      (begin try
               let (optConDec, ocOpt) =
                 ReconConDec.condecToConDec
                   (condec, (Paths.Loc (fileName, r)), false) in
               let rec icd =
                 begin function
                 | Some (BlockDec _ as conDec) ->
                     let cid =
                       installBlockDec IntSyn.Ordinary
                         (conDec, (fileName, ocOpt), r) in
                     ((())(* allocate new cid. *))
                 | Some (BlockDef _ as conDec) ->
                     let cid =
                       installBlockDef IntSyn.Ordinary
                         (conDec, (fileName, ocOpt), r) in
                     ((())(* allocate new cid. *))
                 | Some conDec ->
                     let cid =
                       installConDec IntSyn.Ordinary
                         (conDec, (fileName, ocOpt), r) in
                     ((())
                       (* names are assigned in ReconConDec *)(* val conDec' = nameConDec (conDec) *)
                       (* should print here, not in ReconConDec *)
                       (* allocate new cid after checking modes! *))
                 | None -> () end(* anonymous definition for type-checking *) in
               icd optConDec
      with
      | Error eqns ->
          raise (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))) end)
  | (fileName, (AbbrevDec condec, r)) ->
      (begin try
               let (optConDec, ocOpt) =
                 ReconConDec.condecToConDec
                   (condec, (Paths.Loc (fileName, r)), true) in
               let rec icd =
                 begin function
                 | Some conDec ->
                     let cid =
                       installConDec IntSyn.Ordinary
                         (conDec, (fileName, ocOpt), r) in
                     ((())
                       (* names are assigned in ReconConDec *)(* val conDec' = nameConDec (conDec) *)
                       (* should print here, not in ReconConDec *)
                       (* allocate new cid after checking modes! *))
                 | None -> () end(* anonymous definition for type-checking *) in
               icd optConDec
      with
      | Error eqns ->
          raise (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))) end)
| (fileName, (ClauseDec condec, r)) ->
    (begin try
             let (optConDec, ocOpt) =
               ReconConDec.condecToConDec
                 (condec, (Paths.Loc (fileName, r)), false) in
             let rec icd =
               begin function
               | Some conDec ->
                   let cid =
                     installConDec IntSyn.Clause
                       (conDec, (fileName, ocOpt), r) in
                   ()
               | None -> () end(* anonymous definition for type-checking: ignore %clause *) in
             ((icd optConDec)
               (* val _ = print "%clause " *))
    with
    | Error eqns ->
        raise (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))) end)
| (fileName, (Solve (defines, solve), r)) ->
    (begin try
             let conDecL =
               begin try
                       Solve.solve
                         (defines, solve, (Paths.Loc (fileName, r)))
               with
               | AbortQuery msg ->
                   raise (Solve.AbortQuery (Paths.wrap (r, msg))) end in
           let rec icd (conDec, ocOpt) =
             let cid =
               installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in
             ((())
               (* should print here, not in ReconQuery *)
               (* allocate new cid after checking modes! *)
               (* allocate cid after strictness has been checked! *)) in
           List.app icd conDecL
    with
    | Error eqns ->
        raise (ReconTerm.Error (Paths.wrap (r, (constraintsMsg eqns)))) end)
| (fileName, (Query (expected, try_, query), r)) ->
    (begin try
             Solve.query ((expected, try_, query), (Paths.Loc (fileName, r)))
     with | AbortQuery msg -> raise (Solve.AbortQuery (Paths.wrap (r, msg))) end)
| (fileName, (FQuery query, r)) ->
    (begin try Fquery.run (query, (Paths.Loc (fileName, r)))
     with | AbortQuery msg -> raise (Fquery.AbortQuery (Paths.wrap (r, msg))) end)
| (fileName, (Querytabled (numSol, try_, query), r)) ->
    (begin try
             Solve.querytabled
               ((numSol, try_, query), (Paths.Loc (fileName, r)))
     with | AbortQuery msg -> raise (Solve.AbortQuery (Paths.wrap (r, msg))) end)
| (fileName, (TrustMe (dec, r'), r)) ->
    let _ =
      if not !Global.unsafe
      then begin raise (Thm.Error "%trustme not safe: Toggle `unsafe' flag") end
      else begin () end in
let _ = chmsg 3 (begin function | () -> "[%trustme ...\n" end) in
let _ =
begin match handleExceptions 4 fileName
              (begin function | args -> (begin install1 args; OK end) end)
      (fileName, (dec, r))
with
| OK -> chmsg 3 (begin function | () -> "trustme subject succeeded\n" end)
| ABORT ->
    chmsg 3
      (begin function | () -> "trustme subject failed; continuing\n" end) end in
let _ = chmsg 3 (begin function | () -> "%]\n" end) in ()
| (fileName, (SubordDec qidpairs, r)) ->
    let rec toCid qid =
      begin match Names.constLookup qid with
      | None ->
          raise
            (Names.Error
               (((^) "Undeclared identifier " Names.qidToString
                   (valOf (Names.constUndef qid)))
                  ^ " in subord declaration"))
      | Some cid -> cid end in
  let cidpairs =
    begin try
            List.map
              (begin function | (qid1, qid2) -> ((toCid qid1), (toCid qid2)) end)
            qidpairs
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
let _ =
begin try List.app Subordinate.addSubord cidpairs
with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end in
if !Global.chatter >= 3
then
begin msg
        ((^) "%subord" List.foldr
           (begin function
            | ((a1, a2), s) ->
                (((^) (((^) " (" Names.qidToString (Names.constQid a1)) ^ " ")
                    Names.qidToString (Names.constQid a2))
                   ^ ")")
                  ^ s end) ".\n" cidpairs) end else begin () end
| (fileName, (FreezeDec qids, r)) ->
    let rec toCid qid =
      begin match Names.constLookup qid with
      | None ->
          raise
            (Names.Error
               (((^) "Undeclared identifier " Names.qidToString
                   (valOf (Names.constUndef qid)))
                  ^ " in freeze declaration"))
      | Some cid -> cid end in
  let cids =
    begin try List.map toCid qids
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
  let frozen =
    begin try Subordinate.freeze cids
    with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end in
  (((begin if !Global.chatter >= 3
           then
             begin msg
                     ((^) "%freeze" List.foldr
                        (begin function
                         | (a, s) ->
                             ((^) " " Names.qidToString (Names.constQid a)) ^
                               s end) ".\n" cids) end
    else begin () end;
if !Global.chatter >= 4
then
  begin msg
          ((^) "Frozen:" List.foldr
             (begin function
              | (a, s) -> ((^) " " Names.qidToString (Names.constQid a)) ^ s end)
          "\n" frozen) end else begin () end end))
(* Subordinate.installFrozen cids *))
| (fileName, (ThawDec qids, r)) ->
    let _ =
      if not !Global.unsafe
      then begin raise (ThmSyn.Error "%thaw not safe: Toggle `unsafe' flag") end
      else begin () end in
let rec toCid qid =
begin match Names.constLookup qid with
| None ->
    raise
      (Names.Error
         (((^) "Undeclared identifier " Names.qidToString
             (valOf (Names.constUndef qid)))
            ^ " in thaw declaration"))
| Some cid -> cid end in
let cids =
begin try List.map toCid qids
with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
let thawed =
begin try Subordinate.thaw cids
with | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end in
let _ =
if !Global.chatter >= 3
then
  begin msg
          ((^) "%thaw" List.foldr
             (begin function | (a, s) -> ((^) " " cidToString a) ^ s end)
          ".\n" cids) end
else begin () end in
let _ =
if !Global.chatter >= 4
then
  begin msg
          ((^) "Thawed" List.foldr
             (begin function | (a, s) -> ((^) " " cidToString a) ^ s end)
          "\n" thawed) end
else begin () end in
let _ = invalidate WorldSyn.uninstall thawed "world" in
let _ = invalidate Thm.uninstallTerminates thawed "termination" in
let _ = invalidate Thm.uninstallReduces thawed "reduction" in
let _ = invalidate UniqueTable.uninstallMode thawed "uniqueness" in
let _ = invalidate Total.uninstall thawed "totality" in ((())
(* invalidate prior meta-theoretic properteis of signatures *)(* exempt only %mode [incremental], %covers [not stored] *))
| (fileName, (DeterministicDec qids, r)) ->
    let rec toCid qid =
      begin match Names.constLookup qid with
      | None ->
          raise
            (Names.Error
               (((^) "Undeclared identifier " Names.qidToString
                   (valOf (Names.constUndef qid)))
                  ^ " in deterministic declaration"))
      | Some cid -> cid end in
  let rec insertCid cid = CompSyn.detTableInsert (cid, true) in
  let cids =
    begin try List.map toCid qids
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
  (begin List.map insertCid cids;
   if !Global.chatter >= 3
   then
     begin msg
             ((^) ((if !Global.chatter >= 4 then begin "%" end
                     else begin "" end) ^ "%deterministic")
     List.foldr
     (begin function
      | (a, s) -> ((^) " " Names.qidToString (Names.constQid a)) ^ s end)
   ".\n"
   cids) end else begin () end end)
| (fileName, (Compile qids, r)) ->
    let rec toCid qid =
      begin match Names.constLookup qid with
      | None ->
          raise
            (Names.Error
               (((^) "Undeclared identifier " Names.qidToString
                   (valOf (Names.constUndef qid)))
                  ^ " in compile assertion"))
      | Some cid -> cid end in
  let cids =
    begin try List.map toCid qids
    with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end in
  let rec checkFreeOut =
    begin function
    | [] -> ()
    | a::La ->
        let Some ms = ModeTable.modeLookup a in
        let _ = ModeCheck.checkFreeOut (a, ms) in checkFreeOut La end in
  let _ = checkFreeOut cids in
  let (lemma, projs, sels) = Converter.installPrg cids in
  let p_ = Tomega.lemmaDef lemma in
  let f_ = Converter.convertFor cids in
  let _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (p_, f_)) in
  let rec f cid = IntSyn.conDecName (IntSyn.sgnLookup cid) in
  let _ =
    if !Global.chatter >= 2
    then
      begin msg
              (((^) "\n" TomegaPrint.funToString (((map f cids), projs), p_))
                 ^ "\n") end
    else begin () end in
  let _ =
    if !Global.chatter >= 3
    then
      begin msg
              ((^) ((if !Global.chatter >= 4 then begin "%" end
                      else begin "" end) ^ "%compile")
      List.foldr
      (begin function
       | (a, s) -> ((^) " " Names.qidToString (Names.constQid a)) ^ s end)
    ".\n"
    cids) end else begin () end in
  ((())
    (* MOVED -- ABP 4/4/03 *)(* ******************************************* *)
    (* ******************************************* *))
| (fileName, (FixDec ((qid, r), fixity), _)) ->
    (begin match Names.constLookup qid with
     | None ->
         raise
           (Names.Error
              (((^) "Undeclared identifier " Names.qidToString
                  (valOf (Names.constUndef qid)))
                 ^ " in fixity declaration"))
     | Some cid ->
         (begin try
                  begin Names.installFixity (cid, fixity);
                  if !Global.chatter >= 3
                  then
                    begin msg
                            (((^) (((^) (if !Global.chatter >= 4
                                         then begin "%" end
                                      else begin "" end)
                                Names.Fixity.toString fixity)
                               ^ " ") Names.qidToString (Names.constQid cid))
                    ^ ".\n") end
          else begin () end end
with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end) end)
| (fileName, (NamePref ((qid, r), namePref), _)) ->
    (begin match Names.constLookup qid with
     | None ->
         raise
           (Names.Error
              (((^) "Undeclared identifier " Names.qidToString
                  (valOf (Names.constUndef qid)))
                 ^ " in name preference"))
     | Some cid ->
         (begin try Names.installNamePref (cid, namePref)
          with | Error msg -> raise (Names.Error (Paths.wrap (r, msg))) end) end)
| (fileName, (ModeDec mterms, r)) ->
    let mdecs = List.map ReconMode.modeToMode mterms in
    let _ = ReconTerm.checkErrors r in
    let _ =
      List.app
        (begin function
         | (((a, _) as mdec), r) ->
             (begin match ModeTable.modeLookup a with
              | None -> ()
              | Some _ ->
                  if Subordinate.frozen [a]
                  then
                    begin raise
                            (ModeTable.Error
                               (Paths.wrap
                                  (r,
                                    ((^) "Cannot redeclare mode for frozen constant "
                                       Names.qidToString (Names.constQid a))))) end
                  else begin () end end) end)
      mdecs in
let _ =
List.app
  (begin function
   | (((a, _) as mdec), r) ->
       (begin try
                begin match IntSyn.conDecStatus (IntSyn.sgnLookup a) with
                | IntSyn.Normal -> ModeTable.installMode mdec
                | _ ->
                    raise
                      (ModeTable.Error
                         "Cannot declare modes for foreign constants") end
       with | Error msg -> raise (ModeTable.Error (Paths.wrap (r, msg))) end) end)
mdecs in
let _ = List.app (begin function | mdec -> ModeDec.checkPure mdec end) mdecs in
let _ =
List.app
  (begin function
   | (mdec, r) ->
       (((begin try ModeCheck.checkMode mdec
          with | Error msg -> raise (ModeCheck.Error msg) end))
   (* exception comes with location *)) end)
mdecs in
let _ =
if !Global.chatter >= 3
then
  begin msg
          (((^) "%mode " ModePrint.modesToString
              (List.map (begin function | (mdec, r) -> mdec end) mdecs)) ^
          ".\n") end
else begin () end in ()
| (fileName, (UniqueDec mterms, r)) ->
    let mdecs = List.map ReconMode.modeToMode mterms in
    let _ = ReconTerm.checkErrors r in
    let _ =
      List.app
        (begin function
         | (((a, _) as mdec), r) ->
             (begin try
                      begin match IntSyn.conDecStatus (IntSyn.sgnLookup a)
                            with
                      | IntSyn.Normal -> UniqueTable.installMode mdec
                      | _ ->
                          raise
                            (UniqueTable.Error
                               "Cannot declare modes for foreign constants") end
             with | Error msg -> raise (Unique.Error (Paths.wrap (r, msg))) end) end)
      mdecs in
  let _ =
    List.app
      (begin function
       | (mdec, r) ->
           (begin try Timers.time Timers.coverage Unique.checkUnique mdec
            with | Error msg -> raise (Unique.Error (Paths.wrap (r, msg))) end) end)
    mdecs in
let _ =
if !Global.chatter >= 3
then
  begin msg
          (((^) "%unique " ModePrint.modesToString
              (List.map (begin function | (mdec, r) -> mdec end) mdecs)) ^
          ".\n") end
else begin () end in ((())
(* convert all UniqueTable.Error to Unique.Error *)(* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
(* %unique does not auto-freeze, since family must already be frozen *))
| (fileName, (CoversDec mterms, r)) ->
    let mdecs = List.map ReconMode.modeToMode mterms in
    let _ = ReconTerm.checkErrors r in
    let _ = List.app (begin function | mdec -> ModeDec.checkPure mdec end)
      mdecs in
    let _ =
      List.app
        (begin function
         | (mdec, r) ->
             (begin try Timers.time Timers.coverage Cover.checkCovers mdec
              with | Error msg -> raise (Cover.Error (Paths.wrap (r, msg))) end) end)
      mdecs in
    let _ =
      if !Global.chatter >= 3
      then
        begin msg
                (((^) "%covers " ModePrint.modesToString
                    (List.map (begin function | (mdec, r) -> mdec end) mdecs))
                ^ ".\n") end
      else begin () end in ((())
(* MERGE Fri Aug 22 13:43:12 2003 -cs *))
| (fileName, (TotalDec lterm, r)) ->
    let (t_, ((r, rs) as rrs)) = ReconThm.tdeclTotDecl lterm in
    let La = Thm.installTotal (t_, rrs) in
    let _ = map Total.install La in
    let _ =
      ((begin try map Total.checkFam La
        with | Error msg -> raise (Total.Error msg)
        | Error msg -> raise (Cover.Error (Paths.wrap (r, msg)))
        | Error msg -> raise (Reduces.Error msg)
        | Error msg -> raise (Subordinate.Error (Paths.wrap (r, msg))) end)
      (* include region and file *)(*                     | Cover.Error (msg) => covererror (result1, msg)  disabled -cs Thu Jan 29 16:35:13 2004 *)
      (* includes filename *)) in
    let _ =
      if !Global.chatter >= 3
      then begin msg (((^) "%total " ThmPrint.tDeclToString t_) ^ ".\n") end
      else begin () end in
    ((())
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
      (*        val _ = case (result1)
                    of NONE => ()
                     | SOME msg => raise Cover.Error (Paths.wrap (r, "Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] " ^ msg))
*)
      (* %total does not auto-freeze, since the predicate must already be frozen *))
| (fileName, (TerminatesDec lterm, _)) ->
    let (t_, ((r, rs) as rrs)) = ReconThm.tdeclTotDecl lterm in
    let TDecl (_, Callpats callpats) = t_ in
    let La = Thm.installTerminates (t_, rrs) in
    let _ = map (Timers.time Timers.terminate Reduces.checkFam) La in
    let _ =
      if !Global.autoFreeze then begin (begin Subordinate.freeze La; () end) end
      else begin () end in
    let _ =
      if !Global.chatter >= 3
      then begin msg (((^) "%terminates " ThmPrint.tDeclToString t_) ^ ".\n") end
      else begin () end in
    ((())
      (* allow re-declaration since safe? *)(* Thu Mar 10 13:45:42 2005 -fp *)
      (*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookup a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare termination order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *))
| (fileName, (ReducesDec lterm, _)) ->
    let (r_, ((r, rs) as rrs)) = ReconThm.rdeclTorDecl lterm in
    let RDecl (_, Callpats callpats) = r_ in
    let La = Thm.installReduces (r_, rrs) in
    let _ = map (Timers.time Timers.terminate Reduces.checkFamReduction) La in
    let _ =
      if !Global.autoFreeze then begin (begin Subordinate.freeze La; () end) end
      else begin () end in
    let _ =
      if !Global.chatter >= 3
      then begin msg (((^) "%reduces " ThmPrint.rDeclToString r_) ^ ".\n") end
      else begin () end in
    ((())
      (* allow re-declaration since safe? *)(* Thu Mar 10 14:06:13 2005 -fp *)
      (*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare reduction order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
      (*  -bp6/12/99.   *))
| (fileName, (TabledDec tdecl, _)) ->
    let (t_, r) = ReconThm.tableddeclTotabledDecl tdecl in
    let La = Thm.installTabled t_ in
    let _ =
      if !Global.chatter >= 3
      then
        begin msg (((^) "%tabled " ThmPrint.tabledDeclToString t_) ^ ".\n") end
      else begin () end in
    ((())(*  -bp6/12/99.   *))
| (fileName, (KeepTableDec tdecl, _)) ->
    let (t_, r) = ReconThm.keepTabledeclToktDecl tdecl in
    let La = Thm.installKeepTable t_ in
    let _ =
      if !Global.chatter >= 3
      then
        begin msg
                (((^) "%keeptabled " ThmPrint.keepTableDeclToString t_) ^
                   ".\n") end
      else begin () end in
    ()
| (fileName, (TheoremDec tdec, r)) ->
    let Tdec = ReconThm.theoremDecToTheoremDec tdec in
    let _ = ReconTerm.checkErrors r in
    let (GBs, (ConDec (name, _, k, _, v_, l_) as e_)) =
      ThmSyn.theoremDecToConDec (Tdec, r) in
    let _ = FunSyn.labelReset () in
    let _ =
      List.foldr
        (begin function
         | ((g1_, g2_), k) ->
             FunSyn.labelAdd
               (FunSyn.LabelDec
                  ((Int.toString k), (FunSyn.ctxToList g1_),
                    (FunSyn.ctxToList g2_))) end)
      0 GBs in
    let cid = installConDec IntSyn.Ordinary (e_, (fileName, None), r) in
    let MS = ThmSyn.theoremDecToModeSpine (Tdec, r) in
    let _ = ModeTable.installMode (cid, MS) in
    let _ =
      if !Global.chatter >= 3
      then begin msg (((^) "%theorem " Print.conDecToString e_) ^ "\n") end
      else begin () end in
    ()
| (fileName, (ProveDec lterm, r)) ->
    let (PDecl (depth, t_), rrs) = ReconThm.proveToProve lterm in
    let La = Thm.installTerminates (t_, rrs) in
    let _ =
      if !Global.chatter >= 3
      then
        begin msg
                (((("%prove " ^ (Int.toString depth)) ^ " ") ^
                    (ThmPrint.tDeclToString t_))
                   ^ ".\n") end
      else begin () end in
    let _ = Prover.init (depth, La) in
    let _ =
      ((if !Global.chatter >= 3
        then
          begin map
                  (begin function
                   | a ->
                       msg
                         (("%mode " ^
                             (ModePrint.modeToString
                                (a, (valOf (ModeTable.modeLookup a)))))
                            ^ ".\n") end)
          La end
      else begin [()] end)(* mode must be declared!*)) in
  let _ =
    begin try Prover.auto ()
    with
    | Error msg -> raise (Prover.Error (Paths.wrap ((joinregion rrs), msg))) end in
  let _ = if !Global.chatter >= 3 then begin msg "%QED\n" end
    else begin () end in
(((begin Prover.install
         (begin function
          | e_ -> installConDec IntSyn.Ordinary (e_, (fileName, None), r) end);
Skolem.install La end))
(* La is the list of type constants *)(* times itself *))
| (fileName, (EstablishDec lterm, r)) ->
    let (PDecl (depth, t_), rrs) = ReconThm.establishToEstablish lterm in
    let La = Thm.installTerminates (t_, rrs) in
    let _ =
      if !Global.chatter >= 3
      then
        begin msg
                (((("%prove " ^ (Int.toString depth)) ^ " ") ^
                    (ThmPrint.tDeclToString t_))
                   ^ ".\n") end
      else begin () end in
    let _ = Prover.init (depth, La) in
    let _ =
      ((if !Global.chatter >= 3
        then
          begin map
                  (begin function
                   | a ->
                       msg
                         (("%mode " ^
                             (ModePrint.modeToString
                                (a, (valOf (ModeTable.modeLookup a)))))
                            ^ ".\n") end)
          La end
      else begin [()] end)(* mode must be declared!*)) in
  let _ =
    begin try Prover.auto ()
    with
    | Error msg -> raise (Prover.Error (Paths.wrap ((joinregion rrs), msg))) end in
  ((Prover.install
      (begin function
       | e_ -> installConDec IntSyn.Ordinary (e_, (fileName, None), r) end))
(* La is the list of type constants *)(* times itself *))
| (fileName, (AssertDec aterm, _)) ->
    let _ =
      if not !Global.unsafe
      then
        begin raise (ThmSyn.Error "%assert not safe: Toggle `unsafe' flag") end
      else begin () end in
let ((Callpats (l_) as cp), rrs) = ReconThm.assertToAssert aterm in
let La = map (begin function | (c, p_) -> c end) l_ in
let _ =
if !Global.chatter >= 3
then begin msg (("%assert " ^ (ThmPrint.callpatsToString cp)) ^ ".\n") end
else begin () end in
let _ =
((if !Global.chatter >= 3
  then
    begin map
            (begin function
             | a ->
                 msg
                   (("%mode " ^
                       (ModePrint.modeToString
                          (a, (valOf (ModeTable.modeLookup a)))))
                      ^ ".\n") end)
    La end
else begin [()] end)(* mode must be declared!*)) in
((Skolem.install La)(* La is the list of type constants *))
| (fileName, (WorldDec wdecl, _)) ->
    let (WDecl (qids, (Callpats cpa as cp)), rs) =
      ReconThm.wdeclTowDecl wdecl in
    let _ =
      ListPair.app
        (begin function
         | ((a, _), r) ->
             if Subordinate.frozen [a]
             then
               begin raise
                       (WorldSyn.Error
                          (Paths.wrapLoc
                             ((Paths.Loc (fileName, r)),
                               ((^) "Cannot declare worlds for frozen family "
                                  Names.qidToString (Names.constQid a))))) end
             else begin () end end)
      (cpa, rs) in
let rec flatten arg__0 arg__1 =
begin match (arg__0, arg__1) with
| ([], f_) -> f_
| (cid::l_, f_) ->
    (begin match IntSyn.sgnLookup cid with
     | BlockDec _ -> flatten l_ (cid :: f_)
     | BlockDef (_, _, l'_) -> flatten (l_ @ l'_) f_ end) end in
let w_ =
Tomega.Worlds
  (flatten
     (List.map
        (begin function
         | qid ->
             (begin match Names.constLookup qid with
              | None ->
                  raise
                    (Names.Error
                       (((^) "Undeclared label " Names.qidToString
                           (valOf (Names.constUndef qid)))
                          ^ "."))
              | Some cid -> cid end) end) qids)
[]) in
let _ =
((begin try
          List.app (begin function | (a, _) -> WorldSyn.install (a, w_) end)
          cpa
with
| Error msg ->
    raise
      (WorldSyn.Error
         (Paths.wrapLoc ((Paths.Loc (fileName, (joinregions rs))), msg))) end)
(* error location inaccurate here *)) in
let _ =
if !Global.autoFreeze
then
  begin (begin Subordinate.freeze
                 (List.map (begin function | (a, _) -> a end) cpa);
  () end) end else begin () end in
let _ =
if !Global.chatter >= 3
then
  begin msg
          (((^) (((^) "%worlds " Print.worldsToString w_) ^ " ")
              ThmPrint.callpatsToString cp)
             ^ ".\n") end
else begin () end in
(((begin Timers.time Timers.worlds
         (map (begin function | (a, _) -> WorldSyn.worldcheck w_ a end))
 cpa; () end))
(*if !Global.doubleCheck
             then (map (fn (a,_) => Worldify.worldify a) cpa; ())
           else  ()  --cs Sat Aug 27 22:04:29 2005 *))
| (fileName, ((SigDef _, _) as declr)) ->
    install1WithSig (fileName, None, declr)
| (fileName, ((StructDec _, _) as declr)) ->
    install1WithSig (fileName, None, declr)
| (fileName, ((Include _, _) as declr)) ->
    install1WithSig (fileName, None, declr)
| (fileName, ((Open _, _) as declr)) ->
    install1WithSig (fileName, None, declr)
| (fileName, (Use name, r)) ->
    (begin match !context with
     | None -> CSManager.useSolver name
     | _ ->
         raise
           (ModSyn.Error
              (Paths.wrap (r, "%use declaration needs to be at top level"))) end) end
(* Assert declaration *)(* Establish declaration *)
(* Prove declaration *)(* Theorem declaration *)
(* %keepTable declaration *)(* Tabled declaration *)
(* Reduces declaration *)(* -bp *)
(* Termination declaration *)(* time activities separately in total.fun *)
(* Total declaration *)(* Coverage declaration *)
(* Unique declaration *)(* Mode declaration *)
(* Name preference declaration for printing *)(* Fixity declaration for operator precedence parsing *)
(* -ABP 4/4/03 *)(* %compile <qids> *)
(* %deterministic <qid> ... *)(* %thaw <qid> ... *)
(* %freeze <qid> ... *)(* %subord (<qid> <qid>) ... *)
(* %trustme <decl> *)(* Solve.query might raise Solve.AbortQuery (msg) *)
(* %queryTabled <expected> <try> A or %query <expected> <try> X : A *)
(* Solve.query might raise Fquery.AbortQuery (msg) *)
(* %fquery <expected> <try> A or %fquery <expected> <try> X : A *)
(* Solve.query might raise Solve.AbortQuery (msg) *)
(* %query <expected> <try> A or %query <expected> <try> X : A *)
(* Solve declarations %solve c : A *)(* these are like definitions, but entered into the program table *)
(* Clauses %clause c = U or %clause c : V = U or %clause c : V *)
(* Abbreviations %abbrev c = U and %abbrev c : V = U *)
(* Constant declarations c : V, c : V = U plus variations *)
let rec install1WithSig =
  begin function
  | (fileName, moduleOpt, (SigDef sigdef, r)) ->
      let (idOpt, module_, wherecls) =
        ReconModule.sigdefToSigdef (sigdef, moduleOpt) in
      let module' =
        foldl
          (begin function
           | (inst, module_) -> ReconModule.moduleWhere (module_, inst) end)
        module_ wherecls in
      let name =
        begin try
                ((begin match idOpt with
                  | Some id ->
                      (begin ModSyn.installSigDef (id, module'); id end)
                | None -> "_" end)
        (* anonymous *))
        with | Error msg -> raise (ModSyn.Error (Paths.wrap (r, msg))) end in
let _ =
  if !Global.chatter >= 3
  then begin msg (("%sig " ^ name) ^ " = { ... }.\n") end else begin () end in
((())(* FIX: should probably time this -kw *))
| (fileName, moduleOpt, (StructDec structdec, r)) ->
    (begin match ReconModule.structdecToStructDec (structdec, moduleOpt) with
     | StructDec (idOpt, module_, wherecls) ->
         let module' =
           foldl
             (begin function
              | (inst, module_) -> ReconModule.moduleWhere (module_, inst) end)
           module_ wherecls in
       let name =
         ((begin match idOpt with
           | Some id ->
               (begin installStrDec
                        ((IntSyn.StrDec (id, None)), module', r, false);
                id end)
         | None -> "_" end)(* anonymous *)) in
   let _ =
     if !Global.chatter = 3
     then begin msg (("%struct " ^ name) ^ " : { ... }.\n") end
     else begin () end in
  ()
| StructDef (idOpt, mid) ->
    let ns = Names.getComponents mid in
    let module_ = ModSyn.abstractModule (ns, (Some mid)) in
    let name =
      ((begin match idOpt with
        | Some id ->
            (begin installStrDec
                     ((IntSyn.StrDec (id, None)), module_, r, true);
             id end)
      | None -> "_" end)(* anonymous *)) in
    let _ =
      if !Global.chatter = 3
      then
        begin msg
                (((^) (("%struct " ^ name) ^ " = ") Names.qidToString
                    (Names.structQid mid))
                   ^ ".\n") end
      else begin () end in
  () end)
| (fileName, moduleOpt, (Include sigexp, r)) ->
    let (module_, wherecls) = ReconModule.sigexpToSigexp (sigexp, moduleOpt) in
    let module' =
      foldl
        (begin function
         | (inst, module_) -> ReconModule.moduleWhere (module_, inst) end)
      module_ wherecls in
    let _ = includeSig (module', r, false) in
    let _ = if !Global.chatter = 3 then begin msg "%include { ... }.\n" end
      else begin () end in
    ()
| (fileName, None, (Open strexp, r)) ->
    let mid = ReconModule.strexpToStrexp strexp in
    let ns = Names.getComponents mid in
    let module_ = ModSyn.abstractModule (ns, (Some mid)) in
    let _ = includeSig (module_, r, true) in
    let _ =
      if !Global.chatter = 3
      then
        begin msg
                (((^) "%open " Names.qidToString (Names.structQid mid)) ^
                   ".\n") end
      else begin () end in
    () end(* Open declaration *)(* Include declaration *)
(* Structure declaration *)(* Signature declaration *)
let rec installSubsig (fileName, s) =
  let namespace = Names.newNamespace () in
  let (mark, markStruct) = IntSyn.sgnSize () in
  let markSigDef = ModSyn.sigDefSize () in
  let oldContext = !context in
  let _ = (:=) context Some namespace in
  let _ =
    if !Global.chatter >= 4 then begin msg "\n% begin subsignature\n" end
    else begin () end in
  let rec install s = install' (Timers.time Timers.parsing S.expose s)
  and install' =
    begin function
    | Cons ((Parser.BeginSubsig, _), s') ->
        install (installSubsig (fileName, s'))
    | Cons ((Parser.EndSubsig, _), s') -> s'
    | Cons (declr, s') -> (begin install1 (fileName, declr); install s' end) end in
  let result =
    begin try
            let s' = install s in
            let module_ = ModSyn.abstractModule (namespace, None) in
            let _ =
              if !Global.chatter >= 4
              then begin msg "% end subsignature\n\n" end else begin () end in
            Value (module_, s')
    with | exn -> Exception exn end in
  let _ = context := oldContext in
  let _ = Names.resetFrom (mark, markStruct) in
  let _ = Index.resetFrom mark in
  let _ = IndexSkolem.resetFrom mark in
  let _ = ModSyn.resetFrom markSigDef in
  ((begin match result with
    | Value (module_, s') ->
        let Cons (declr, s'') = Timers.time Timers.parsing S.expose s' in
        (begin install1WithSig (fileName, (Some module_), declr); s'' end)
    | Exception exn -> raise exn end)
    (* val _ = ModeTable.resetFrom mark *)(* val _ = Total.resetFrom mark *)
    (* val _ = Subordinate.resetFrom mark  ouch! *)
    (* val _ = Reduces.resetFrom mark *)(* Origins, CompSyn, FunSyn harmless? -kw *)
    (* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for now -kw *))
let rec loadFile fileName =
  handleExceptions 0 fileName (withOpenIn fileName)
    (begin function
     | instream ->
         let _ = ReconTerm.resetErrors fileName in
         let rec install s = install' (Timers.time Timers.parsing S.expose s)
         and install' =
           begin function
           | S.Empty -> OK
           | Cons ((Parser.BeginSubsig, _), s') ->
               install (installSubsig (fileName, s'))
           | Cons (decl, s') ->
               (begin install1 (fileName, decl); install s' end) end(* now done in installConDec *)
           (* Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) *) in
       install (Parser.parseStream instream) end)
let rec loadString str =
  handleExceptions 0 "string"
    (begin function
     | () ->
         let _ = ReconTerm.resetErrors "string" in
         let rec install s = install' (Timers.time Timers.parsing S.expose s)
         and install' =
           begin function
           | S.Empty -> OK
           | Cons ((Parser.BeginSubsig, _), s') ->
               (begin installSubsig ("string", s'); install s' end)
           | Cons (decl, s') ->
               (begin install1 ("string", decl); install s' end) end in
   install (Parser.parseStream (TextIO.openString str)) end)
()
let rec sLoop () = if Solve.qLoop () then begin OK end else begin ABORT end
let rec topLoop () =
  ((begin match handleExceptions 0 "stdIn" sLoop () with
    | ABORT -> topLoop ()
    | OK -> () end)
  (* "stdIn" as fake fileName *))
let rec top () = topLoop ()
let rec installCSMDec (conDec, optFixity, mdecL) =
  let _ = ModeCheck.checkD (conDec, "%use", None) in
  let cid =
    installConDec IntSyn.FromCS (conDec, ("", None), (Paths.Reg (0, 0))) in
  let _ =
    if !Global.chatter >= 3
    then begin msg ((Print.conDecToString conDec) ^ "\n") end
    else begin () end in
  let _ =
    begin match optFixity with
    | Some fixity ->
        (begin Names.installFixity (cid, fixity);
         if !Global.chatter >= 3
         then
           begin msg
                   (((^) (((^) (if !Global.chatter >= 4 then begin "%" end
                             else begin "" end)
                       Names.Fixity.toString fixity)
                      ^ " ") Names.qidToString (Names.constQid cid))
           ^ ".\n") end
    else begin () end end)
  | None -> () end in
let _ =
List.app (begin function | mdec -> ModeTable.installMmode (cid, mdec) end)
mdecL in ((cid)
(* put a more reasonable region here? -kw *))
let _ = CSManager.setInstallFN installCSMDec
let rec reset () =
  ((begin IntSyn.sgnReset ();
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
    context := None end)
  (* -fp Wed Mar  9 20:24:45 2005 *)(* -fp *)(* -fp *)
  (* -bp *)(* -bp *)(* necessary? -fp; yes - bp*)
  (*  -bp *)(* resetting substitution trees *))
let rec readDecl () =
  handleExceptions 0 "stdIn"
    (begin function
     | () ->
         let _ = ReconTerm.resetErrors "stdIn" in
         let rec install s = install' (Timers.time Timers.parsing S.expose s)
         and install' =
           begin function
           | S.Empty -> ABORT
           | Cons ((Parser.BeginSubsig, _), s') ->
               (begin installSubsig ("stdIn", s'); OK end)
           | Cons (decl, s') -> (begin install1 ("stdIn", decl); OK end) end in
   install (Parser.parseStream TextIO.stdIn) end)
()
let rec decl id =
  begin match Names.stringToQid id with
  | None ->
      (begin msg (id ^ " is not a well-formed qualified identifier\n"); ABORT end)
  | Some qid ->
      (begin match Names.constLookup qid with
       | None ->
           (begin msg
                    ((Names.qidToString (valOf (Names.constUndef qid))) ^
                       " has not been declared\n");
            ABORT end)
      | Some cid -> decl' cid end) end
let rec decl' cid =
  let conDec = IntSyn.sgnLookup cid in
  ((begin msg ((Print.conDecToString conDec) ^ "\n"); OK end)
  (* val fixity = Names.getFixity (cid) *)(* can't get name preference right now *)
  (* val mode = ModeTable.modeLookup (cid) *)(* can't get termination declaration *))
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
    let rec create file = (file, (ref None))
    let rec fileName (file, _) = file
    let rec editName edit (file, mtime) = ((edit file), mtime)
    let rec modified =
      begin function
      | (_, { contents = None }) -> true
      | (file, { contents = Some time }) ->
          (begin match Time.compare (time, (OS.FileSys.modTime file)) with
           | EQUAL -> false
           | _ -> true end) end
  let rec makeModified (_, mtime) = mtime := None
  let rec makeUnmodified (file, mtime) =
    (:=) mtime Some (OS.FileSys.modTime file) end

module Config =
  struct
    type nonrec config = (string * ModFile.mfile list)
    let suffix = ref "cfg"
    let rec mkRel (prefix, path) =
      OS.Path.mkCanonical (if OS.Path.isAbsolute path then begin path end
        else begin OS.Path.concat (prefix, path) end)
  let rec read config =
    let rec appendUniq (l1, l2) =
      let rec appendUniq' =
        begin function
        | x::l2 -> if List.exists (begin function | y -> x = y end) l1
            then begin appendUniq' l2 end
        else begin (::) x appendUniq' l2 end
      | [] -> List.rev l1 end in
  List.rev (appendUniq' (List.rev l2)) in
let rec isConfig item =
let suffix_size = (String.size !suffix) + 1 in
let suffix_start = (String.size item) - suffix_size in
(suffix_start >= 0) &&
  ((String.substring (item, suffix_start, suffix_size)) =
     ((!) ((^) ".") suffix)) in
let rec fromUnixPath path =
let vol = OS.Path.getVolume config in
let isAbs = String.isPrefix "/" path in
let arcs = String.tokens (begin function | c -> c = '/' end) path in
OS.Path.toString { isAbs; vol; arcs } in
let rec read' (sources, configs) config =
withOpenIn config
  (begin function
   | instream ->
       let { dir = configDir; file = _; file = _ } =
         OS.Path.splitDirFile config in
       let rec parseItem (sources, configs) item =
         if isConfig item
         then
           begin (((if
                      List.exists
                        (begin function | config' -> item = config' end)
                      configs
           then begin (sources, configs) end
         else begin read' (sources, (item :: configs)) item end))
         (* we have already read this one *)) end
       else begin
         ((if List.exists (begin function | source' -> item = source' end)
             sources
         then begin (sources, configs) end
       else begin ((sources @ [item]), configs) end)
  (* we have already collected this one *)) end in
let rec parseLine (sources, configs) line =
((if Substring.isEmpty line then begin (sources, configs) end
else begin
  (let line' = Substring.dropl Char.isSpace line in
   parseLine' (sources, configs) line') end)
(* end of file *))
and parseLine' (sources, configs) line =
  ((if (((Substring.isEmpty line) || ((Substring.sub (line, 0)) = '%'))
      (* empty line *))
    then begin parseStream (sources, configs) end
  else begin
    (let line' = Substring.string (Substring.takel (not o Char.isSpace) line) in
     let item = mkRel (configDir, (fromUnixPath line')) in
     parseStream (parseItem (sources, configs) item)) end)
(* comment *))
and parseStream (sources, configs) =
  let line = Compat.Substring.full (Compat.inputLine97 instream) in
  parseLine (sources, configs) line in parseStream (sources, configs) end) in
let pwdir = OS.FileSys.getDir () in
(((pwdir,
  (List.map ModFile.create ((fun r -> r.1) (read' ([], [config]) config)))))
(* appendUniq (list1, list2) appends list2 to list1, removing all
               elements of list2 which are already in list1.
            *)
(* isConfig (item) is true iff item has the suffix of a
               configuration file.
            *)
(* fromUnixPath path transforms path (assumed to be in Unix form)
               to the local OS conventions.
            *)
(*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *))
let rec readWithout (s, c) =
  let (d, fs) = read s in
  let (d', fs') = c in
  let fns' = map (begin function | m -> mkRel (d', (ModFile.fileName m)) end)
    fs' in
  let rec redundant m =
    let n = mkRel (d, (ModFile.fileName m)) in
    List.exists (begin function | n' -> n = n' end) fns' in
  (d, (List.filter (not o redundant) fs))
let rec loadAbort =
  begin function
  | (mfile, OK) ->
      let status = loadFile (ModFile.fileName mfile) in
      (begin (begin match status with
              | OK -> ModFile.makeUnmodified mfile
              | _ -> () end);
        status end)
  | (_, ABORT) -> ABORT end
let rec load ((_, sources) as config) =
  begin reset (); List.app ModFile.makeModified sources; append config end
let rec append (pwdir, sources) =
  let rec fromFirstModified =
    begin function
    | [] -> []
    | x::xs as sources -> if ModFile.modified x then begin sources end
        else begin fromFirstModified xs end end in
let rec mkAbsolute p =
Compat.OS.Path.mkAbsolute { path = p; relativeTo = pwdir } in
let sources' = if (=) pwdir OS.FileSys.getDir () then begin sources end
else begin List.map (ModFile.editName mkAbsolute) sources end in
let sources'' = fromFirstModified sources' in
((List.foldl loadAbort OK sources'')
(* allow shorter messages if safe *))
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
    let implicit = Print.implicit
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
    type 'a spec_ =
      | None 
      | Some of 'a list 
      | All 
    val trace : string spec_ -> unit
    val break : string spec_ -> unit
    val detail : int ref
    val show : unit -> unit
    val reset : unit -> unit
  end = Trace 
module Timers :
  sig
    val show : unit -> unit
    val reset : unit -> unit
    val check : unit -> unit
  end = Timers 
module OS :
  sig
    val chDir : string -> unit
    val getDir : unit -> string
    val exit : unit -> unit
  end =
  struct
    let chDir = OS.FileSys.chDir
    let getDir = OS.FileSys.getDir
    let rec exit () = OS.Process.exit OS.Process.success
  end 
module Compile : sig type opt_ = CompSyn.opt_ val optimize : opt_ ref end =
  struct type opt_ = CompSyn.opt_
         let optimize = CompSyn.optimize end 
module Recon :
  sig
    type traceMode_ = ReconTerm.traceMode_
    val trace : bool ref
    val traceMode : traceMode_ ref
  end =
  struct
    type traceMode_ = ReconTerm.traceMode_
    let trace = ReconTerm.trace
    let traceMode = ReconTerm.traceMode
  end 
module Recon :
  sig
    type traceMode_ = ReconTerm.traceMode_
    val trace : bool ref
    val traceMode : traceMode_ ref
  end =
  struct
    type traceMode_ = ReconTerm.traceMode_
    let trace = ReconTerm.trace
    let traceMode = ReconTerm.traceMode
  end 
module Prover :
  sig
    type strategy_ = MetaGlobal.strategy_
    val strategy : strategy_ ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end =
  struct
    type strategy_ = MetaGlobal.strategy_
    let strategy = MetaGlobal.strategy
    let maxSplit = MetaGlobal.maxSplit
    let maxRecurse = MetaGlobal.maxRecurse
  end 
let (chatter : int ref) = Global.chatter
let (doubleCheck : bool ref) = Global.doubleCheck
let (unsafe : bool ref) = Global.unsafe
let (autoFreeze : bool ref) = Global.autoFreeze
let (timeLimit : Time.time option ref) = Global.timeLimit
type status_ = status_
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
    val load : config -> status_
    val append : config -> status_
    val define : string list -> config
  end = Config 
let make = make
let version = Version.version_string
module Table :
  sig
    type strategy_ = TableParam.strategy_
    val strategy : strategy_ ref
    val strengthen : bool ref
    val resetGlobalTable : unit -> unit
    val top : unit -> unit
  end =
  struct
    type strategy_ = TableParam.strategy_
    let strategy = TableParam.strategy
    let strengthen = TableParam.strengthen
    let resetGlobalTable = TableParam.resetGlobalTable
    let rec top () =
      let rec sLoopT () = if Solve.qLoopT () then begin OK end
        else begin ABORT end in
    let rec topLoopT () =
      ((begin match handleExceptions 0 "stdIn" sLoopT () with
        | ABORT -> topLoopT ()
        | OK -> () end)
      (* "stdIn" as fake fileName *)) in
    topLoopT () end  end
