module type SERVER  =
  sig val server : (string * string list) -> OS.Process.status end
module Server(Server:sig
                       module SigINT : SIGINT
                       module Timing : TIMING
                       module Lexer : LEXER
                       module Twelf : TWELF
                     end) : SERVER =
  struct
    let (globalConfig : Twelf.Config.config option ref) = ref None
    let rec readLine () =
      let rec getLine () =
        begin try Compat.inputLine97 TextIO.stdIn
        with | SysErr (_, Some _) -> getLine () end in
    let line = getLine () in
    let rec triml ss = Substring.dropl Char.isSpace ss in
    let rec trimr ss = Substring.dropr Char.isSpace ss in
    let line' = triml (trimr (Compat.Substring.full line)) in
    ((if line = "" then begin ("OS.exit", "") end
      else begin if (Substring.size line') = 0 then begin readLine () end
        else begin
          (let (command', args') = Substring.position " " line' in
           ((Substring.string command'), (Substring.string (triml args')))) end end)
      (* val line = TextIO.inputLine (TextIO.stdIn) *)
      (* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *))
let rec tokenize args = String.tokens Char.isSpace args
exception Error of string 
let rec error msg = raise (Error msg)
let rec quote string = ("`" ^ string) ^ "'"
let rec issue =
  begin function
  | Twelf.OK -> print "%% OK %%\n"
  | Twelf.ABORT -> print "%% ABORT %%\n" end
let rec checkEmpty =
  begin function | "" -> () | args -> error "Extraneous arguments" end
let rec getFile =
  begin function | ("", default) -> default | (fileName, default) -> fileName end
let rec getFile' =
  begin function | "" -> error "Missing filename" | fileName -> fileName end
let rec getId =
  begin function
  | id::[] -> id
  | [] -> error "Missing identifier"
  | ts -> error "Extraneous arguments" end
let rec getIds ids = ids
let rec getStrategy =
  begin function
  | "FRS"::[] -> Twelf.Prover.FRS
  | "RFS"::[] -> Twelf.Prover.RFS
  | [] -> error "Missing strategy"
  | t::[] -> error ((quote t) ^ " is not a strategy (must be FRS or RFS)")
  | ts -> error "Extraneous arguments" end
let rec strategyToString =
  begin function | Twelf.Prover.FRS -> "FRS" | Twelf.Prover.RFS -> "RFS" end
let rec getBool =
  begin function
  | "true"::[] -> true
  | "false"::[] -> false
  | [] -> error "Missing boolean value"
  | t::[] -> error ((quote t) ^ " is not a boolean")
  | ts -> error "Extraneous arguments" end
let rec getNat =
  begin function
  | t::[] ->
      (begin try Lexer.stringToNat t
       with | NotDigit char -> error ((quote t) ^ " is not a natural number") end)
  | [] -> error "Missing natural number" | ts -> error "Extraneous arguments" end
let rec getLimit =
  begin function
  | "*"::[] -> None
  | t::ts -> Some (getNat (t :: ts))
  | [] -> error "Missing `*' or natural number" end
let rec limitToString =
  begin function | None -> "*" | Some i -> Int.toString i end
let rec getTableStrategy =
  begin function
  | "Variant"::[] -> Twelf.Table.Variant
  | "Subsumption"::[] -> Twelf.Table.Subsumption
  | [] -> error "Missing tabling strategy"
  | t::[] ->
      error
        ((quote t) ^
           " is not a tabling strategy (must be Variant or Subsumption)")
  | ts -> error "Extraneous arguments" end
let rec tableStrategyToString =
  begin function
  | Twelf.Table.Variant -> "Variant"
  | Twelf.Table.Subsumption -> "Subsumption" end
let rec getReconTraceMode =
  begin function
  | "Progressive"::[] -> Twelf.Recon.Progressive
  | "Omniscient"::[] -> Twelf.Recon.Omniscient
  | [] -> error "Missing tracing reconstruction mode"
  | t::[] ->
      error
        ((quote t) ^
           " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)")
  | ts -> error "Extraneous arguments" end
let rec reconTraceModeToString =
  begin function
  | Twelf.Recon.Progressive -> "Progressive"
  | Twelf.Recon.Omniscient -> "Omniscient" end
let rec getCompileOpt =
  begin function
  | "No"::[] -> Twelf.Compile.No
  | "LinearHeads"::[] -> Twelf.Compile.LinearHeads
  | "Indexing"::[] -> Twelf.Compile.Indexing
  | [] -> error "Missing tabling strategy"
  | t::[] ->
      error
        ((quote t) ^
           " is not a compile option (must be No, LinearHeads, or Indexing ")
  | ts -> error "Extraneous arguments" end
let rec compOptToString =
  begin function
  | Twelf.Compile.No -> "No"
  | Twelf.Compile.LinearHeads -> "LinearHeads"
  | Twelf.Compile.Indexing -> "Indexing" end
let rec setParm =
  begin function
  | "chatter"::ts -> (:=) Twelf.chatter getNat ts
  | "doubleCheck"::ts -> (:=) Twelf.doubleCheck getBool ts
  | "unsafe"::ts -> (:=) Twelf.unsafe getBool ts
  | "autoFreeze"::ts -> (:=) Twelf.autoFreeze getBool ts
  | "Print.implicit"::ts -> (:=) Twelf.Print.implicit getBool ts
  | "Print.depth"::ts -> (:=) Twelf.Print.depth getLimit ts
  | "Print.length"::ts -> (:=) Twelf.Print.length getLimit ts
  | "Print.indent"::ts -> (:=) Twelf.Print.indent getNat ts
  | "Print.width"::ts -> (:=) Twelf.Print.width getNat ts
  | "Trace.detail"::ts -> (:=) Twelf.Trace.detail getNat ts
  | "Compile.optimize"::ts -> (:=) Twelf.Compile.optimize getCompileOpt ts
  | "Recon.trace"::ts -> (:=) Twelf.Recon.trace getBool ts
  | "Recon.traceMode"::ts -> (:=) Twelf.Recon.traceMode getReconTraceMode ts
  | "Prover.strategy"::ts -> (:=) Twelf.Prover.strategy getStrategy ts
  | "Prover.maxSplit"::ts -> (:=) Twelf.Prover.maxSplit getNat ts
  | "Prover.maxRecurse"::ts -> (:=) Twelf.Prover.maxRecurse getNat ts
  | "Table.strategy"::ts -> (:=) Twelf.Table.strategy getTableStrategy ts
  | "Table.strengthen"::ts -> (:=) Twelf.Table.strengthen getBool ts
  | t::ts -> error ((^) "Unknown parameter " quote t)
  | [] -> error "Missing parameter" end
let rec getParm =
  begin function
  | "chatter"::ts -> Int.toString !Twelf.chatter
  | "doubleCheck"::ts -> Bool.toString !Twelf.doubleCheck
  | "unsafe"::ts -> Bool.toString !Twelf.unsafe
  | "autoFreeze"::ts -> Bool.toString !Twelf.autoFreeze
  | "Print.implicit"::ts -> Bool.toString !Twelf.Print.implicit
  | "Print.depth"::ts -> limitToString !Twelf.Print.depth
  | "Print.length"::ts -> limitToString !Twelf.Print.length
  | "Print.indent"::ts -> Int.toString !Twelf.Print.indent
  | "Print.width"::ts -> Int.toString !Twelf.Print.width
  | "Trace.detail"::ts -> Int.toString !Twelf.Trace.detail
  | "Compile.optimize"::ts -> compOptToString !Twelf.Compile.optimize
  | "Recon.trace"::ts -> Bool.toString !Twelf.Recon.trace
  | "Recon.traceMode"::ts -> reconTraceModeToString !Twelf.Recon.traceMode
  | "Prover.strategy"::ts -> strategyToString !Twelf.Prover.strategy
  | "Prover.maxSplit"::ts -> Int.toString !Twelf.Prover.maxSplit
  | "Prover.maxRecurse"::ts -> Int.toString !Twelf.Prover.maxRecurse
  | "Table.strategy"::ts -> tableStrategyToString !Twelf.Table.strategy
  | t::ts -> error ((^) "Unknown parameter " quote t)
  | [] -> error "Missing parameter" end
let helpString =
  "Commands:\n  set <parameter> <value>     - Set <parameter> to <value>\n  get <parameter>             - Print the current value of <parameter>\n  Trace.trace <id1> ... <idn> - Trace given constants\n  Trace.traceAll              - Trace all constants\n  Trace.untrace               - Untrace all constants\n  Trace.break <id1> ... <idn> - Set breakpoint for given constants\n  Trace.breakAll              - Break on all constants\n  Trace.unbreak               - Remove all breakpoints\n  Trace.show                  - Show current trace and breakpoints\n  Trace.reset                 - Reset all tracing and breaking\n  Print.sgn                   - Print current signature\n  Print.prog                  - Print current signature as program\n  Print.subord                - Print current subordination relation\n  Print.domains               - Print registered constraint domains\n  Print.TeX.sgn               - Print signature in TeX format\n  Print.TeX.prog              - Print signature in TeX format as program\n  Timers.show                 - Print and reset timers\n  Timers.reset                - Reset timers\n  Timers.check                - Print, but do not reset timers.\n  OS.chDir <file>             - Change working directory to <file>\n  OS.getDir                   - Print current working directory\n  OS.exit                     - Exit Twelf server\n  quit                        - Quit Twelf server (same as exit)\n  Config.read <file>          - Read current configuration from <file>\n  Config.load                 - Load current configuration\n  Config.append               - Load current configuration without prior reset\n  make <file>                 - Read and load configuration from <file>\n  reset                       - Reset global signature.\n  loadFile <file>             - Load Twelf file <file>\n  decl <id>                   - Show constant declaration for <id>\n  top                         - Enter interactive query loop\n  Table.top                   - Enter interactive loop for tables queries\n  version                     - Print Twelf server's version\n  help                        - Print this help message\n\nParameters:\n  chatter <nat>               - Level of verbosity (0 = none, 3 = default)\n  doubleCheck <bool>          - Perform additional internal type-checking\n  unsafe <bool>               - Allow unsafe operations (%assert)\n  autoFreeze <bool>           - Freeze families involved in meta-theorems\n  Print.implicit <bool>       - Print implicit arguments\n  Print.depth <limit>         - Cut off printing at depth <limit>\n  Print.length <limit>        - Cut off printing at length <limit>\n  Print.indent <nat>          - Indent by <nat> spaces\n  Print.width <nat>           - Line width for formatting\n  Trace.detail <nat>          - Detail of tracing\n  Compile.optimize <bool>     - Optimize during translation to clauses\n  Recon.trace <bool>          - Trace term reconstruction\n  Recon.traceMode <reconTraceMode> - Term reconstruction tracing mode\n  Prover.strategy <strategy>  - Prover strategy\n  Prover.maxSplit <nat>       - Prover splitting depth bound\n  Prover.maxRecurse <nat>     - Prover recursion depth bound\n  Table.strategy <tableStrategy>   - Tabling strategy\n\nServer types:\n  file                        - File name, relative to working directory\n  id                          - A Twelf identifier\n  bool                        - Either `true' or `false'\n  nat                         - A natural number (starting at `0')\n  limit                       - Either `*' (no limit) or a natural number\n  reconTraceMode              - Either `Progressive' or `Omniscient'\n  strategy                    - Either `FRS' or `RFS'\n  tableStrategy               - Either `Variant' or `Subsumption'\n\nSee http://www.cs.cmu.edu/~twelf/guide-1-4/ for more information,\nor type M-x twelf-info (C-c C-h) in Emacs.\n"
let rec serve' =
  begin function
  | ("set", args) -> (begin setParm (tokenize args); serve Twelf.OK end)
  | ("get", args) ->
      (begin print ((getParm (tokenize args)) ^ "\n"); serve Twelf.OK end)
  | ("Style.check", args) ->
      (begin checkEmpty args; StyleCheck.check (); serve Twelf.OK end)
| ("Print.sgn", args) ->
    (begin checkEmpty args; Twelf.Print.sgn (); serve Twelf.OK end)
| ("Print.prog", args) ->
    (begin checkEmpty args; Twelf.Print.prog (); serve Twelf.OK end)
| ("Print.subord", args) ->
    (begin checkEmpty args; Twelf.Print.subord (); serve Twelf.OK end)
| ("Print.domains", args) ->
    (begin checkEmpty args; Twelf.Print.domains (); serve Twelf.OK end)
| ("Print.TeX.sgn", args) ->
    (begin checkEmpty args; Twelf.Print.TeX.sgn (); serve Twelf.OK end)
| ("Print.TeX.prog", args) ->
    (begin checkEmpty args; Twelf.Print.TeX.prog (); serve Twelf.OK end)
| ("Trace.trace", args) ->
    (begin Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
     serve Twelf.OK end)
| ("Trace.traceAll", args) ->
    (begin checkEmpty args; Twelf.Trace.trace Twelf.Trace.All; serve Twelf.OK end)
| ("Trace.untrace", args) ->
    (begin checkEmpty args;
     Twelf.Trace.trace Twelf.Trace.None;
     serve Twelf.OK end)
| ("Trace.break", args) ->
    (begin Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
     serve Twelf.OK end)
| ("Trace.breakAll", args) ->
    (begin checkEmpty args; Twelf.Trace.break Twelf.Trace.All; serve Twelf.OK end)
| ("Trace.unbreak", args) ->
    (begin checkEmpty args;
     Twelf.Trace.break Twelf.Trace.None;
     serve Twelf.OK end)
| ("Trace.show", args) ->
    (begin checkEmpty args; Twelf.Trace.show (); serve Twelf.OK end)
| ("Trace.reset", args) ->
    (begin checkEmpty args; Twelf.Trace.reset (); serve Twelf.OK end)
| ("Timers.show", args) ->
    (begin checkEmpty args; Timers.show (); serve Twelf.OK end)
| ("Timers.reset", args) ->
    (begin checkEmpty args; Timers.reset (); serve Twelf.OK end)
| ("Timers.check", args) ->
    (begin checkEmpty args; Timers.reset (); serve Twelf.OK end)
| ("OS.chDir", args) ->
    (begin Twelf.OS.chDir (getFile' args); serve Twelf.OK end)
| ("OS.getDir", args) ->
    (begin checkEmpty args;
     print ((Twelf.OS.getDir ()) ^ "\n");
     serve Twelf.OK end)
| ("OS.exit", args) -> (begin checkEmpty args; () end) | ("quit", args) -> ()
| ("Config.read", args) ->
    let fileName = getFile (args, "sources.cfg") in
    (begin (:=) globalConfig Some (Twelf.Config.read fileName);
     serve Twelf.OK end)
| ("Config.load", args) ->
    (begin (begin match !globalConfig with
            | None ->
                (:=) globalConfig Some (Twelf.Config.read "sources.cfg")
            | _ -> () end);
    serve (Twelf.Config.load (valOf !globalConfig)) end)
| ("Config.append", args) ->
    (begin (begin match !globalConfig with
            | None ->
                (:=) globalConfig Some (Twelf.Config.read "sources.cfg")
            | _ -> () end);
    serve (Twelf.Config.append (valOf !globalConfig)) end)
| ("make", args) ->
    let fileName = getFile (args, "sources.cfg") in
    (begin (:=) globalConfig Some (Twelf.Config.read fileName);
     serve (Twelf.Config.load (valOf !globalConfig)) end)
| ("reset", args) ->
    (begin checkEmpty args; Twelf.reset (); serve Twelf.OK end)
| ("loadFile", args) -> serve (Twelf.loadFile (getFile' args))
| ("readDecl", args) -> (begin checkEmpty args; serve (Twelf.readDecl ()) end)
| ("decl", args) -> serve (Twelf.decl (getId (tokenize args)))
| ("top", args) -> (begin checkEmpty args; Twelf.top (); serve Twelf.OK end)
| ("Table.top", args) ->
    (begin checkEmpty args; Twelf.Table.top (); serve Twelf.OK end)
| ("version", args) ->
    (begin print (Twelf.version ^ "\n"); serve Twelf.OK end)
| ("help", args) -> (begin print helpString; serve Twelf.OK end)
| (t, args) -> error ((^) "Unrecognized command " quote t) end(* quit, as a concession *)
(* | serve' ("complete-at", args) = error "NYI" *)
(* | serve' ("type-at", args) = error "NYI" *)(*
      serve' ("toc", args) = error "NYI"
    | serve' ("list-program", args) = error "NYI"
    | serve' ("list-signature", args) = error "NYI"
    *)
let rec serveLine () = serve' (readLine ())
let rec serve =
  begin function | Twelf.OK -> (begin issue Twelf.OK; serveLine () end)
  | Twelf.ABORT -> (begin issue Twelf.ABORT; serveLine () end) end
let rec serveTop status =
  begin try serve status
  with
  | Error msg ->
      (begin print (("Server error: " ^ msg) ^ "\n"); serveTop Twelf.ABORT end)
  | exn ->
      (begin print (((^) "Uncaught exception: " exnMessage exn) ^ "\n");
       serveTop Twelf.ABORT end) end
let rec server (name, _) =
  ((begin print (Twelf.version ^ "\n");
    Timing.init ();
    SigINT.interruptLoop (begin function | () -> serveTop Twelf.OK end);
  OS.Process.success end)
(* initialize timers *))(* ignore server name and arguments *)
end 
module Server =
  (Server)(struct
                  module SigINT = SigINT
                  module Timing = Timing
                  module Lexer = Lexer
                  module Twelf = Twelf
                end)