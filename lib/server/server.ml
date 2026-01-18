
module type SERVER  =
  sig val server : (string * string list) -> OS.Process.status end
module Server(Server:sig
                       module SigINT : SIGINT
                       module Timing : TIMING
                       module Lexer : LEXER
                       module Twelf : TWELF
                     end) : SERVER =
  struct
    let (globalConfig : Twelf.Config.config option ref) = ref NONE
    let rec readLine () =
      let rec getLine () =
        try Compat.inputLine97 TextIO.stdIn
        with | SysErr (_, SOME _) -> getLine () in
      let line = getLine () in
      let rec triml ss = Substring.dropl Char.isSpace ss in
      let rec trimr ss = Substring.dropr Char.isSpace ss in
      let line' = triml (trimr (Compat.Substring.full line)) in
      if line = ""
      then ("OS.exit", "")
      else
        if (Substring.size line') = 0
        then readLine ()
        else
          (let (command', args') = Substring.position " " line' in
           ((Substring.string command'), (Substring.string (triml args'))))
    let rec tokenize args = String.tokens Char.isSpace args
    exception Error of string 
    let rec error msg = raise (Error msg)
    let rec quote string = ("`" ^ string) ^ "'"
    let rec issue =
      function
      | Twelf.OK -> print "%% OK %%\n"
      | Twelf.ABORT -> print "%% ABORT %%\n"
    let rec checkEmpty =
      function | "" -> () | args -> error "Extraneous arguments"
    let rec getFile =
      function | ("", default) -> default | (fileName, default) -> fileName
    let rec getFile' =
      function | "" -> error "Missing filename" | fileName -> fileName
    let rec getId =
      function
      | id::nil -> id
      | nil -> error "Missing identifier"
      | ts -> error "Extraneous arguments"
    let rec getIds ids = ids
    let rec getStrategy =
      function
      | "FRS"::nil -> Twelf.Prover.FRS
      | "RFS"::nil -> Twelf.Prover.RFS
      | nil -> error "Missing strategy"
      | t::nil ->
          error ((quote t) ^ " is not a strategy (must be FRS or RFS)")
      | ts -> error "Extraneous arguments"
    let rec strategyToString =
      function | Twelf.Prover.FRS -> "FRS" | Twelf.Prover.RFS -> "RFS"
    let rec getBool =
      function
      | "true"::nil -> true__
      | "false"::nil -> false__
      | nil -> error "Missing boolean value"
      | t::nil -> error ((quote t) ^ " is not a boolean")
      | ts -> error "Extraneous arguments"
    let rec getNat =
      function
      | t::nil ->
          (try Lexer.stringToNat t
           with
           | NotDigit char -> error ((quote t) ^ " is not a natural number"))
      | nil -> error "Missing natural number"
      | ts -> error "Extraneous arguments"
    let rec getLimit =
      function
      | "*"::nil -> NONE
      | t::ts -> SOME (getNat (t :: ts))
      | nil -> error "Missing `*' or natural number"
    let rec limitToString = function | NONE -> "*" | SOME i -> Int.toString i
    let rec getTableStrategy =
      function
      | "Variant"::nil -> Twelf.Table.Variant
      | "Subsumption"::nil -> Twelf.Table.Subsumption
      | nil -> error "Missing tabling strategy"
      | t::nil ->
          error
            ((quote t) ^
               " is not a tabling strategy (must be Variant or Subsumption)")
      | ts -> error "Extraneous arguments"
    let rec tableStrategyToString =
      function
      | Twelf.Table.Variant -> "Variant"
      | Twelf.Table.Subsumption -> "Subsumption"
    let rec getReconTraceMode =
      function
      | "Progressive"::nil -> Twelf.Recon.Progressive
      | "Omniscient"::nil -> Twelf.Recon.Omniscient
      | nil -> error "Missing tracing reconstruction mode"
      | t::nil ->
          error
            ((quote t) ^
               " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)")
      | ts -> error "Extraneous arguments"
    let rec reconTraceModeToString =
      function
      | Twelf.Recon.Progressive -> "Progressive"
      | Twelf.Recon.Omniscient -> "Omniscient"
    let rec getCompileOpt =
      function
      | "No"::nil -> Twelf.Compile.No
      | "LinearHeads"::nil -> Twelf.Compile.LinearHeads
      | "Indexing"::nil -> Twelf.Compile.Indexing
      | nil -> error "Missing tabling strategy"
      | t::nil ->
          error
            ((quote t) ^
               " is not a compile option (must be No, LinearHeads, or Indexing ")
      | ts -> error "Extraneous arguments"
    let rec compOptToString =
      function
      | Twelf.Compile.No -> "No"
      | Twelf.Compile.LinearHeads -> "LinearHeads"
      | Twelf.Compile.Indexing -> "Indexing"
    let rec setParm =
      function
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
      | "Compile.optimize"::ts ->
          (:=) Twelf.Compile.optimize getCompileOpt ts
      | "Recon.trace"::ts -> (:=) Twelf.Recon.trace getBool ts
      | "Recon.traceMode"::ts ->
          (:=) Twelf.Recon.traceMode getReconTraceMode ts
      | "Prover.strategy"::ts -> (:=) Twelf.Prover.strategy getStrategy ts
      | "Prover.maxSplit"::ts -> (:=) Twelf.Prover.maxSplit getNat ts
      | "Prover.maxRecurse"::ts -> (:=) Twelf.Prover.maxRecurse getNat ts
      | "Table.strategy"::ts -> (:=) Twelf.Table.strategy getTableStrategy ts
      | "Table.strengthen"::ts -> (:=) Twelf.Table.strengthen getBool ts
      | t::ts -> error ((^) "Unknown parameter " quote t)
      | nil -> error "Missing parameter"
    let rec getParm =
      function
      | "chatter"::ts -> Int.toString (!Twelf.chatter)
      | "doubleCheck"::ts -> Bool.toString (!Twelf.doubleCheck)
      | "unsafe"::ts -> Bool.toString (!Twelf.unsafe)
      | "autoFreeze"::ts -> Bool.toString (!Twelf.autoFreeze)
      | "Print.implicit"::ts -> Bool.toString (!Twelf.Print.implicit)
      | "Print.depth"::ts -> limitToString (!Twelf.Print.depth)
      | "Print.length"::ts -> limitToString (!Twelf.Print.length)
      | "Print.indent"::ts -> Int.toString (!Twelf.Print.indent)
      | "Print.width"::ts -> Int.toString (!Twelf.Print.width)
      | "Trace.detail"::ts -> Int.toString (!Twelf.Trace.detail)
      | "Compile.optimize"::ts -> compOptToString (!Twelf.Compile.optimize)
      | "Recon.trace"::ts -> Bool.toString (!Twelf.Recon.trace)
      | "Recon.traceMode"::ts ->
          reconTraceModeToString (!Twelf.Recon.traceMode)
      | "Prover.strategy"::ts -> strategyToString (!Twelf.Prover.strategy)
      | "Prover.maxSplit"::ts -> Int.toString (!Twelf.Prover.maxSplit)
      | "Prover.maxRecurse"::ts -> Int.toString (!Twelf.Prover.maxRecurse)
      | "Table.strategy"::ts -> tableStrategyToString (!Twelf.Table.strategy)
      | t::ts -> error ((^) "Unknown parameter " quote t)
      | nil -> error "Missing parameter"
    let helpString =
      "Commands:\n  set <parameter> <value>     - Set <parameter> to <value>\n  get <parameter>             - Print the current value of <parameter>\n  Trace.trace <id1> ... <idn> - Trace given constants\n  Trace.traceAll              - Trace all constants\n  Trace.untrace               - Untrace all constants\n  Trace.break <id1> ... <idn> - Set breakpoint for given constants\n  Trace.breakAll              - Break on all constants\n  Trace.unbreak               - Remove all breakpoints\n  Trace.show                  - Show current trace and breakpoints\n  Trace.reset                 - Reset all tracing and breaking\n  Print.sgn                   - Print current signature\n  Print.prog                  - Print current signature as program\n  Print.subord                - Print current subordination relation\n  Print.domains               - Print registered constraint domains\n  Print.TeX.sgn               - Print signature in TeX format\n  Print.TeX.prog              - Print signature in TeX format as program\n  Timers.show                 - Print and reset timers\n  Timers.reset                - Reset timers\n  Timers.check                - Print, but do not reset timers.\n  OS.chDir <file>             - Change working directory to <file>\n  OS.getDir                   - Print current working directory\n  OS.exit                     - Exit Twelf server\n  quit                        - Quit Twelf server (same as exit)\n  Config.read <file>          - Read current configuration from <file>\n  Config.load                 - Load current configuration\n  Config.append               - Load current configuration without prior reset\n  make <file>                 - Read and load configuration from <file>\n  reset                       - Reset global signature.\n  loadFile <file>             - Load Twelf file <file>\n  decl <id>                   - Show constant declaration for <id>\n  top                         - Enter interactive query loop\n  Table.top                   - Enter interactive loop for tables queries\n  version                     - Print Twelf server's version\n  help                        - Print this help message\n\nParameters:\n  chatter <nat>               - Level of verbosity (0 = none, 3 = default)\n  doubleCheck <bool>          - Perform additional internal type-checking\n  unsafe <bool>               - Allow unsafe operations (%assert)\n  autoFreeze <bool>           - Freeze families involved in meta-theorems\n  Print.implicit <bool>       - Print implicit arguments\n  Print.depth <limit>         - Cut off printing at depth <limit>\n  Print.length <limit>        - Cut off printing at length <limit>\n  Print.indent <nat>          - Indent by <nat> spaces\n  Print.width <nat>           - Line width for formatting\n  Trace.detail <nat>          - Detail of tracing\n  Compile.optimize <bool>     - Optimize during translation to clauses\n  Recon.trace <bool>          - Trace term reconstruction\n  Recon.traceMode <reconTraceMode> - Term reconstruction tracing mode\n  Prover.strategy <strategy>  - Prover strategy\n  Prover.maxSplit <nat>       - Prover splitting depth bound\n  Prover.maxRecurse <nat>     - Prover recursion depth bound\n  Table.strategy <tableStrategy>   - Tabling strategy\n\nServer types:\n  file                        - File name, relative to working directory\n  id                          - A Twelf identifier\n  bool                        - Either `true' or `false'\n  nat                         - A natural number (starting at `0')\n  limit                       - Either `*' (no limit) or a natural number\n  reconTraceMode              - Either `Progressive' or `Omniscient'\n  strategy                    - Either `FRS' or `RFS'\n  tableStrategy               - Either `Variant' or `Subsumption'\n\nSee http://www.cs.cmu.edu/~twelf/guide-1-4/ for more information,\nor type M-x twelf-info (C-c C-h) in Emacs.\n"
    let rec serve' =
      function
      | ("set", args) -> (setParm (tokenize args); serve Twelf.OK)
      | ("get", args) ->
          (print ((getParm (tokenize args)) ^ "\n"); serve Twelf.OK)
      | ("Style.check", args) ->
          (checkEmpty args; StyleCheck.check (); serve Twelf.OK)
      | ("Print.sgn", args) ->
          (checkEmpty args; Twelf.Print.sgn (); serve Twelf.OK)
      | ("Print.prog", args) ->
          (checkEmpty args; Twelf.Print.prog (); serve Twelf.OK)
      | ("Print.subord", args) ->
          (checkEmpty args; Twelf.Print.subord (); serve Twelf.OK)
      | ("Print.domains", args) ->
          (checkEmpty args; Twelf.Print.domains (); serve Twelf.OK)
      | ("Print.TeX.sgn", args) ->
          (checkEmpty args; Twelf.Print.TeX.sgn (); serve Twelf.OK)
      | ("Print.TeX.prog", args) ->
          (checkEmpty args; Twelf.Print.TeX.prog (); serve Twelf.OK)
      | ("Trace.trace", args) ->
          (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
           serve Twelf.OK)
      | ("Trace.traceAll", args) ->
          (checkEmpty args; Twelf.Trace.trace Twelf.Trace.All; serve Twelf.OK)
      | ("Trace.untrace", args) ->
          (checkEmpty args;
           Twelf.Trace.trace Twelf.Trace.None;
           serve Twelf.OK)
      | ("Trace.break", args) ->
          (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
           serve Twelf.OK)
      | ("Trace.breakAll", args) ->
          (checkEmpty args; Twelf.Trace.break Twelf.Trace.All; serve Twelf.OK)
      | ("Trace.unbreak", args) ->
          (checkEmpty args;
           Twelf.Trace.break Twelf.Trace.None;
           serve Twelf.OK)
      | ("Trace.show", args) ->
          (checkEmpty args; Twelf.Trace.show (); serve Twelf.OK)
      | ("Trace.reset", args) ->
          (checkEmpty args; Twelf.Trace.reset (); serve Twelf.OK)
      | ("Timers.show", args) ->
          (checkEmpty args; Timers.show (); serve Twelf.OK)
      | ("Timers.reset", args) ->
          (checkEmpty args; Timers.reset (); serve Twelf.OK)
      | ("Timers.check", args) ->
          (checkEmpty args; Timers.reset (); serve Twelf.OK)
      | ("OS.chDir", args) ->
          (Twelf.OS.chDir (getFile' args); serve Twelf.OK)
      | ("OS.getDir", args) ->
          (checkEmpty args;
           print ((Twelf.OS.getDir ()) ^ "\n");
           serve Twelf.OK)
      | ("OS.exit", args) -> (checkEmpty args; ())
      | ("quit", args) -> ()
      | ("Config.read", args) ->
          let fileName = getFile (args, "sources.cfg") in
          ((:=) globalConfig SOME (Twelf.Config.read fileName);
           serve Twelf.OK)
      | ("Config.load", args) ->
          ((match !globalConfig with
            | NONE ->
                (:=) globalConfig SOME (Twelf.Config.read "sources.cfg")
            | _ -> ());
           serve (Twelf.Config.load (valOf (!globalConfig))))
      | ("Config.append", args) ->
          ((match !globalConfig with
            | NONE ->
                (:=) globalConfig SOME (Twelf.Config.read "sources.cfg")
            | _ -> ());
           serve (Twelf.Config.append (valOf (!globalConfig))))
      | ("make", args) ->
          let fileName = getFile (args, "sources.cfg") in
          ((:=) globalConfig SOME (Twelf.Config.read fileName);
           serve (Twelf.Config.load (valOf (!globalConfig))))
      | ("reset", args) -> (checkEmpty args; Twelf.reset (); serve Twelf.OK)
      | ("loadFile", args) -> serve (Twelf.loadFile (getFile' args))
      | ("readDecl", args) -> (checkEmpty args; serve (Twelf.readDecl ()))
      | ("decl", args) -> serve (Twelf.decl (getId (tokenize args)))
      | ("top", args) -> (checkEmpty args; Twelf.top (); serve Twelf.OK)
      | ("Table.top", args) ->
          (checkEmpty args; Twelf.Table.top (); serve Twelf.OK)
      | ("version", args) -> (print (Twelf.version ^ "\n"); serve Twelf.OK)
      | ("help", args) -> (print helpString; serve Twelf.OK)
      | (t, args) -> error ((^) "Unrecognized command " quote t)
    let rec serveLine () = serve' (readLine ())
    let rec serve =
      function
      | Twelf.OK -> (issue Twelf.OK; serveLine ())
      | Twelf.ABORT -> (issue Twelf.ABORT; serveLine ())
    let rec serveTop status =
      try serve status
      with
      | Error msg ->
          (print (("Server error: " ^ msg) ^ "\n"); serveTop Twelf.ABORT)
      | exn ->
          (print (((^) "Uncaught exception: " exnMessage exn) ^ "\n");
           serveTop Twelf.ABORT)
    let rec server (name, _) =
      print (Twelf.version ^ "\n");
      Timing.init ();
      SigINT.interruptLoop (function | () -> serveTop Twelf.OK);
      OS.Process.success
  end  (* signature SERVER *)
(* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
(* val line = TextIO.inputLine (TextIO.stdIn) *)
(* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)
(* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)
(* exception Error for server errors *)
(* Print the OK or ABORT messages which are parsed by Emacs *)
(* Checking if there are no extraneous arguments *)
(* Command argument types *)
(* File names, given a default *)
(* File names, not defaults *)
(* Identifiers, used as a constant *)
(* Identifiers, used as a trace specification *)
(* Strategies for %prove, %establish *)
(* Booleans *) (* Natural numbers *)
(* Limits ( *, or natural number) *)
(* Tabling strategy *)
(* Tracing mode for term reconstruction *)
(* Compile options *)
(* Setting Twelf parameters *)
(* Getting Twelf parameter values *)
(* extracted from doc/guide/twelf.texi *)
(* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
(*
      serve' ("toc", args) = error "NYI"
    | serve' ("list-program", args) = error "NYI"
    | serve' ("list-signature", args) = error "NYI"
    *)
(* | serve' ("type-at", args) = error "NYI" *)
(* | serve' ("complete-at", args) = error "NYI" *)
(* quit, as a concession *)
(* ignore server name and arguments *)
(* initialize timers *)
(* functor Server *)
module Server =
  (Make_Server)(struct
                  module SigINT = SigINT
                  module Timing = Timing
                  module Lexer = Lexer
                  module Twelf = Twelf
                end);;
