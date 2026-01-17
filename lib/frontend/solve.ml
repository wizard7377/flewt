
module type SOLVE  =
  sig
    module ExtQuery :
    ((EXTQUERY)(* Solve and query declarations, interactive top level *)
    (* Author: Frank Pfenning *)(*! structure IntSyn : INTSYN !*)
    (*! structure Paths : PATHS !*))
    exception AbortQuery of string 
    val solve :
      (ExtQuery.define list * ExtQuery.solve * Paths.location) ->
        (IntSyn.__ConDec * Paths.occConDec option) list
    val query :
      ((int option * int option * ExtQuery.query) * Paths.location) -> unit
    val querytabled :
      ((int option * int option * ExtQuery.query) * Paths.location) ->
        ((unit)(* may raise AbortQuery(msg) *))
    val qLoop :
      unit -> ((bool)(* may raise AbortQuery(msg) *))
    val qLoopT :
      unit -> ((bool)(* true means normal exit *))
  end;;




module Solve(Solve:sig
                     module Global : GLOBAL
                     module Names : NAMES
                     module Parser : PARSER
                     module ReconQuery : RECON_QUERY
                     module Timers : TIMERS
                     module Compile : COMPILE
                     module CPrint : CPRINT
                     module AbsMachine : ABSMACHINE
                     module AbsMachineSbt : ABSMACHINESBT
                     module PtRecon : PTRECON
                     module Tabled : TABLED
                     module Print : PRINT
                     module Msg :
                     ((MSG)(* Front End Interface *)
                     (* Author: Frank Pfenning *)(* Modified: Carsten Schuermann, Jeff Polakow, Roberto Virga *)
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing ReconQuery.IntSyn = IntSyn' !*)
                     (* sharing type ReconQuery.Paths.occConDec = Origins.Paths.occConDec *)
                     (*! structure CompSyn : COMPSYN !*)
                     (*! sharing CompSyn.IntSyn = IntSyn' !*)(*! sharing Compile.IntSyn = IntSyn' !*)
                     (*! sharing Compile.CompSyn = CompSyn !*)(*! sharing CPrint.IntSyn = IntSyn' !*)
                     (*! sharing CPrint.CompSyn = CompSyn !*)(*! structure CSManager : CS_MANAGER !*)
                     (*! sharing CSManager.IntSyn = IntSyn' !*)(*! sharing AbsMachine.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachine.CompSyn = CompSyn !*)
                     (*! sharing AbsMachineSbt.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachineSbt.CompSyn = CompSyn!*)
                     (*! sharing PtRecon.IntSyn = IntSyn' !*)(*! sharing PtRecon.CompSyn = CompSyn !*)
                     (*! structure TableParam : TABLEPARAM !*)(*! sharing Tabled.IntSyn = IntSyn' !*)
                     (*! sharing Tabled.CompSyn = CompSyn !*)(*! structure MemoTable : MEMOTABLE !*)
                     (*! sharing MemoTable.IntSyn = IntSyn' !*)(*! sharing Print.IntSyn = IntSyn' !*))
                   end) : SOLVE =
  struct
    module ExtQuery =
      ((ReconQuery)(*! structure IntSyn = IntSyn' !*))
    module S =
      ((Parser.Stream)(*! structure Paths = ReconQuery.Paths !*))
    let rec evarInstToString
      ((Xs)(* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *))
      = if (!Global.chatter) >= 3 then Print.evarInstToString Xs else ""
    let rec expToString
      ((GU)(* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *))
      = if (!Global.chatter) >= 3 then Print.expToString GU else ""
    exception AbortQuery of
      ((string)(* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *))
      
    type nonrec bound =
      ((int)(* Concrete syntax: 0, 1, 2, ..., * *)(* Bounds SOME(n) for n >= 0, NONE represents positive infinity *))
        option
    let rec exceeds =
      function
      | (SOME ((n)(* exceeds : bound * bound -> bool *)),
         SOME m) -> n >= m
      | (SOME n, NONE) -> false__
      | (NONE, _) -> true__
    let rec boundEq =
      function
      | (SOME ((n)(* boundEq : bound * bound -> bool *)),
         SOME m) -> n = m
      | (NONE, NONE) -> true__
      | _ -> false__
    let rec boundToString =
      function
      | SOME ((n)(* boundToString : bound -> string *)) ->
          Int.toString n
      | NONE -> "*"
    let rec boundMin =
      function
      | (SOME ((n)(* boundMin : bound * bound -> bound *)),
         SOME m) -> SOME (Int.min (n, m))
      | (b, NONE) -> b
      | (NONE, b) -> b
    let rec checkSolutions
      (((expected)(* checkSolutions : bound * bound * int -> unit *)
       (* raises AbortQuery(msg) if the actual solutions do not match *)
       (* the expected number, given the bound on the number of tries *)),
       try__, solutions)
      =
      if boundEq ((boundMin (expected, try__)), (SOME solutions))
      then ()
      else
        raise
          (AbortQuery
             ((^) (((^) (((^) "Query error -- wrong number of solutions: expected "
                            boundToString expected)
                           ^ " in ")
                      boundToString try__)
                     ^ " tries, but found ")
                Int.toString solutions))
    let rec checkStages
      (((try__)(* checkStages : bound * int -> unit *)
       (* raises AbortQuery(msg) if the actual #stages do not match *)
       (* the expected number, given the bound on the number of tries *)),
       stages)
      =
      if boundEq (try__, (SOME stages))
      then ()
      else
        raise
          (AbortQuery
             ((^) (((^) "Query error -- wrong number of stages: "
                      boundToString try__)
                     ^ " tries, but terminated after  ")
                Int.toString stages))
    let rec moreSolutions
      ((())(* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is "q" or "Q"
  *))
      =
      print "More? ";
      (match String.sub ((Compat.inputLine97 TextIO.stdIn), 0) with
       | 'y' -> true__
       | 'Y' -> true__
       | ';' -> true__
       | 'q' -> raise (AbortQuery "Query error -- explicit quit")
       | 'Q' -> raise (AbortQuery "Query error -- explicit quit")
       | _ -> false__)
    exception Done (* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)
    exception Completed (* exception Completed raised by tabled computation when table is saturated *)
    exception Solution of
      ((IntSyn.__Exp)(* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *))
      
    exception SolutionSkel of CompSyn.pskeleton 
    let rec solve'
      (((defines)(* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)),
       solve, Loc (fileName, r))
      =
      let (A, finish) =
        ReconQuery.solveToSolve
          (((defines)(* self timing *)), solve,
            (Paths.Loc (fileName, r))) in
      let ((_)(* echo declaration, according to chatter level *))
        = if (!Global.chatter) >= 3 then Msg.message "%solve " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, A))
               ^ ".\n")
        else () in
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let search () =
        AbsMachine.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            (function | M -> raise (Solution M))) in
      CSManager.reset ();
      (try
         TimeLimit.timeLimit (!Global.timeLimit)
           (Timers.time Timers.solving search) ();
         raise (AbortQuery "No solution to %solve found")
       with
       | Solution (M) ->
           (try
              if (!Global.chatter) >= 3 then Msg.message " OK\n" else ();
              finish M
            with
            | TimeLimit.TimeOut ->
                raise
                  (AbortQuery (("\n----------- TIME OUT ---------------\n")
                     (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)))))
    let rec solveSbt
      (((defines)(* Using substitution tree indexing for clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)),
       solve, Loc (fileName, r))
      =
      let (A, finish) =
        ReconQuery.solveToSolve
          (((defines)(* self timing *)), solve,
            (Paths.Loc (fileName, r))) in
      let ((_)(* echo declaration, according to chatter level *))
        = if (!Global.chatter) >= 3 then Msg.message "%solve " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, A))
               ^ ".\n")
        else () in
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      CSManager.reset ();
      (try
         TimeLimit.timeLimit (!Global.timeLimit)
           (Timers.time Timers.solving AbsMachineSbt.solve)
           ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
             (function | Skel -> raise (SolutionSkel Skel)));
         raise (AbortQuery "No solution to %solve found")
       with
       | SolutionSkel (Skel) ->
           (try
              if (!Global.chatter) >= 2 then Msg.message " OK\n" else ();
              (try
                 Timers.time Timers.ptrecon PtRecon.solve
                   (Skel, (g, IntSyn.id),
                     (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                     (function | (Skel, M) -> raise (Solution M)));
                 raise (AbortQuery "Proof reconstruction for %solve failed")
               with | Solution (M) -> finish M)
            with
            | TimeLimit.TimeOut ->
                raise
                  (AbortQuery (("\n----------- TIME OUT ---------------\n")
                     (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)))))
    let rec solve args =
      match !Compile.optimize with
      | Compile.Indexing ->
          solveSbt ((args)
            (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *))
      | Compile.LinearHeads -> solve' args
      | _ -> solve' args
    let rec query'
      ((((expected)(* %query <expected> <try> A or %query <expected> <try> X : A *)),
        try__, quy),
       Loc (fileName, r))
      =
      let (((A)(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)),
           optName, Xs)
        = ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let ((_)(* times itself *)) =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) (((^) "%query " boundToString expected) ^ " ")
                boundToString try__)
               ^ "\n")
        else () in
      let _ = if (!Global.chatter) >= 4 then Msg.message " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, A))
               ^ ".\n")
        else () in
      let ((g)(* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
        (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *))
        = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let ((solutions)(* solutions = ref <n> counts the number of solutions found *))
        = ref 0 in
      let scInit
        ((M)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
        =
        ((!) ((:=) solutions) solutions) + 1;
        if (!Global.chatter) >= 3
        then
          (Msg.message
             (((^) "---------- Solution " Int.toString (!solutions)) ^
                " ----------\n");
           Msg.message
             ((Timers.time Timers.printing evarInstToString Xs) ^ "\n"))
        else if (!Global.chatter) >= 3 then Msg.message "." else ();
        (match optName with
         | NONE -> ()
         | SOME name ->
             if (!Global.chatter) >= 3
             then
               Msg.message
                 ((Timers.time Timers.printing evarInstToString [(M, name)])
                    ^ "\n")
             else ());
        if (!Global.chatter) >= 3
        then
          (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
           with
           | NONE -> ()
           | SOME str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
        else ();
        if exceeds ((SOME (!solutions)), try__)
        then raise Done
        else ((())
          (* Question: should we collect constraints in M? *)) in
      let search () =
        AbsMachine.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit) in
      if not (boundEq (try__, (SOME 0)))
      then
        (CSManager.reset ();
         (try
            try
              TimeLimit.timeLimit (!Global.timeLimit)
                (Timers.time Timers.solving search) ()
            with | Done -> ()
          with
          | TimeLimit.TimeOut ->
              raise (AbortQuery "\n----------- TIME OUT ---------------\n"));
         CSManager.reset ();
         checkSolutions (expected, try__, (!solutions)))
      else
        if (!Global.chatter) >= 3
        then Msg.message "Skipping query (bound = 0)\n"
        else if (!Global.chatter) >= 4 then Msg.message "skipping" else ();
      if (!Global.chatter) >= 3
      then Msg.message "____________________________________________\n\n"
      else
        if (!Global.chatter) >= 4
        then Msg.message " OK\n"
        else ((())
          (* solve query if bound > 0 *)(* printing is timed into solving! *)
          (* in case Done was raised *)(* check if number of solutions is correct *))
    let rec querySbt
      ((((expected)(* %query <expected> <try> A or %query <expected> <try> X : A *)),
        try__, quy),
       Loc (fileName, r))
      =
      let (((A)(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)),
           optName, Xs)
        = ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let ((_)(* times itself *)) =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) (((^) "%query " boundToString expected) ^ " ")
                boundToString try__)
               ^ "\n")
        else () in
      let _ = if (!Global.chatter) >= 4 then Msg.message " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, A))
               ^ ".\n")
        else () in
      let ((g)(* Problem: we cannot give an answer substitution for the variables
               in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for the
               original variables encountered during parsing.
             *)
        (*
                val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
             *))
        = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let ((solutions)(* solutions = ref <n> counts the number of solutions found *))
        = ref 0 in
      let scInit
        ((M)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
        =
        ((!) ((:=) solutions) solutions) + 1;
        if (!Global.chatter) >= 3
        then
          (Msg.message
             (((^) "---------- Solution " Int.toString (!solutions)) ^
                " ----------\n");
           Msg.message
             ((Timers.time Timers.printing evarInstToString Xs) ^ "\n"))
        else if (!Global.chatter) >= 3 then Msg.message "." else ();
        (match optName with
         | NONE -> ()
         | SOME name ->
             (if (!Global.chatter) > 3
              then
                (Msg.message "\n pskeleton \n";
                 Msg.message ((CompSyn.pskeletonToString M) ^ "\n"))
              else ();
              Timers.time Timers.ptrecon PtRecon.solve
                (M, (g, IntSyn.id),
                  (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                  (function
                   | (pskel, M) ->
                       if (!Global.chatter) >= 3
                       then
                         Msg.message
                           ((Timers.time Timers.printing evarInstToString
                               [(M, name)])
                              ^ "\n")
                       else ()))));
        if (!Global.chatter) >= 3
        then
          (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
           with
           | NONE -> ()
           | SOME str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
        else ();
        if exceeds ((SOME (!solutions)), try__)
        then raise Done
        else ((())
          (* Question: should we collect constraints in M? *)) in
      let search () =
        AbsMachineSbt.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit) in
      if not (boundEq (try__, (SOME 0)))
      then
        (CSManager.reset ();
         (try
            TimeLimit.timeLimit (!Global.timeLimit)
              (Timers.time Timers.solving search) ()
          with
          | Done ->
              (try ()
               with
               | TimeLimit.TimeOut ->
                   raise
                     (AbortQuery "\n----------- TIME OUT ---------------\n")));
         CSManager.reset ();
         checkSolutions (expected, try__, (!solutions)))
      else
        if (!Global.chatter) >= 3
        then Msg.message "Skipping query (bound = 0)\n"
        else if (!Global.chatter) >= 4 then Msg.message "skipping" else ();
      if (!Global.chatter) >= 3
      then Msg.message "____________________________________________\n\n"
      else
        if (!Global.chatter) >= 4
        then Msg.message " OK\n"
        else ((())
          (* solve query if bound > 0 *)(* printing is timed into solving! *)
          (* in case Done was raised *)(* check if number of solutions is correct *))
    let rec query
      ((args)(* %query <expected> <try> A or %query <expected> <try> X : A  *))
      =
      match !Compile.optimize with
      | Compile.Indexing ->
          querySbt ((args)
            (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *))
      | Compile.LinearHeads -> query' args
      | _ -> query' args
    let rec querytabled
      ((((numSol)(* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)),
        try__, quy),
       Loc (fileName, r))
      =
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            ((^) (((^) "%querytabled " boundToString numSol) ^ " ")
               boundToString try__)
        else () in
      let (((A)(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)),
           optName, Xs)
        = ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let ((_)(* times itself *)) =
        if (!Global.chatter) >= 4 then Msg.message " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, A))
               ^ ".\n")
        else () in
      let ((g)(* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
        (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *))
        = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let ((solutions)(* solutions = ref <n> counts the number of solutions found *))
        = ref 0 in
      let status = ref false__ in
      let solExists = ref false__ in
      let ((stages)(* stage = ref <n> counts the number of stages found *))
        = ref 1 in
      let scInit
        ((O)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
        =
        ((!) ((:=) solutions) solutions) + 1;
        solExists := true__;
        if (!Global.chatter) >= 3
        then
          (Msg.message
             (((^) "\n---------- Solutions " Int.toString (!solutions)) ^
                " ----------\n");
           Msg.message
             ((Timers.time Timers.printing evarInstToString Xs) ^ " \n"))
        else if (!Global.chatter) >= 1 then Msg.message "." else ();
        (match optName with
         | NONE -> ()
         | SOME name ->
             (Msg.message ((CompSyn.pskeletonToString O) ^ "\n");
              Timers.time Timers.ptrecon PtRecon.solve
                (O, (g, IntSyn.id),
                  (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                  (function
                   | (O, M) ->
                       if (!Global.chatter) >= 3
                       then
                         Msg.message
                           ((Timers.time Timers.printing evarInstToString
                               [(M, name)])
                              ^ "\n")
                       else ()))));
        if (!Global.chatter) >= 3
        then
          (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
           with
           | NONE -> ()
           | SOME str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
        else ();
        if (!Global.chatter) >= 1
        then Msg.message "More solutions?\n"
        else ();
        (match numSol with
         | NONE -> ((())
             (* Question: should we collect constraints in M? *))
         | SOME n ->
             if (!solutions) = n
             then
               (if (!Global.chatter) >= 1
                then Msg.message "Found enough solutions\n"
                else ();
                raise Done)
             else ()) in
      let loop
        ((())(* loops -- scinit will raise exception Done *))
        =
        if exceeds ((SOME ((!stages) - 1)), try__)
        then
          (if (!Global.chatter) >= 1
           then
             Msg.message
               (("\n ================= " ^ " Number of tries exceeds stages ")
                  ^ " ======================= \n")
           else ();
           status := false__;
           raise Done)
        else ();
        if (!Global.chatter) >= 1
        then
          Msg.message
            (((^) "\n ====================== Stage " Int.toString (!stages))
               ^ " finished =================== \n")
        else ();
        if exceeds ((SOME (!stages)), try__)
        then
          (Msg.message
             (("\n ================= " ^ " Number of tries exceeds stages ")
                ^ " ======================= \n");
           status := false__;
           raise Done)
        else ();
        if Tabled.nextStage ()
        then ((stages := (!stages)) + 1; loop ())
        else status := true__;
        raise ((Done)
          (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)) in
      let _ = Tabled.reset () in
      let _ = Tabled.fillTable () in
      let tabledSearch () =
        Tabled.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit);
        CSManager.reset ();
        loop ();
        checkStages
          (((try__)
            (* in case Done was raised *)(* next stage until table doesn't change *)),
            (!stages)) in
      if not (boundEq (try__, (SOME 0)))
      then
        (try
           CSManager.reset ();
           (try
              TimeLimit.timeLimit (!Global.timeLimit)
                (Timers.time Timers.solving tabledSearch) ()
            with
            | TimeLimit.TimeOut ->
                (Msg.message "\n----------- TIME OUT ---------------\n";
                 raise Done))
         with | Done -> ())
      else
        if (!Global.chatter) >= 3
        then Msg.message "Skipping query (bound = 0)\n"
        else if (!Global.chatter) >= 2 then Msg.message "skipping" else ();
      if (!Global.chatter) >= 3
      then
        (Msg.message "\n____________________________________________\n\n";
         Msg.message
           (((^) ((((^) "number of stages: tried " boundToString try__) ^
                     " \n")
                    ^ "terminated after ")
               Int.toString (!stages))
              ^ " stages \n \n");
         if !solExists
         then ()
         else Msg.message "\nNO solution exists to query \n\n";
         if !status
         then Msg.message "Tabled evaluation COMPLETE \n \n"
         else Msg.message "Tabled evaluation NOT COMPLETE \n \n";
         Msg.message "\n____________________________________________\n\n";
         Msg.message "\n Table Indexing parameters: \n";
         (match !TableParam.strategy with
          | TableParam.Variant ->
              Msg.message "\n       Table Strategy := Variant \n"
          | TableParam.Subsumption ->
              Msg.message "\n       Table Strategy := Subsumption \n");
         if !TableParam.strengthen
         then Msg.message "\n       Strengthening := true \n"
         else Msg.message "\n       Strengthening := false \n";
         Msg.message
           (((^) "\nNumber of table indices : " Int.toString
               (Tabled.tableSize ()))
              ^ "\n");
         Msg.message
           (((^) "Number of suspended goals : " Int.toString
               (Tabled.suspGoalNo ()))
              ^ "\n");
         Msg.message "\n____________________________________________\n\n")
      else if (!Global.chatter) >= 3 then Msg.message " OK\n" else ();
      Tabled.updateGlobalTable
        (((g)(* solve query if bound > 0 *)), (!status))
    let rec qLoop ((())(* Interactive Query Top Level *)) =
      qLoops (CSManager.reset (); Parser.parseTerminalQ ("?- ", "   "))
    let rec qLoops ((s)(* primary, secondary prompt *)) =
      qLoops' (Timers.time Timers.parsing S.expose s)
    let rec qLoops' =
      function
      | S.Empty -> true__
      | Cons (((query)(* normal exit *)), s') ->
          let (A, optName, Xs) =
            ReconQuery.queryToQuery
              (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
          let ((g)(* times itself *)) =
            Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
          let scInit (M) =
            if (!Global.chatter) >= 1
            then
              Msg.message
                ((Timers.time Timers.printing evarInstToString Xs) ^ "\n")
            else ();
            (match optName with
             | NONE -> ()
             | SOME name ->
                 if (!Global.chatter) >= 3
                 then
                   Msg.message
                     ((Timers.time Timers.printing evarInstToString
                         [(M, name)])
                        ^ "\n")
                 else ());
            if (!Global.chatter) >= 3
            then
              (match Timers.time Timers.printing Print.evarCnstrsToStringOpt
                       Xs
               with
               | NONE -> ()
               | SOME str ->
                   Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
            else ();
            if moreSolutions ()
            then ()
            else
              raise ((Done)
                (* Question: should we collect constraints from M *)) in
          let _ =
            if (!Global.chatter) >= 3 then Msg.message "Solving...\n" else () in
          ((try
              Timers.time Timers.solving AbsMachine.solve
                ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                  scInit);
              Msg.message "No more solutions\n"
            with | Done -> ());
           qLoop ((())
             (* scInit is timed into solving! *)(* Ignore s': parse one query at a time *)))
    let rec qLoopT
      ((())(* querytabled interactive top loop *)) =
      qLoopsT (CSManager.reset (); Parser.parseTerminalQ ("?- ", "   "))
    let rec qLoopsT ((s)(* primary, secondary prompt *)) =
      qLoopsT' (Timers.time Timers.parsing S.expose s)
    let rec qLoopsT' =
      function
      | S.Empty -> true__
      | Cons (((query)(* normal exit *)), s') ->
          let solExists = ref false__ in
          let (A, optName, Xs) =
            ReconQuery.queryToQuery
              (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
          let ((g)(* times itself *)) =
            Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
          let _ = Tabled.reset () in
          let scInit (O) =
            if (!Global.chatter) >= 1
            then
              Msg.message
                ((Timers.time Timers.printing evarInstToString Xs) ^ "\n")
            else ();
            (match optName with
             | NONE -> ()
             | SOME name ->
                 if (!Global.chatter) >= 3
                 then
                   Msg.message
                     " Sorry cannot reconstruct pskeleton proof terms yet \n"
                 else ());
            if (!Global.chatter) >= 3
            then
              (match Timers.time Timers.printing Print.evarCnstrsToStringOpt
                       Xs
               with
               | NONE -> ()
               | SOME str ->
                   Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
            else ();
            solExists := true__;
            if moreSolutions ()
            then ()
            else
              raise ((Done)
                (* Question: should we collect constraints from M? *)) in
          let loop
            ((())(* loops -- scinit will raise exception Done *))
            =
            if Tabled.nextStage ()
            then loop ()
            else
              raise ((Completed)
                (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)) in
          let _ =
            if (!Global.chatter) >= 3 then Msg.message "Solving...\n" else () in
          ((try
              Timers.time Timers.solving Tabled.solve
                ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                  scInit);
              (try loop ()
               with
               | Completed ->
                   if !solExists
                   then Msg.message "No more solutions\n"
                   else Msg.message "the query has no solution\n")
            with | Done -> ());
           qLoopT ((())
             (* scInit is timed into solving! *)(* Ignore s': parse one query at a time *)))
  end ;;
