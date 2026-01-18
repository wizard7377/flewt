
(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)
module type SOLVE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Paths : PATHS !*)
    module ExtQuery : EXTQUERY
    exception AbortQuery of string 
    val solve :
      (ExtQuery.define list * ExtQuery.solve * Paths.location) ->
        (IntSyn.__ConDec * Paths.occConDec option) list
    val query :
      ((int option * int option * ExtQuery.query) * Paths.location) -> unit
    (* may raise AbortQuery(msg) *)
    val querytabled :
      ((int option * int option * ExtQuery.query) * Paths.location) -> unit
    (* may raise AbortQuery(msg) *)
    val qLoop : unit -> bool
    (* true means normal exit *)
    val qLoopT : unit -> bool
  end;;




(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow, Roberto Virga *)
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
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing ReconQuery.IntSyn = IntSyn' !*)
                     (* sharing type ReconQuery.Paths.occConDec = Origins.Paths.occConDec *)
                     (*! structure CompSyn : COMPSYN !*)
                     (*! sharing CompSyn.IntSyn = IntSyn' !*)
                     (*! sharing Compile.IntSyn = IntSyn' !*)
                     (*! sharing Compile.CompSyn = CompSyn !*)
                     (*! sharing CPrint.IntSyn = IntSyn' !*)
                     (*! sharing CPrint.CompSyn = CompSyn !*)
                     (*! structure CSManager : CS_MANAGER !*)
                     (*! sharing CSManager.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachine.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachine.CompSyn = CompSyn !*)
                     (*! sharing AbsMachineSbt.IntSyn = IntSyn' !*)
                     (*! sharing AbsMachineSbt.CompSyn = CompSyn!*)
                     (*! sharing PtRecon.IntSyn = IntSyn' !*)
                     (*! sharing PtRecon.CompSyn = CompSyn !*)
                     (*! structure TableParam : TABLEPARAM !*)
                     (*! sharing Tabled.IntSyn = IntSyn' !*)
                     (*! sharing Tabled.CompSyn = CompSyn !*)
                     (*! structure MemoTable : MEMOTABLE !*)
                     (*! sharing MemoTable.IntSyn = IntSyn' !*)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     module Msg : MSG
                   end) : SOLVE =
  struct
    (*! structure IntSyn = IntSyn' !*)
    module ExtQuery = ReconQuery
    (*! structure Paths = ReconQuery.Paths !*)
    module S = Parser.Stream
    (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec evarInstToString (Xs) =
      if (!Global.chatter) >= 3 then Print.evarInstToString Xs else ""
    (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec expToString (GU) =
      if (!Global.chatter) >= 3 then Print.expToString GU else ""
    (* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *)
    exception AbortQuery of string 
    (* Bounds SOME(n) for n >= 0, NONE represents positive infinity *)
    (* Concrete syntax: 0, 1, 2, ..., * *)
    type nonrec bound = int option
    (* exceeds : bound * bound -> bool *)
    let rec exceeds =
      function
      | (SOME n, SOME m) -> n >= m
      | (SOME n, NONE) -> false__
      | (NONE, _) -> true__
    (* boundEq : bound * bound -> bool *)
    let rec boundEq =
      function
      | (SOME n, SOME m) -> n = m
      | (NONE, NONE) -> true__
      | _ -> false__
    (* boundToString : bound -> string *)
    let rec boundToString = function | SOME n -> Int.toString n | NONE -> "*"
    (* boundMin : bound * bound -> bound *)
    let rec boundMin =
      function
      | (SOME n, SOME m) -> SOME (Int.min (n, m))
      | (b, NONE) -> b
      | (NONE, b) -> b
    (* checkSolutions : bound * bound * int -> unit *)
    (* raises AbortQuery(msg) if the actual solutions do not match *)
    (* the expected number, given the bound on the number of tries *)
    let rec checkSolutions (expected, try__, solutions) =
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
    (* checkStages : bound * int -> unit *)
    (* raises AbortQuery(msg) if the actual #stages do not match *)
    (* the expected number, given the bound on the number of tries *)
    let rec checkStages (try__, stages) =
      if boundEq (try__, (SOME stages))
      then ()
      else
        raise
          (AbortQuery
             ((^) (((^) "Query error -- wrong number of stages: "
                      boundToString try__)
                     ^ " tries, but terminated after  ")
                Int.toString stages))
    (* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is "q" or "Q"
  *)
    let rec moreSolutions () =
      print "More? ";
      (match String.sub ((Compat.inputLine97 TextIO.stdIn), 0) with
       | 'y' -> true__
       | 'Y' -> true__
       | ';' -> true__
       | 'q' -> raise (AbortQuery "Query error -- explicit quit")
       | 'Q' -> raise (AbortQuery "Query error -- explicit quit")
       | _ -> false__)
    (* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)
    exception Done 
    (* exception Completed raised by tabled computation when table is saturated *)
    exception Completed 
    (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)
    exception Solution of IntSyn.__Exp 
    exception SolutionSkel of CompSyn.pskeleton 
    (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)
    let rec solve' (defines, solve, Loc (fileName, r)) =
      let (A, finish) =
        ReconQuery.solveToSolve (defines, solve, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 3 then Msg.message "%solve " else () in
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
      let rec search () =
        AbsMachine.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            (function | M -> raise (Solution M))) in
      ((CSManager.reset ();
        (try
           ((TimeLimit.timeLimit (!Global.timeLimit)
               (Timers.time Timers.solving search) ();
             raise (AbortQuery "No solution to %solve found"))
           (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *))
         with
         | Solution (M) ->
             (try
                if (!Global.chatter) >= 3 then Msg.message " OK\n" else ();
                finish M
              with
              | TimeLimit.TimeOut ->
                  raise
                    (AbortQuery "\n----------- TIME OUT ---------------\n"))))
        (* self timing *)(* echo declaration, according to chatter level *))
    (* Using substitution tree indexing for clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)
    let rec solveSbt (defines, solve, Loc (fileName, r)) =
      let (A, finish) =
        ReconQuery.solveToSolve (defines, solve, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 3 then Msg.message "%solve " else () in
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
      ((CSManager.reset ();
        (try
           ((TimeLimit.timeLimit (!Global.timeLimit)
               (Timers.time Timers.solving AbsMachineSbt.solve)
               ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                 (function | Skel -> raise (SolutionSkel Skel)));
             raise (AbortQuery "No solution to %solve found"))
           (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *))
         with
         | SolutionSkel (Skel) ->
             (try
                if (!Global.chatter) >= 2 then Msg.message " OK\n" else ();
                (try
                   Timers.time Timers.ptrecon PtRecon.solve
                     (Skel, (g, IntSyn.id),
                       (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                       (function | (Skel, M) -> raise (Solution M)));
                   raise
                     (AbortQuery "Proof reconstruction for %solve failed")
                 with | Solution (M) -> finish M)
              with
              | TimeLimit.TimeOut ->
                  raise
                    (AbortQuery "\n----------- TIME OUT ---------------\n"))))
        (* self timing *)(* echo declaration, according to chatter level *))
    let rec solve args =
      ((match !Compile.optimize with
        | Compile.Indexing -> solveSbt args
        | Compile.LinearHeads -> solve' args
        | _ -> solve' args)
      (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *))
    (* %query <expected> <try> A or %query <expected> <try> X : A *)
    let rec query' ((expected, try__, quy), Loc (fileName, r)) =
      let (A, optName, Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ =
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
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let solutions = ref 0 in
      let rec scInit (M) =
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
        ((if (!Global.chatter) >= 3
          then
            (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
             with
             | NONE -> ()
             | SOME str ->
                 Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
          else ())
        (* Question: should we collect constraints in M? *));
        if exceeds ((SOME (!solutions)), try__) then raise Done else () in
      let rec search () =
        AbsMachine.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit) in
      ((if not (boundEq (try__, (SOME 0)))
        then
          (((CSManager.reset ();
             (try
                ((try
                    TimeLimit.timeLimit (!Global.timeLimit)
                      (Timers.time Timers.solving search) ()
                  with | Done -> ())
                (* printing is timed into solving! *))
              with
              | TimeLimit.TimeOut ->
                  raise
                    (AbortQuery "\n----------- TIME OUT ---------------\n"));
             CSManager.reset ();
             checkSolutions (expected, try__, (!solutions))))
          (* solve query if bound > 0 *)(* in case Done was raised *)
          (* check if number of solutions is correct *))
        else
          if (!Global.chatter) >= 3
          then Msg.message "Skipping query (bound = 0)\n"
          else if (!Global.chatter) >= 4 then Msg.message "skipping" else ();
        if (!Global.chatter) >= 3
        then Msg.message "____________________________________________\n\n"
        else if (!Global.chatter) >= 4 then Msg.message " OK\n" else ())
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        (* times itself *)(* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
        (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *)
        (* solutions = ref <n> counts the number of solutions found *)
        (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
    (* %query <expected> <try> A or %query <expected> <try> X : A *)
    let rec querySbt ((expected, try__, quy), Loc (fileName, r)) =
      let (A, optName, Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ =
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
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
      let solutions = ref 0 in
      let rec scInit (M) =
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
        ((if (!Global.chatter) >= 3
          then
            (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
             with
             | NONE -> ()
             | SOME str ->
                 Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
          else ())
        (* Question: should we collect constraints in M? *));
        if exceeds ((SOME (!solutions)), try__) then raise Done else () in
      let rec search () =
        AbsMachineSbt.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit) in
      ((if not (boundEq (try__, (SOME 0)))
        then
          (((CSManager.reset ();
             (try
                TimeLimit.timeLimit (!Global.timeLimit)
                  (Timers.time Timers.solving search) ()
              with
              | Done ->
                  (try ()
                   with
                   | TimeLimit.TimeOut ->
                       raise
                         (AbortQuery
                            "\n----------- TIME OUT ---------------\n")));
             CSManager.reset ();
             checkSolutions (expected, try__, (!solutions))))
          (* solve query if bound > 0 *)(* printing is timed into solving! *)
          (* in case Done was raised *)(* check if number of solutions is correct *))
        else
          if (!Global.chatter) >= 3
          then Msg.message "Skipping query (bound = 0)\n"
          else if (!Global.chatter) >= 4 then Msg.message "skipping" else ();
        if (!Global.chatter) >= 3
        then Msg.message "____________________________________________\n\n"
        else if (!Global.chatter) >= 4 then Msg.message " OK\n" else ())
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        (* times itself *)(* Problem: we cannot give an answer substitution for the variables
               in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for the
               original variables encountered during parsing.
             *)
        (*
                val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
             *)
        (* solutions = ref <n> counts the number of solutions found *)
        (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
    (* %query <expected> <try> A or %query <expected> <try> X : A  *)
    let rec query args =
      ((match !Compile.optimize with
        | Compile.Indexing -> querySbt args
        | Compile.LinearHeads -> query' args
        | _ -> query' args)
      (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *))
    (* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)
    let rec querytabled ((numSol, try__, quy), Loc (fileName, r)) =
      let _ =
        if (!Global.chatter) >= 3
        then
          Msg.message
            ((^) (((^) "%querytabled " boundToString numSol) ^ " ")
               boundToString try__)
        else () in
      let (A, optName, Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 4 then Msg.message " " else () in
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
      let solutions = ref 0 in
      let status = ref false__ in
      let solExists = ref false__ in
      let stages = ref 1 in
      let rec scInit (O) =
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
        ((if (!Global.chatter) >= 3
          then
            (match Timers.time Timers.printing Print.evarCnstrsToStringOpt Xs
             with
             | NONE -> ()
             | SOME str ->
                 Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
          else ())
        (* Question: should we collect constraints in M? *));
        if (!Global.chatter) >= 1
        then Msg.message "More solutions?\n"
        else ();
        (match numSol with
         | NONE -> ()
         | SOME n ->
             if (!solutions) = n
             then
               (if (!Global.chatter) >= 1
                then Msg.message "Found enough solutions\n"
                else ();
                raise Done)
             else ()) in
      let rec loop () =
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
        ((if Tabled.nextStage ()
          then ((stages := (!stages)) + 1; loop ())
          else status := true__)
        (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *));
        raise Done in
      let _ = Tabled.reset () in
      let _ = Tabled.fillTable () in
      let rec tabledSearch () =
        ((Tabled.solve
            ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
              scInit);
          CSManager.reset ();
          loop ();
          checkStages (try__, (!stages)))
        (* in case Done was raised *)(* next stage until table doesn't change *)) in
      ((if not (boundEq (try__, (SOME 0)))
        then
          (try
             ((CSManager.reset ();
               (try
                  TimeLimit.timeLimit (!Global.timeLimit)
                    (Timers.time Timers.solving tabledSearch) ()
                with
                | TimeLimit.TimeOut ->
                    (Msg.message "\n----------- TIME OUT ---------------\n";
                     raise Done)))
             (* solve query if bound > 0 *))
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
        Tabled.updateGlobalTable (g, (!status)))
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        (* times itself *)(* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
        (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
        (* solutions = ref <n> counts the number of solutions found *)
        (* stage = ref <n> counts the number of stages found *)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
        (* loops -- scinit will raise exception Done *))
    (* Interactive Query Top Level *)
    let rec qLoop () =
      qLoops (CSManager.reset (); Parser.parseTerminalQ ("?- ", "   "))
    let rec qLoops s = qLoops' (Timers.time Timers.parsing S.expose s)
    let rec qLoops' =
      function
      | S.Empty -> true__
      | Cons (query, s') ->
          let (A, optName, Xs) =
            ReconQuery.queryToQuery
              (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
          let g =
            Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
          let rec scInit (M) =
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
            ((if (!Global.chatter) >= 3
              then
                (match Timers.time Timers.printing
                         Print.evarCnstrsToStringOpt Xs
                 with
                 | NONE -> ()
                 | SOME str ->
                     Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
              else ())
            (* Question: should we collect constraints from M *));
            if moreSolutions () then () else raise Done in
          let _ =
            if (!Global.chatter) >= 3 then Msg.message "Solving...\n" else () in
          ((((try
                ((Timers.time Timers.solving AbsMachine.solve
                    ((g, IntSyn.id),
                      (CompSyn.DProg (IntSyn.Null, IntSyn.Null)), scInit);
                  Msg.message "No more solutions\n")
                (* scInit is timed into solving! *))
              with | Done -> ());
             qLoop ()))
            (* times itself *)(* Ignore s': parse one query at a time *))
      (* normal exit *)
    (* querytabled interactive top loop *)
    let rec qLoopT () =
      qLoopsT (CSManager.reset (); Parser.parseTerminalQ ("?- ", "   "))
    let rec qLoopsT s = qLoopsT' (Timers.time Timers.parsing S.expose s)
    let rec qLoopsT' =
      function
      | S.Empty -> true__
      | Cons (query, s') ->
          let solExists = ref false__ in
          let (A, optName, Xs) =
            ReconQuery.queryToQuery
              (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
          let g =
            Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, A) in
          let _ = Tabled.reset () in
          let rec scInit (O) =
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
            ((if (!Global.chatter) >= 3
              then
                (match Timers.time Timers.printing
                         Print.evarCnstrsToStringOpt Xs
                 with
                 | NONE -> ()
                 | SOME str ->
                     Msg.message (("Remaining constraints:\n" ^ str) ^ "\n"))
              else ())
            (* Question: should we collect constraints from M? *));
            solExists := true__;
            if moreSolutions () then () else raise Done in
          let rec loop () =
            ((if Tabled.nextStage () then loop () else raise Completed)
            (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)) in
          let _ =
            if (!Global.chatter) >= 3 then Msg.message "Solving...\n" else () in
          ((((try
                ((Timers.time Timers.solving Tabled.solve
                    ((g, IntSyn.id),
                      (CompSyn.DProg (IntSyn.Null, IntSyn.Null)), scInit);
                  (try loop ()
                   with
                   | Completed ->
                       if !solExists
                       then Msg.message "No more solutions\n"
                       else Msg.message "the query has no solution\n"))
                (* scInit is timed into solving! *))
              with | Done -> ());
             qLoopT ()))
            (* times itself *)(* loops -- scinit will raise exception Done *)
            (* Ignore s': parse one query at a time *))
      (* normal exit *)
  end ;;
