module type SOLVE  =
  sig
    module ExtQuery : EXTQUERY
    exception AbortQuery of string 
    val solve :
      (ExtQuery.define list * ExtQuery.solve * Paths.location) ->
        (IntSyn.conDec_ * Paths.occConDec option) list
    val query :
      ((int option * int option * ExtQuery.query) * Paths.location) -> unit
    val querytabled :
      ((int option * int option * ExtQuery.query) * Paths.location) -> unit
    val qLoop : unit -> bool
    val qLoopT : unit -> bool
  end


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
                     module Msg : MSG
                   end) : SOLVE =
  struct
    module ExtQuery = ReconQuery
    module S = Parser.Stream
    let rec evarInstToString (xs_) =
      if !Global.chatter >= 3 then begin Print.evarInstToString xs_ end
      else begin "" end
  let rec expToString (GU) =
    if !Global.chatter >= 3 then begin Print.expToString GU end
    else begin "" end
exception AbortQuery of string 
type nonrec bound = int option
let rec exceeds =
  begin function
  | (Some n, Some m) -> n >= m
  | (Some n, None) -> false
  | (None, _) -> true end
let rec boundEq =
  begin function
  | (Some n, Some m) -> n = m
  | (None, None) -> true
  | _ -> false end
let rec boundToString =
  begin function | Some n -> Int.toString n | None -> "*" end
let rec boundMin =
  begin function
  | (Some n, Some m) -> Some (Int.min (n, m))
  | (b, None) -> b
  | (None, b) -> b end
let rec checkSolutions (expected, try_, solutions) =
  if boundEq ((boundMin (expected, try_)), (Some solutions))
  then begin () end
  else begin
    raise
      (AbortQuery
         ((^) (((^) (((^) "Query error -- wrong number of solutions: expected "
                        boundToString expected)
                       ^ " in ")
                  boundToString try_)
                 ^ " tries, but found ")
            Int.toString solutions)) end
let rec checkStages (try_, stages) =
  if boundEq (try_, (Some stages)) then begin () end
  else begin
    raise
      (AbortQuery
         ((^) (((^) "Query error -- wrong number of stages: " boundToString
                  try_)
                 ^ " tries, but terminated after  ")
            Int.toString stages)) end
let rec moreSolutions () =
  begin print "More? ";
  (begin match String.sub ((Compat.inputLine97 TextIO.stdIn), 0) with
   | 'y' -> true
   | 'Y' -> true
   | ';' -> true
   | 'q' -> raise (AbortQuery "Query error -- explicit quit")
   | 'Q' -> raise (AbortQuery "Query error -- explicit quit")
   | _ -> false end) end
exception Done 
exception Completed 
exception Solution of IntSyn.exp_ 
exception SolutionSkel of CompSyn.pskeleton 
let rec solve' (defines, solve, Loc (fileName, r)) =
  let (a_, finish) =
    ReconQuery.solveToSolve (defines, solve, (Paths.Loc (fileName, r))) in
  let _ = if !Global.chatter >= 3 then begin Msg.message "%solve " end
    else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, a_))
               ^ ".\n") end
  else begin () end in
let g = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
let rec search () =
  AbsMachine.solve
    ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
      (begin function | m_ -> raise (Solution m_) end)) in
((begin CSManager.reset ();
  (begin try
           ((begin TimeLimit.timeLimit !Global.timeLimit
                     (Timers.time Timers.solving search) ();
             raise (AbortQuery "No solution to %solve found") end)
   (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *))
  with
  | Solution (m_) ->
      (begin try
               begin if !Global.chatter >= 3
                     then begin Msg.message " OK\n" end
               else begin () end;
       finish m_ end
  with
  | TimeLimit.TimeOut ->
      raise (AbortQuery "\n----------- TIME OUT ---------------\n") end) end) end)
(* self timing *)(* echo declaration, according to chatter level *))
let rec solveSbt (defines, solve, Loc (fileName, r)) =
  let (a_, finish) =
    ReconQuery.solveToSolve (defines, solve, (Paths.Loc (fileName, r))) in
  let _ = if !Global.chatter >= 3 then begin Msg.message "%solve " end
    else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, a_))
               ^ ".\n") end
  else begin () end in
let g = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
((begin CSManager.reset ();
  (begin try
           ((begin TimeLimit.timeLimit !Global.timeLimit
                     (Timers.time Timers.solving AbsMachineSbt.solve)
                     ((g, IntSyn.id),
                       (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                       (begin function | Skel -> raise (SolutionSkel Skel) end));
           raise (AbortQuery "No solution to %solve found") end)
  (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *))
  with
  | SolutionSkel (Skel) ->
      (begin try
               begin if !Global.chatter >= 2
                     then begin Msg.message " OK\n" end
               else begin () end;
       (begin try
                begin Timers.time Timers.ptrecon PtRecon.solve
                        (Skel, (g, IntSyn.id),
                          (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                          (begin function | (Skel, m_) -> raise (Solution m_) end));
                raise (AbortQuery "Proof reconstruction for %solve failed") end
      with | Solution (m_) -> finish m_ end) end
with
| TimeLimit.TimeOut ->
    raise (AbortQuery "\n----------- TIME OUT ---------------\n") end) end) end)
(* self timing *)(* echo declaration, according to chatter level *))
let rec solve args =
  ((begin match !Compile.optimize with
    | Compile.Indexing -> solveSbt args
    | Compile.LinearHeads -> solve' args
    | _ -> solve' args end)
  (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *))
let rec query' ((expected, try_, quy), Loc (fileName, r)) =
  let (a_, optName, xs_) =
    ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
  let _ =
    if !Global.chatter >= 3
    then
      begin Msg.message
              (((^) (((^) "%query " boundToString expected) ^ " ")
                  boundToString try_)
                 ^ "\n") end
    else begin () end in
let _ = if !Global.chatter >= 4 then begin Msg.message " " end
  else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, a_))
               ^ ".\n") end
  else begin () end in
let g = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
let solutions = ref 0 in
let rec scInit (m_) =
begin ((!) ((:=) solutions) solutions) + 1;
if !Global.chatter >= 3
then
  begin (begin Msg.message
                 (((^) "---------- Solution " Int.toString !solutions) ^
                    " ----------\n");
         Msg.message
           ((Timers.time Timers.printing evarInstToString xs_) ^ "\n") end) end
else begin if !Global.chatter >= 3 then begin Msg.message "." end
  else begin () end end;
(begin match optName with
 | None -> ()
 | Some name ->
     if !Global.chatter >= 3
     then
       begin Msg.message
               ((Timers.time Timers.printing evarInstToString [(m_, name)]) ^
                  "\n") end
     else begin () end end);
((if !Global.chatter >= 3
  then
    begin (begin match Timers.time Timers.printing
                         Print.evarCnstrsToStringOpt xs_
                 with
           | None -> ()
           | Some str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n") end) end
else begin () end)
(* Question: should we collect constraints in M? *));
if exceeds ((Some !solutions), try_) then begin raise Done end
else begin () end end in
let rec search () =
AbsMachine.solve
  ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)), scInit) in
((begin if not (boundEq (try_, (Some 0)))
      then
        begin (((begin CSManager.reset ();
                 (begin try
                          ((begin try
                                    TimeLimit.timeLimit !Global.timeLimit
                                      (Timers.time Timers.solving search) ()
                            with | Done -> () end)
                  (* printing is timed into solving! *))
                 with
                 | TimeLimit.TimeOut ->
                     raise
                       (AbortQuery "\n----------- TIME OUT ---------------\n") end);
      CSManager.reset ();
      checkSolutions (expected, try_, !solutions) end))
(* solve query if bound > 0 *)(* in case Done was raised *)
(* check if number of solutions is correct *)) end
else begin
  if !Global.chatter >= 3
  then begin Msg.message "Skipping query (bound = 0)\n" end
  else begin if !Global.chatter >= 4 then begin Msg.message "skipping" end
    else begin () end end end;
if !Global.chatter >= 3
then begin Msg.message "____________________________________________\n\n" end
else begin if !Global.chatter >= 4 then begin Msg.message " OK\n" end
  else begin () end end end)
(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
(* times itself *)(* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
(* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *)
(* solutions = ref <n> counts the number of solutions found *)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
let rec querySbt ((expected, try_, quy), Loc (fileName, r)) =
  let (a_, optName, xs_) =
    ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
  let _ =
    if !Global.chatter >= 3
    then
      begin Msg.message
              (((^) (((^) "%query " boundToString expected) ^ " ")
                  boundToString try_)
                 ^ "\n") end
    else begin () end in
let _ = if !Global.chatter >= 4 then begin Msg.message " " end
  else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, a_))
               ^ ".\n") end
  else begin () end in
let g = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
let solutions = ref 0 in
let rec scInit (m_) =
begin ((!) ((:=) solutions) solutions) + 1;
if !Global.chatter >= 3
then
  begin (begin Msg.message
                 (((^) "---------- Solution " Int.toString !solutions) ^
                    " ----------\n");
         Msg.message
           ((Timers.time Timers.printing evarInstToString xs_) ^ "\n") end) end
else begin if !Global.chatter >= 3 then begin Msg.message "." end
  else begin () end end;
(begin match optName with
 | None -> ()
 | Some name ->
     (begin if !Global.chatter > 3
            then
              begin (begin Msg.message "\n pskeleton \n";
                     Msg.message ((CompSyn.pskeletonToString m_) ^ "\n") end) end
     else begin () end;
Timers.time Timers.ptrecon PtRecon.solve
  (m_, (g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
    (begin function
     | (pskel, m_) ->
         if !Global.chatter >= 3
         then
           begin Msg.message
                   ((Timers.time Timers.printing evarInstToString
                       [(m_, name)])
                      ^ "\n") end
         else begin () end end)) end) end);
((if !Global.chatter >= 3
  then
    begin (begin match Timers.time Timers.printing
                         Print.evarCnstrsToStringOpt xs_
                 with
           | None -> ()
           | Some str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n") end) end
else begin () end)
(* Question: should we collect constraints in M? *));
if exceeds ((Some !solutions), try_) then begin raise Done end
else begin () end end in
let rec search () =
AbsMachineSbt.solve
  ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)), scInit) in
((begin if not (boundEq (try_, (Some 0)))
      then
        begin (((begin CSManager.reset ();
                 (begin try
                          TimeLimit.timeLimit !Global.timeLimit
                            (Timers.time Timers.solving search) ()
                  with
                  | Done ->
                      (begin try ()
                       with
                       | TimeLimit.TimeOut ->
                           raise
                             (AbortQuery
                                "\n----------- TIME OUT ---------------\n") end) end);
      CSManager.reset ();
      checkSolutions (expected, try_, !solutions) end))
(* solve query if bound > 0 *)(* printing is timed into solving! *)
(* in case Done was raised *)(* check if number of solutions is correct *)) end
else begin
  if !Global.chatter >= 3
  then begin Msg.message "Skipping query (bound = 0)\n" end
  else begin if !Global.chatter >= 4 then begin Msg.message "skipping" end
    else begin () end end end;
if !Global.chatter >= 3
then begin Msg.message "____________________________________________\n\n" end
else begin if !Global.chatter >= 4 then begin Msg.message " OK\n" end
  else begin () end end end)
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
(* solutions = ref <n> counts the number of solutions found *)(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *))
let rec query args =
  ((begin match !Compile.optimize with
    | Compile.Indexing -> querySbt args
    | Compile.LinearHeads -> query' args
    | _ -> query' args end)
  (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *))
let rec querytabled ((numSol, try_, quy), Loc (fileName, r)) =
  let _ =
    if !Global.chatter >= 3
    then
      begin Msg.message
              ((^) (((^) "%querytabled " boundToString numSol) ^ " ")
                 boundToString try_) end
    else begin () end in
let (a_, optName, xs_) =
  ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
let _ = if !Global.chatter >= 4 then begin Msg.message " " end
  else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin Msg.message
            (((^) "\n" (Timers.time Timers.printing expToString)
                (IntSyn.Null, a_))
               ^ ".\n") end
  else begin () end in
let g = Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
let solutions = ref 0 in
let status = ref false in
let solExists = ref false in
let stages = ref 1 in
let rec scInit (o_) =
begin ((!) ((:=) solutions) solutions) + 1;
solExists := true;
if !Global.chatter >= 3
then
  begin (begin Msg.message
                 (((^) "\n---------- Solutions " Int.toString !solutions) ^
                    " ----------\n");
         Msg.message
           ((Timers.time Timers.printing evarInstToString xs_) ^ " \n") end) end
else begin if !Global.chatter >= 1 then begin Msg.message "." end
  else begin () end end;
(begin match optName with
 | None -> ()
 | Some name ->
     (begin Msg.message ((CompSyn.pskeletonToString o_) ^ "\n");
      Timers.time Timers.ptrecon PtRecon.solve
        (o_, (g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
          (begin function
           | (o_, m_) ->
               if !Global.chatter >= 3
               then
                 begin Msg.message
                         ((Timers.time Timers.printing evarInstToString
                             [(m_, name)])
                            ^ "\n") end
               else begin () end end)) end) end);
((if !Global.chatter >= 3
  then
    begin (begin match Timers.time Timers.printing
                         Print.evarCnstrsToStringOpt xs_
                 with
           | None -> ()
           | Some str ->
               Msg.message (("Remaining constraints:\n" ^ str) ^ "\n") end) end
else begin () end)
(* Question: should we collect constraints in M? *));
if !Global.chatter >= 1 then begin Msg.message "More solutions?\n" end
else begin () end;
(begin match numSol with
 | None -> ()
 | Some n ->
     if !solutions = n
     then
       begin (begin if !Global.chatter >= 1
                    then begin Msg.message "Found enough solutions\n" end
              else begin () end;
     raise Done end) end else begin () end end) end in
let rec loop () =
begin if exceeds ((Some (!stages - 1)), try_)
      then
        begin (begin if !Global.chatter >= 1
                     then
                       begin Msg.message
                               (("\n ================= " ^
                                   " Number of tries exceeds stages ")
                                  ^ " ======================= \n") end
               else begin () end;
      status := false;
      raise Done end) end else begin () end;
if !Global.chatter >= 1
then
  begin Msg.message
          (((^) "\n ====================== Stage " Int.toString !stages) ^
             " finished =================== \n") end else begin () end;
if exceeds ((Some !stages), try_)
then
  begin (begin Msg.message
                 (("\n ================= " ^
                     " Number of tries exceeds stages ")
                    ^ " ======================= \n");
         status := false;
         raise Done end) end else begin () end;
((if Tabled.nextStage ()
  then begin (begin (stages := !stages) + 1; loop () end) end
else begin status := true end)
(* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *));
raise Done end in
let _ = Tabled.reset () in
let _ = Tabled.fillTable () in
let rec tabledSearch () =
((begin Tabled.solve
          ((g, IntSyn.id), (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
            scInit);
  CSManager.reset ();
  loop ();
  checkStages (try_, !stages) end)
(* in case Done was raised *)(* next stage until table doesn't change *)) in
((begin if not (boundEq (try_, (Some 0)))
      then
        begin (begin try
                       ((begin CSManager.reset ();
                         (begin try
                                  TimeLimit.timeLimit !Global.timeLimit
                                    (Timers.time Timers.solving tabledSearch)
                                    ()
                          with
                          | TimeLimit.TimeOut ->
                              (begin Msg.message
                                       "\n----------- TIME OUT ---------------\n";
                               raise Done end) end) end)
      (* solve query if bound > 0 *))
with | Done -> () end) end
else begin
  if !Global.chatter >= 3
  then begin Msg.message "Skipping query (bound = 0)\n" end
  else begin if !Global.chatter >= 2 then begin Msg.message "skipping" end
    else begin () end end end;
if !Global.chatter >= 3
then
  begin (begin Msg.message
                 "\n____________________________________________\n\n";
         Msg.message
           (((^) ((((^) "number of stages: tried " boundToString try_) ^
                     " \n")
                    ^ "terminated after ")
               Int.toString !stages)
              ^ " stages \n \n");
         if !solExists then begin () end
         else begin Msg.message "\nNO solution exists to query \n\n" end;
if !status then begin Msg.message "Tabled evaluation COMPLETE \n \n" end
else begin Msg.message "Tabled evaluation NOT COMPLETE \n \n" end;
Msg.message "\n____________________________________________\n\n";
Msg.message "\n Table Indexing parameters: \n";
(begin match !TableParam.strategy with
 | TableParam.Variant -> Msg.message "\n       Table Strategy := Variant \n"
 | TableParam.Subsumption ->
     Msg.message "\n       Table Strategy := Subsumption \n" end);
if !TableParam.strengthen
then begin Msg.message "\n       Strengthening := true \n" end
else begin Msg.message "\n       Strengthening := false \n" end;
Msg.message
  (((^) "\nNumber of table indices : " Int.toString (Tabled.tableSize ())) ^
     "\n");
Msg.message
  (((^) "Number of suspended goals : " Int.toString (Tabled.suspGoalNo ())) ^
     "\n");
Msg.message "\n____________________________________________\n\n" end) end
else begin if !Global.chatter >= 3 then begin Msg.message " OK\n" end
  else begin () end end; Tabled.updateGlobalTable (g, !status) end)
(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
(* times itself *)(* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
(* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
(* solutions = ref <n> counts the number of solutions found *)(* stage = ref <n> counts the number of stages found *)
(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
(* loops -- scinit will raise exception Done *))
let rec qLoop () =
  qLoops (begin CSManager.reset (); Parser.parseTerminalQ ("?- ", "   ") end)
let rec qLoops s = qLoops' (Timers.time Timers.parsing S.expose s)
let rec qLoops' =
  begin function
  | S.Empty -> true
  | Cons (query, s') ->
      let (a_, optName, xs_) =
        ReconQuery.queryToQuery
          (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
      let rec scInit (m_) =
        begin if !Global.chatter >= 1
              then
                begin Msg.message
                        ((Timers.time Timers.printing evarInstToString xs_) ^
                           "\n") end
        else begin () end;
        (begin match optName with
         | None -> ()
         | Some name ->
             if !Global.chatter >= 3
             then
               begin Msg.message
                       ((Timers.time Timers.printing evarInstToString
                           [(m_, name)])
                          ^ "\n") end
             else begin () end end);
      ((if !Global.chatter >= 3
        then
          begin (begin match Timers.time Timers.printing
                               Print.evarCnstrsToStringOpt xs_
                       with
                 | None -> ()
                 | Some str ->
                     Msg.message (("Remaining constraints:\n" ^ str) ^ "\n") end) end
  else begin () end)
  (* Question: should we collect constraints from M *));
  if moreSolutions () then begin () end else begin raise Done end end in
let _ = if !Global.chatter >= 3 then begin Msg.message "Solving...\n" end
else begin () end in
(((begin (begin try
                ((begin Timers.time Timers.solving AbsMachine.solve
                          ((g, IntSyn.id),
                            (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                            scInit);
                  Msg.message "No more solutions\n" end)
        (* scInit is timed into solving! *))
 with | Done -> () end); qLoop () end))
(* times itself *)(* Ignore s': parse one query at a time *)) end
(* normal exit *)
let rec qLoopT () =
  qLoopsT (begin CSManager.reset (); Parser.parseTerminalQ ("?- ", "   ") end)
let rec qLoopsT s = qLoopsT' (Timers.time Timers.parsing S.expose s)
let rec qLoopsT' =
  begin function
  | S.Empty -> true
  | Cons (query, s') ->
      let solExists = ref false in
      let (a_, optName, xs_) =
        ReconQuery.queryToQuery
          (query, (Paths.Loc ("stdIn", (Paths.Reg (0, 0))))) in
      let g =
        Timers.time Timers.compiling Compile.compileGoal (IntSyn.Null, a_) in
      let _ = Tabled.reset () in
      let rec scInit (o_) =
        begin if !Global.chatter >= 1
              then
                begin Msg.message
                        ((Timers.time Timers.printing evarInstToString xs_) ^
                           "\n") end
        else begin () end;
        (begin match optName with
         | None -> ()
         | Some name ->
             if !Global.chatter >= 3
             then
               begin Msg.message
                       " Sorry cannot reconstruct pskeleton proof terms yet \n" end
             else begin () end end);
        ((if !Global.chatter >= 3
          then
            begin (begin match Timers.time Timers.printing
                                 Print.evarCnstrsToStringOpt xs_
                         with
                   | None -> ()
                   | Some str ->
                       Msg.message
                         (("Remaining constraints:\n" ^ str) ^ "\n") end) end
        else begin () end)
  (* Question: should we collect constraints from M? *));
  solExists := true;
  if moreSolutions () then begin () end
  else begin raise Done end end in
let rec loop () = ((if Tabled.nextStage () then begin loop () end
else begin raise Completed end)
(* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)) in
let _ = if !Global.chatter >= 3 then begin Msg.message "Solving...\n" end
else begin () end in
(((begin (begin try
                ((begin Timers.time Timers.solving Tabled.solve
                          ((g, IntSyn.id),
                            (CompSyn.DProg (IntSyn.Null, IntSyn.Null)),
                            scInit);
                  (begin try loop ()
                   with
                   | Completed ->
                       if !solExists
                       then begin Msg.message "No more solutions\n" end
                       else begin Msg.message "the query has no solution\n" end end) end)
(* scInit is timed into solving! *)) with | Done -> () end);
qLoopT () end))
(* times itself *)(* loops -- scinit will raise exception Done *)
(* Ignore s': parse one query at a time *)) end(* normal exit *)
end
