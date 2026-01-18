
module type TRACE  =
  sig
    (* Program interface *)
    (*! structure IntSyn : INTSYN !*)
    type nonrec goalTag
    val tagGoal : unit -> goalTag
    type __Event =
      | IntroHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | IntroParm of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeParm of (IntSyn.__Head * IntSyn.__Dec) 
      | Resolved of (IntSyn.__Head * IntSyn.__Head) 
      | Subgoal of ((IntSyn.__Head * IntSyn.__Head) * (unit -> int)) 
      | SolveGoal of (goalTag * IntSyn.__Head * IntSyn.__Exp) 
      | SucceedGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | CommitGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | RetryGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | FailGoal of (goalTag * IntSyn.__Head * IntSyn.__Exp) 
      | Unify of ((IntSyn.__Head * IntSyn.__Head) * IntSyn.__Exp *
      IntSyn.__Exp) 
      | FailUnify of ((IntSyn.__Head * IntSyn.__Head) * string) 
    (* failure message *)
    val signal : (IntSyn.dctx * __Event) -> unit
    val init : unit -> unit
    (* initialize trace, break and tag *)
    val tracing : unit -> bool
    (* currently tracing or using breakpoints *)
    (* User interface *)
    type 'a __Spec =
      | None 
      | Some of 'a list 
      | All 
    val trace : string __Spec -> unit
    val break : string __Spec -> unit
    val detail : int ref
    (* 0 = none, 1 = default, 2 = unify *)
    val show : unit -> unit
    (* show trace, break, detail *)
    val reset : unit -> unit
  end;;




module Trace(Trace:sig
                     (*! structure IntSyn' : INTSYN !*)
                     module Names : NAMES
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     module Print : PRINT
                   end) : TRACE =
  struct
    (*! sharing Print.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module I = IntSyn
    module P = Print
    module N = Names
    (* Printing Utilities *)
    let rec headToString =
      function
      | (__g, Const c) -> N.qidToString (N.constQid c)
      | (__g, Def d) -> N.qidToString (N.constQid d)
      | (__g, BVar k) -> N.bvarName (__g, k)
    let rec expToString (GU) = (P.expToString GU) ^ ". "
    let rec decToString (GD) = (P.decToString GD) ^ ". "
    let rec eqnToString (__g, __U1, __U2) =
      ((^) ((P.expToString (__g, __U1)) ^ " = ") P.expToString (__g, __U2)) ^ ". "
    let rec newline () = print "\n"
    let rec printCtx =
      function
      | I.Null -> print "No hypotheses or parameters. "
      | Decl (I.Null, __d) -> print (decToString (I.Null, __d))
      | Decl (__g, __d) -> (printCtx __g; newline (); print (decToString (__g, __d)))
    let rec evarsToString (Xnames) =
      let inst = P.evarInstToString Xnames in
      let constrOpt = P.evarCnstrsToStringOpt Xnames in
      match constrOpt with
      | None -> inst
      | Some constr -> (inst ^ "\nConstraints:\n") ^ constr
    let rec varsToEVarInst =
      function
      | nil -> nil
      | name::names ->
          (match N.getEVarOpt name with
           | None ->
               (print
                  (("Trace warning: ignoring unknown variable " ^ name) ^
                     "\n");
                varsToEVarInst names)
           | Some (x) -> (x, name) :: varsToEVarInst names)
    let rec printVars names = print (evarsToString (varsToEVarInst names))
    let rec printVarstring line =
      printVars (List.tl (String.tokens Char.isSpace line))
    type 'a __Spec =
      | None 
      | Some of 'a list 
      | All 
    let (traceSpec : string __Spec ref) = ref None
    let (breakSpec : string __Spec ref) = ref None
    let rec trace =
      function
      | None -> traceSpec := None
      | Some names -> (:=) traceSpec Some names
      | All -> traceSpec := All
    let rec break =
      function
      | None -> breakSpec := None
      | Some names -> (:=) breakSpec Some names
      | All -> breakSpec := All
    let detail = ref 1
    let rec setDetail =
      function
      | None -> print "Trace warning: detail is not a valid integer\n"
      | Some n ->
          ((if 0 <= n
            then detail := n
            else print "Trace warning: detail must be positive\n")
          (* andalso n <= 2 *))
    let (traceTSpec : I.cid __Spec ref) = ref None
    let (breakTSpec : I.cid __Spec ref) = ref None
    let rec toCids =
      function
      | nil -> nil
      | name::names ->
          (match N.stringToQid name with
           | None ->
               (print
                  (("Trace warning: ignoring malformed qualified identifier "
                      ^ name)
                     ^ "\n");
                toCids names)
           | Some qid ->
               (match N.constLookup qid with
                | None ->
                    (print
                       (((^) "Trace warning: ignoring undeclared constant "
                           N.qidToString qid)
                          ^ "\n");
                     toCids names)
                | Some cid -> cid :: toCids names))
    let rec initTrace =
      function
      | None -> traceTSpec := None
      | Some names -> (:=) traceTSpec Some (toCids names)
      | All -> traceTSpec := All
    let rec initBreak =
      function
      | None -> breakTSpec := None
      | Some names -> (:=) breakTSpec Some (toCids names)
      | All -> breakTSpec := All
    let rec printHelp () =
      print
        "<newline> - continue --- execute with current settings\nn - next --- take a single step\nr - run --- remove all breakpoints and continue\ns - skip --- skip until current subgoals succeeds, is retried, or fails\ns n - skip to n --- skip until goal (n) is considered\nt - trace --- trace all events\nu - untrace --- trace no events\nd n - detail --- set trace detail to n (0, 1, or 2)\nh - hypotheses --- show current hypotheses\ng - goal --- show current goal\ni - instantiation --- show instantiation of variables in current goal\nv X1 ... Xn - variables --- show instantiation of X1 ... Xn\n? for help"
    let (currentGoal : (I.dctx * I.__Exp) ref) = ref (I.Null, (I.Uni I.Type))
    (* dummy initialization *)
    let (currentEVarInst : (I.__Exp * string) list ref) = ref nil
    let rec setEVarInst (__Xs) =
      (:=) currentEVarInst List.map
        (function | x -> (x, (N.evarName (I.Null, x)))) __Xs
    let rec setGoal (__g, __v) =
      currentGoal := (__g, __v);
      setEVarInst (Abstract.collectEVars (__g, (__v, I.id), nil))
    type nonrec goalTag = int option
    let (tag : goalTag ref) = ref None
    let rec tagGoal () =
      match !tag with
      | None -> None
      | Some n -> ((:=) tag Some (n + 1); !tag)
    let (watchForTag : goalTag ref) = ref None
    let rec initTag () =
      watchForTag := None;
      (match ((!traceTSpec), (!breakTSpec)) with
       | (None, None) -> tag := None
       | _ -> (:=) tag Some 0)
    let rec setWatchForTag =
      function
      | None -> (!) ((:=) watchForTag) tag
      | Some n -> (:=) watchForTag Some n
    let rec breakAction (__g) =
      let _ = print " " in
      let line = Compat.inputLine97 TextIO.stdIn in
      match String.sub (line, 0) with
      | '\n' -> ()
      | 'n' -> breakTSpec := All
      | 'r' -> breakTSpec := None
      | 's' ->
          setWatchForTag (Int.fromString (String.extract (line, 1, None)))
      | 't' -> (traceTSpec := All; print "% Now tracing all"; breakAction __g)
      | 'u' ->
          (traceTSpec := None; print "% Now tracing none"; breakAction __g)
      | 'd' ->
          (setDetail (Int.fromString (String.extract (line, 1, None)));
           print ((^) "% Trace detail now " Int.toString (!detail));
           breakAction __g)
      | 'h' -> (printCtx __g; breakAction __g)
      | 'g' -> (print (expToString (!currentGoal)); breakAction __g)
      | 'i' ->
          (print (evarsToString (List.rev (!currentEVarInst))); breakAction __g)
      | 'v' -> (printVarstring line; breakAction __g)
      | '?' -> (printHelp (); breakAction __g)
      | _ -> (print "unrecognized command (? for help)"; breakAction __g)
    let rec init () =
      initTrace (!traceSpec); initBreak (!breakSpec); initTag ()
    type __Event =
      | IntroHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | IntroParm of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeParm of (IntSyn.__Head * IntSyn.__Dec) 
      | Resolved of (IntSyn.__Head * IntSyn.__Head) 
      | Subgoal of ((IntSyn.__Head * IntSyn.__Head) * (unit -> int)) 
      | SolveGoal of (goalTag * IntSyn.__Head * IntSyn.__Exp) 
      | SucceedGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | CommitGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | RetryGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | FailGoal of (goalTag * IntSyn.__Head * IntSyn.__Exp) 
      | Unify of ((IntSyn.__Head * IntSyn.__Head) * IntSyn.__Exp *
      IntSyn.__Exp) 
      | FailUnify of ((IntSyn.__Head * IntSyn.__Head) * string) 
    (* failure message *)
    let rec eventToString =
      function
      | (__g, IntroHyp (_, __d)) ->
          (^) "% Introducing hypothesis\n" decToString (__g, __d)
      | (__g, DischargeHyp (_, Dec (Some x, _))) ->
          "% Discharging hypothesis " ^ x
      | (__g, IntroParm (_, __d)) ->
          (^) "% Introducing parameter\n" decToString (__g, __d)
      | (__g, DischargeParm (_, Dec (Some x, _))) ->
          "% Discharging parameter " ^ x
      | (__g, Resolved (Hc, Ha)) ->
          (^) (((^) "% Resolved with clause " headToString (__g, Hc)) ^ "\n")
            evarsToString (List.rev (!currentEVarInst))
      | (__g, Subgoal ((Hc, Ha), msg)) ->
          (^) (((^) "% Solving subgoal (" Int.toString (msg ())) ^
                 ") of clause ")
            headToString (__g, Hc)
      | (__g, SolveGoal (Some tag, _, __v)) ->
          (^) (((^) "% Goal " Int.toString tag) ^ ":\n") expToString (__g, __v)
      | (__g, SucceedGoal (Some tag, _, __v)) ->
          ((^) "% Goal " Int.toString tag) ^ " succeeded"
      | (__g, CommitGoal (Some tag, _, __v)) ->
          ((^) "% Goal " Int.toString tag) ^ " committed to first solution"
      | (__g, RetryGoal (Some tag, (Hc, Ha), __v)) ->
          (^) (((^) ((((^) "% Backtracking from clause " headToString (__g, Hc))
                        ^ "\n")
                       ^ "% Retrying goal ")
                  Int.toString tag)
                 ^ ":\n")
            expToString (__g, __v)
      | (__g, FailGoal (Some tag, _, __v)) ->
          (^) "% Failed goal " Int.toString tag
      | (__g, Unify ((Hc, Ha), Q, P)) ->
          (^) (((^) "% Trying clause " headToString (__g, Hc)) ^ "\n")
            eqnToString (__g, Q, P)
      | (__g, FailUnify ((Hc, Ha), msg)) ->
          (((^) "% Unification failed with clause " headToString (__g, Hc)) ^
             ":\n")
            ^ msg
    let rec traceEvent (__g, e) = print (eventToString (__g, e))
    let rec monitorHead =
      function
      | (cids, Const c) -> List.exists (function | c' -> c = c') cids
      | (cids, Def d) -> List.exists (function | c' -> d = c') cids
      | (cids, BVar k) -> false__
    let rec monitorHeads (cids, (Hc, Ha)) =
      (monitorHead (cids, Hc)) || (monitorHead (cids, Ha))
    let rec monitorEvent =
      function
      | (cids, IntroHyp (H, _)) -> monitorHead (cids, H)
      | (cids, DischargeHyp (H, _)) -> monitorHead (cids, H)
      | (cids, IntroParm (H, _)) -> monitorHead (cids, H)
      | (cids, DischargeParm (H, _)) -> monitorHead (cids, H)
      | (cids, SolveGoal (_, H, __v)) -> monitorHead (cids, H)
      | (cids, SucceedGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, CommitGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, RetryGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, FailGoal (_, H, _)) -> monitorHead (cids, H)
      | (cids, Resolved (Hc, Ha)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, Subgoal ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, Unify ((Hc, Ha), _, _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, FailUnify ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
    let rec monitorDetail =
      function
      | Unify _ -> (!detail) >= 2
      | FailUnify _ -> (!detail) >= 2
      | _ -> (!detail) >= 1
    (* expensive if tracing Unify! *)
    (* but: maintain only if break or trace is on *)
    (* may not be sufficient for some information *)
    let rec maintain =
      function
      | (__g, SolveGoal (_, _, __v)) -> setGoal (__g, __v)
      | (__g, RetryGoal (_, _, __v)) -> setGoal (__g, __v)
      | (__g, FailGoal (_, _, __v)) -> setGoal (__g, __v)
      | (__g, Unify (_, Q, P)) ->
          setEVarInst
            (Abstract.collectEVars
               (__g, (P, I.id), (Abstract.collectEVars (__g, (Q, I.id), nil))))
      | _ -> ()(* show substitution for variables in clause head if tracing unification *)
    let rec monitorBreak =
      function
      | (None, __g, e) -> false__
      | (Some cids, __g, e) ->
          if monitorEvent (cids, e)
          then (maintain (__g, e); traceEvent (__g, e); breakAction __g; true__)
          else false__
      | (All, __g, e) ->
          (maintain (__g, e); traceEvent (__g, e); breakAction __g; true__)
    let rec monitorTrace =
      function
      | (None, __g, e) -> false__
      | (Some cids, __g, e) ->
          if monitorEvent (cids, e)
          then (maintain (__g, e); traceEvent (__g, e); newline (); true__)
          else false__
      | (All, __g, e) ->
          (maintain (__g, e); traceEvent (__g, e); newline (); true__)
    let rec watchFor e =
      match !watchForTag with
      | None -> false__
      | Some t ->
          (match e with
           | SolveGoal (Some t', _, _) -> t' = t
           | SucceedGoal (Some t', _, _) -> t' = t
           | CommitGoal (Some t', _, _) -> t' = t
           | RetryGoal (Some t', _, _) -> t' = t
           | FailGoal (Some t', _, _) -> t' = t
           | _ -> false__)
    let rec skipping () =
      match !watchForTag with | None -> false__ | Some _ -> true__
    let rec signal (__g, e) =
      ((if monitorDetail e
        then
          (if skipping ()
           then
             (if watchFor e
              then (watchForTag := None; signal (__g, e))
              else (monitorTrace ((!traceTSpec), __g, e); ()))
           else
             ((if monitorBreak ((!breakTSpec), __g, e)
               then ()
               else (monitorTrace ((!traceTSpec), __g, e); ()))
             (* stops, continues after input *)))
        else ())
      (* prints trace, continues *))
    let rec showSpec =
      function
      | (msg, None) -> print (msg ^ " = None\n")
      | (msg, Some names) ->
          (print (msg ^ " = Some [");
           List.app (function | name -> print (" " ^ name)) names;
           print "]\n")
      | (msg, All) -> print (msg ^ " = All\n")
    let rec tracing () =
      match ((!traceSpec), (!breakSpec)) with
      | (None, None) -> false__
      | _ -> true__
    let rec show () =
      showSpec ("trace", (!traceSpec));
      showSpec ("break", (!breakSpec));
      print (((^) "detail = " Int.toString (!detail)) ^ "\n")
    let rec reset () = trace None; break None; detail := 1
  end ;;
