
module type TRACE  =
  sig
    type nonrec goalTag(*! structure IntSyn : INTSYN !*)
    (* Program interface *)
    val tagGoal : unit -> goalTag
    type __Event =
      | IntroHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | IntroParm of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeParm of (IntSyn.__Head * IntSyn.__Dec) 
      | Resolved of (IntSyn.__Head * IntSyn.__Head) 
      | Subgoal of
      ((((IntSyn.__Head)(* resolved with clause c, fam a *))
      * IntSyn.__Head) * (unit -> int)) 
      | SolveGoal of
      (((goalTag)(* clause c, fam a, nth subgoal *)) *
      IntSyn.__Head * IntSyn.__Exp) 
      | SucceedGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | CommitGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | RetryGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | FailGoal of (goalTag * IntSyn.__Head * IntSyn.__Exp) 
      | Unify of ((IntSyn.__Head * IntSyn.__Head) * IntSyn.__Exp *
      IntSyn.__Exp) 
      | FailUnify of
      ((((IntSyn.__Head)(* clause head == goal *)) *
      IntSyn.__Head) * string) 
    val signal :
      (IntSyn.dctx * __Event) ->
        ((unit)(* failure message *))
    val init : unit -> unit
    val tracing :
      unit -> ((bool)(* initialize trace, break and tag *))
    type 'a __Spec =
      | None 
      | Some of
      (('a)(* User interface *)(* currently tracing or using breakpoints *))
      list 
      | All 
    val trace : string __Spec -> unit
    val break : string __Spec -> unit
    val detail : int ref
    val show :
      unit -> ((unit)(* 0 = none, 1 = default, 2 = unify *))
    val reset :
      unit -> ((unit)(* show trace, break, detail *))
  end;;




module Trace(Trace:sig
                     module Names : NAMES
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Print :
                     ((PRINT)(*! structure IntSyn' : INTSYN !*)(*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*))
                   end) : TRACE =
  struct
    module I = IntSyn
    module P = Print
    module N = Names
    let rec headToString =
      function
      | (((g)(*! sharing Print.IntSyn = IntSyn' !*)(*! structure IntSyn = IntSyn' !*)
         (* Printing Utilities *)), Const c) ->
          N.qidToString (N.constQid c)
      | (g, Def d) -> N.qidToString (N.constQid d)
      | (g, BVar k) -> N.bvarName (g, k)
    let rec expToString (GU) = (P.expToString GU) ^ ". "
    let rec decToString (GD) = (P.decToString GD) ^ ". "
    let rec eqnToString (g, u1, u2) =
      ((^) ((P.expToString (g, u1)) ^ " = ") P.expToString (g, u2)) ^ ". "
    let rec newline () = print "\n"
    let rec printCtx =
      function
      | I.Null -> print "No hypotheses or parameters. "
      | Decl (I.Null, D) -> print (decToString (I.Null, D))
      | Decl (g, D) -> (printCtx g; newline (); print (decToString (g, D)))
    let rec evarsToString (Xnames) =
      let inst = P.evarInstToString Xnames in
      let constrOpt = P.evarCnstrsToStringOpt Xnames in
      match constrOpt with
      | NONE -> inst
      | SOME constr -> (inst ^ "\nConstraints:\n") ^ constr
    let rec varsToEVarInst =
      function
      | nil -> nil
      | name::names ->
          (match N.getEVarOpt name with
           | NONE ->
               (print
                  (("Trace warning: ignoring unknown variable " ^ name) ^
                     "\n");
                varsToEVarInst names)
           | SOME (X) -> (::) (X, name) varsToEVarInst names)
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
      | NONE -> print "Trace warning: detail is not a valid integer\n"
      | SOME n ->
          if 0 <= n
          then detail := n
          else
            print (("Trace warning: detail must be positive\n")
              (* andalso n <= 2 *))
    let (traceTSpec : I.cid __Spec ref) = ref None
    let (breakTSpec : I.cid __Spec ref) = ref None
    let rec toCids =
      function
      | nil -> nil
      | name::names ->
          (match N.stringToQid name with
           | NONE ->
               (print
                  (("Trace warning: ignoring malformed qualified identifier "
                      ^ name)
                     ^ "\n");
                toCids names)
           | SOME qid ->
               (match N.constLookup qid with
                | NONE ->
                    (print
                       (((^) "Trace warning: ignoring undeclared constant "
                           N.qidToString qid)
                          ^ "\n");
                     toCids names)
                | SOME cid -> (::) cid toCids names))
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
    let (currentEVarInst :
      (((I.__Exp)(* dummy initialization *)) * string) list
        ref)
      = ref nil
    let rec setEVarInst (Xs) =
      (:=) currentEVarInst List.map
        (function | X -> (X, (N.evarName (I.Null, X)))) Xs
    let rec setGoal (g, V) =
      currentGoal := (g, V);
      setEVarInst (Abstract.collectEVars (g, (V, I.id), nil))
    type nonrec goalTag = int option
    let (tag : goalTag ref) = ref NONE
    let rec tagGoal () =
      match !tag with
      | NONE -> NONE
      | SOME n -> ((:=) tag SOME (n + 1); !tag)
    let (watchForTag : goalTag ref) = ref NONE
    let rec initTag () =
      watchForTag := NONE;
      (match ((!traceTSpec), (!breakTSpec)) with
       | (None, None) -> tag := NONE
       | _ -> (:=) tag SOME 0)
    let rec setWatchForTag =
      function
      | NONE -> (!) ((:=) watchForTag) tag
      | SOME n -> (:=) watchForTag SOME n
    let rec breakAction (g) =
      let _ = print " " in
      let line = Compat.inputLine97 TextIO.stdIn in
      match String.sub (line, 0) with
      | '\n' -> ()
      | 'n' -> breakTSpec := All
      | 'r' -> breakTSpec := None
      | 's' ->
          setWatchForTag (Int.fromString (String.extract (line, 1, NONE)))
      | 't' -> (traceTSpec := All; print "% Now tracing all"; breakAction g)
      | 'u' ->
          (traceTSpec := None; print "% Now tracing none"; breakAction g)
      | 'd' ->
          (setDetail (Int.fromString (String.extract (line, 1, NONE)));
           print ((^) "% Trace detail now " Int.toString (!detail));
           breakAction g)
      | 'h' -> (printCtx g; breakAction g)
      | 'g' -> (print (expToString (!currentGoal)); breakAction g)
      | 'i' ->
          (print (evarsToString (List.rev (!currentEVarInst))); breakAction g)
      | 'v' -> (printVarstring line; breakAction g)
      | '?' -> (printHelp (); breakAction g)
      | _ -> (print "unrecognized command (? for help)"; breakAction g)
    let rec init () =
      initTrace (!traceSpec); initBreak (!breakSpec); initTag ()
    type __Event =
      | IntroHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeHyp of (IntSyn.__Head * IntSyn.__Dec) 
      | IntroParm of (IntSyn.__Head * IntSyn.__Dec) 
      | DischargeParm of (IntSyn.__Head * IntSyn.__Dec) 
      | Resolved of (IntSyn.__Head * IntSyn.__Head) 
      | Subgoal of
      ((((IntSyn.__Head)(* resolved with clause c, fam a *))
      * IntSyn.__Head) * (unit -> int)) 
      | SolveGoal of
      (((goalTag)(* clause c, fam a, nth subgoal *)) *
      IntSyn.__Head * IntSyn.__Exp) 
      | SucceedGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | CommitGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | RetryGoal of (goalTag * (IntSyn.__Head * IntSyn.__Head) *
      IntSyn.__Exp) 
      | FailGoal of (((goalTag)(* clause c failed, fam a *))
      * IntSyn.__Head * IntSyn.__Exp) 
      | Unify of ((IntSyn.__Head * IntSyn.__Head) * IntSyn.__Exp *
      IntSyn.__Exp) 
      | FailUnify of
      ((((IntSyn.__Head)(* clause head == goal *)) *
      IntSyn.__Head) * string) 
    let rec eventToString =
      function
      | (((g)(* failure message *)), IntroHyp (_, D)) ->
          (^) "% Introducing hypothesis\n" decToString (g, D)
      | (g, DischargeHyp (_, Dec (SOME x, _))) ->
          "% Discharging hypothesis " ^ x
      | (g, IntroParm (_, D)) ->
          (^) "% Introducing parameter\n" decToString (g, D)
      | (g, DischargeParm (_, Dec (SOME x, _))) ->
          "% Discharging parameter " ^ x
      | (g, Resolved (Hc, Ha)) ->
          (^) (((^) "% Resolved with clause " headToString (g, Hc)) ^ "\n")
            evarsToString (List.rev (!currentEVarInst))
      | (g, Subgoal ((Hc, Ha), msg)) ->
          (^) (((^) "% Solving subgoal (" Int.toString (msg ())) ^
                 ") of clause ")
            headToString (g, Hc)
      | (g, SolveGoal (SOME tag, _, V)) ->
          (^) (((^) "% Goal " Int.toString tag) ^ ":\n") expToString (g, V)
      | (g, SucceedGoal (SOME tag, _, V)) ->
          ((^) "% Goal " Int.toString tag) ^ " succeeded"
      | (g, CommitGoal (SOME tag, _, V)) ->
          ((^) "% Goal " Int.toString tag) ^ " committed to first solution"
      | (g, RetryGoal (SOME tag, (Hc, Ha), V)) ->
          (^) (((^) ((((^) "% Backtracking from clause " headToString (g, Hc))
                        ^ "\n")
                       ^ "% Retrying goal ")
                  Int.toString tag)
                 ^ ":\n")
            expToString (g, V)
      | (g, FailGoal (SOME tag, _, V)) ->
          (^) "% Failed goal " Int.toString tag
      | (g, Unify ((Hc, Ha), Q, P)) ->
          (^) (((^) "% Trying clause " headToString (g, Hc)) ^ "\n")
            eqnToString (g, Q, P)
      | (g, FailUnify ((Hc, Ha), msg)) ->
          (((^) "% Unification failed with clause " headToString (g, Hc)) ^
             ":\n")
            ^ msg
    let rec traceEvent (g, e) = print (eventToString (g, e))
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
      | (cids, SolveGoal (_, H, V)) -> monitorHead (cids, H)
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
    let rec maintain =
      function
      | (((g)(* expensive if tracing Unify! *)(* but: maintain only if break or trace is on *)
         (* may not be sufficient for some information *)),
         SolveGoal (_, _, V)) -> setGoal (g, V)
      | (g, RetryGoal (_, _, V)) -> setGoal (g, V)
      | (g, FailGoal (_, _, V)) -> setGoal (g, V)
      | (g, Unify (_, Q, P)) ->
          setEVarInst
            (Abstract.collectEVars
               (((g)
                 (* show substitution for variables in clause head if tracing unification *)),
                 (P, I.id), (Abstract.collectEVars (g, (Q, I.id), nil))))
      | _ -> ()
    let rec monitorBreak =
      function
      | (None, g, e) -> false__
      | (Some cids, g, e) ->
          if monitorEvent (cids, e)
          then (maintain (g, e); traceEvent (g, e); breakAction g; true__)
          else false__
      | (All, g, e) ->
          (maintain (g, e); traceEvent (g, e); breakAction g; true__)
    let rec monitorTrace =
      function
      | (None, g, e) -> false__
      | (Some cids, g, e) ->
          if monitorEvent (cids, e)
          then (maintain (g, e); traceEvent (g, e); newline (); true__)
          else false__
      | (All, g, e) ->
          (maintain (g, e); traceEvent (g, e); newline (); true__)
    let rec watchFor e =
      match !watchForTag with
      | NONE -> false__
      | SOME t ->
          (match e with
           | SolveGoal (SOME t', _, _) -> t' = t
           | SucceedGoal (SOME t', _, _) -> t' = t
           | CommitGoal (SOME t', _, _) -> t' = t
           | RetryGoal (SOME t', _, _) -> t' = t
           | FailGoal (SOME t', _, _) -> t' = t
           | _ -> false__)
    let rec skipping () =
      match !watchForTag with | NONE -> false__ | SOME _ -> true__
    let rec signal (g, e) =
      if monitorDetail e
      then
        (if skipping ()
         then
           (if watchFor e
            then (watchForTag := NONE; signal (g, e))
            else (monitorTrace ((!traceTSpec), g, e); ()))
         else
           if monitorBreak ((!breakTSpec), g, e)
           then ()
           else (monitorTrace ((!traceTSpec), g, e); ()))
      else ((())
        (* stops, continues after input *)(* prints trace, continues *))
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
