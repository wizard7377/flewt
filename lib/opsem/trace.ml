
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
      | (((G)(*! sharing Print.IntSyn = IntSyn' !*)(*! structure IntSyn = IntSyn' !*)
         (* Printing Utilities *)), Const c) ->
          N.qidToString (N.constQid c)
      | (G, Def d) -> N.qidToString (N.constQid d)
      | (G, BVar k) -> N.bvarName (G, k)
    let rec expToString (GU) = (P.expToString GU) ^ ". "
    let rec decToString (GD) = (P.decToString GD) ^ ". "
    let rec eqnToString (G, U1, U2) =
      ((^) ((P.expToString (G, U1)) ^ " = ") P.expToString (G, U2)) ^ ". "
    let rec newline () = print "\n"
    let rec printCtx =
      function
      | I.Null -> print "No hypotheses or parameters. "
      | Decl (I.Null, D) -> print (decToString (I.Null, D))
      | Decl (G, D) -> (printCtx G; newline (); print (decToString (G, D)))
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
    let rec setGoal (G, V) =
      currentGoal := (G, V);
      setEVarInst (Abstract.collectEVars (G, (V, I.id), nil))
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
    let rec breakAction (G) =
      let _ = print " " in
      let line = Compat.inputLine97 TextIO.stdIn in
      match String.sub (line, 0) with
      | '\n' -> ()
      | 'n' -> breakTSpec := All
      | 'r' -> breakTSpec := None
      | 's' ->
          setWatchForTag (Int.fromString (String.extract (line, 1, NONE)))
      | 't' -> (traceTSpec := All; print "% Now tracing all"; breakAction G)
      | 'u' ->
          (traceTSpec := None; print "% Now tracing none"; breakAction G)
      | 'd' ->
          (setDetail (Int.fromString (String.extract (line, 1, NONE)));
           print ((^) "% Trace detail now " Int.toString (!detail));
           breakAction G)
      | 'h' -> (printCtx G; breakAction G)
      | 'g' -> (print (expToString (!currentGoal)); breakAction G)
      | 'i' ->
          (print (evarsToString (List.rev (!currentEVarInst))); breakAction G)
      | 'v' -> (printVarstring line; breakAction G)
      | '?' -> (printHelp (); breakAction G)
      | _ -> (print "unrecognized command (? for help)"; breakAction G)
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
      | (((G)(* failure message *)), IntroHyp (_, D)) ->
          (^) "% Introducing hypothesis\n" decToString (G, D)
      | (G, DischargeHyp (_, Dec (SOME x, _))) ->
          "% Discharging hypothesis " ^ x
      | (G, IntroParm (_, D)) ->
          (^) "% Introducing parameter\n" decToString (G, D)
      | (G, DischargeParm (_, Dec (SOME x, _))) ->
          "% Discharging parameter " ^ x
      | (G, Resolved (Hc, Ha)) ->
          (^) (((^) "% Resolved with clause " headToString (G, Hc)) ^ "\n")
            evarsToString (List.rev (!currentEVarInst))
      | (G, Subgoal ((Hc, Ha), msg)) ->
          (^) (((^) "% Solving subgoal (" Int.toString (msg ())) ^
                 ") of clause ")
            headToString (G, Hc)
      | (G, SolveGoal (SOME tag, _, V)) ->
          (^) (((^) "% Goal " Int.toString tag) ^ ":\n") expToString (G, V)
      | (G, SucceedGoal (SOME tag, _, V)) ->
          ((^) "% Goal " Int.toString tag) ^ " succeeded"
      | (G, CommitGoal (SOME tag, _, V)) ->
          ((^) "% Goal " Int.toString tag) ^ " committed to first solution"
      | (G, RetryGoal (SOME tag, (Hc, Ha), V)) ->
          (^) (((^) ((((^) "% Backtracking from clause " headToString (G, Hc))
                        ^ "\n")
                       ^ "% Retrying goal ")
                  Int.toString tag)
                 ^ ":\n")
            expToString (G, V)
      | (G, FailGoal (SOME tag, _, V)) ->
          (^) "% Failed goal " Int.toString tag
      | (G, Unify ((Hc, Ha), Q, P)) ->
          (^) (((^) "% Trying clause " headToString (G, Hc)) ^ "\n")
            eqnToString (G, Q, P)
      | (G, FailUnify ((Hc, Ha), msg)) ->
          (((^) "% Unification failed with clause " headToString (G, Hc)) ^
             ":\n")
            ^ msg
    let rec traceEvent (G, e) = print (eventToString (G, e))
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
      | (((G)(* expensive if tracing Unify! *)(* but: maintain only if break or trace is on *)
         (* may not be sufficient for some information *)),
         SolveGoal (_, _, V)) -> setGoal (G, V)
      | (G, RetryGoal (_, _, V)) -> setGoal (G, V)
      | (G, FailGoal (_, _, V)) -> setGoal (G, V)
      | (G, Unify (_, Q, P)) ->
          setEVarInst
            (Abstract.collectEVars
               (((G)
                 (* show substitution for variables in clause head if tracing unification *)),
                 (P, I.id), (Abstract.collectEVars (G, (Q, I.id), nil))))
      | _ -> ()
    let rec monitorBreak =
      function
      | (None, G, e) -> false__
      | (Some cids, G, e) ->
          if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); breakAction G; true__)
          else false__
      | (All, G, e) ->
          (maintain (G, e); traceEvent (G, e); breakAction G; true__)
    let rec monitorTrace =
      function
      | (None, G, e) -> false__
      | (Some cids, G, e) ->
          if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); newline (); true__)
          else false__
      | (All, G, e) ->
          (maintain (G, e); traceEvent (G, e); newline (); true__)
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
    let rec signal (G, e) =
      if monitorDetail e
      then
        (if skipping ()
         then
           (if watchFor e
            then (watchForTag := NONE; signal (G, e))
            else (monitorTrace ((!traceTSpec), G, e); ()))
         else
           if monitorBreak ((!breakTSpec), G, e)
           then ()
           else (monitorTrace ((!traceTSpec), G, e); ()))
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
