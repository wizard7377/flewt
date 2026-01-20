
module type TRACE  =
  sig
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
    val signal : IntSyn.dctx -> __Event -> unit
    val init : unit -> unit
    val tracing : unit -> bool
    type 'a __Spec =
      | None 
      | Some of 'a list 
      | All 
    val trace : string __Spec -> unit
    val break : string __Spec -> unit
    val detail : int ref
    val show : unit -> unit
    val reset : unit -> unit
  end;;




module Trace(Trace:sig
                     module Names : NAMES
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Print : PRINT
                   end) : TRACE =
  struct
    module I = IntSyn
    module P = Print
    module N = Names
    let rec headToString __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Const c) -> N.qidToString (N.constQid c)
      | (__G, Def d) -> N.qidToString (N.constQid d)
      | (__G, BVar k) -> N.bvarName (__G, k)
    let rec expToString (GU) = (P.expToString GU) ^ ". "
    let rec decToString (GD) = (P.decToString GD) ^ ". "
    let rec eqnToString (__G) (__U1) (__U2) =
      ((^) ((P.expToString (__G, __U1)) ^ " = ") P.expToString (__G, __U2)) ^
        ". "
    let rec newline () = print "\n"
    let rec printCtx =
      function
      | I.Null -> print "No hypotheses or parameters. "
      | Decl (I.Null, __D) -> print (decToString (I.Null, __D))
      | Decl (__G, __D) ->
          (printCtx __G; newline (); print (decToString (__G, __D)))
    let rec evarsToString (Xnames) =
      let inst = P.evarInstToString Xnames in
      let constrOpt = P.evarCnstrsToStringOpt Xnames in
      match constrOpt with
      | NONE -> inst
      | Some constr -> (inst ^ "\nConstraints:\n") ^ constr
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
           | Some (__X) -> (::) (__X, name) varsToEVarInst names)
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
           | NONE ->
               (print
                  (("Trace warning: ignoring malformed qualified identifier "
                      ^ name)
                     ^ "\n");
                toCids names)
           | Some qid ->
               (match N.constLookup qid with
                | NONE ->
                    (print
                       (((^) "Trace warning: ignoring undeclared constant "
                           N.qidToString qid)
                          ^ "\n");
                     toCids names)
                | Some cid -> (::) cid toCids names))
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
    let (currentEVarInst : (I.__Exp * string) list ref) = ref nil
    let rec setEVarInst (__Xs) =
      (:=) currentEVarInst List.map
        (fun (__X) -> (__X, (N.evarName (I.Null, __X)))) __Xs
    let rec setGoal (__G) (__V) =
      currentGoal := (__G, __V);
      setEVarInst (Abstract.collectEVars (__G, (__V, I.id), nil))
    type nonrec goalTag = int option
    let (tag : goalTag ref) = ref NONE
    let rec tagGoal () =
      match !tag with
      | NONE -> NONE
      | Some n -> ((:=) tag Some (n + 1); !tag)
    let (watchForTag : goalTag ref) = ref NONE
    let rec initTag () =
      watchForTag := NONE;
      (match ((!traceTSpec), (!breakTSpec)) with
       | (None, None) -> tag := NONE
       | _ -> (:=) tag Some 0)
    let rec setWatchForTag =
      function
      | NONE -> (!) ((:=) watchForTag) tag
      | Some n -> (:=) watchForTag Some n
    let rec breakAction (__G) =
      let _ = print " " in
      let line = Compat.inputLine97 TextIO.stdIn in
      match String.sub (line, 0) with
      | '\n' -> ()
      | 'n' -> breakTSpec := All
      | 'r' -> breakTSpec := None
      | 's' ->
          setWatchForTag (Int.fromString (String.extract (line, 1, NONE)))
      | 't' ->
          (traceTSpec := All; print "% Now tracing all"; breakAction __G)
      | 'u' ->
          (traceTSpec := None; print "% Now tracing none"; breakAction __G)
      | 'd' ->
          (setDetail (Int.fromString (String.extract (line, 1, NONE)));
           print ((^) "% Trace detail now " Int.toString (!detail));
           breakAction __G)
      | 'h' -> (printCtx __G; breakAction __G)
      | 'g' -> (print (expToString (!currentGoal)); breakAction __G)
      | 'i' ->
          (print (evarsToString (List.rev (!currentEVarInst)));
           breakAction __G)
      | 'v' -> (printVarstring line; breakAction __G)
      | '?' -> (printHelp (); breakAction __G)
      | _ -> (print "unrecognized command (? for help)"; breakAction __G)
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
    let rec eventToString __2__ __3__ =
      match (__2__, __3__) with
      | (__G, IntroHyp (_, __D)) ->
          (^) "% Introducing hypothesis\n" decToString (__G, __D)
      | (__G, DischargeHyp (_, Dec (Some x, _))) ->
          "% Discharging hypothesis " ^ x
      | (__G, IntroParm (_, __D)) ->
          (^) "% Introducing parameter\n" decToString (__G, __D)
      | (__G, DischargeParm (_, Dec (Some x, _))) ->
          "% Discharging parameter " ^ x
      | (__G, Resolved (Hc, Ha)) ->
          (^) (((^) "% Resolved with clause " headToString (__G, Hc)) ^ "\n")
            evarsToString (List.rev (!currentEVarInst))
      | (__G, Subgoal ((Hc, Ha), msg)) ->
          (^) (((^) "% Solving subgoal (" Int.toString (msg ())) ^
                 ") of clause ")
            headToString (__G, Hc)
      | (__G, SolveGoal (Some tag, _, __V)) ->
          (^) (((^) "% Goal " Int.toString tag) ^ ":\n") expToString
            (__G, __V)
      | (__G, SucceedGoal (Some tag, _, __V)) ->
          ((^) "% Goal " Int.toString tag) ^ " succeeded"
      | (__G, CommitGoal (Some tag, _, __V)) ->
          ((^) "% Goal " Int.toString tag) ^ " committed to first solution"
      | (__G, RetryGoal (Some tag, (Hc, Ha), __V)) ->
          (^) (((^) ((((^) "% Backtracking from clause " headToString
                         (__G, Hc))
                        ^ "\n")
                       ^ "% Retrying goal ")
                  Int.toString tag)
                 ^ ":\n")
            expToString (__G, __V)
      | (__G, FailGoal (Some tag, _, __V)) ->
          (^) "% Failed goal " Int.toString tag
      | (__G, Unify ((Hc, Ha), __Q, __P)) ->
          (^) (((^) "% Trying clause " headToString (__G, Hc)) ^ "\n")
            eqnToString (__G, __Q, __P)
      | (__G, FailUnify ((Hc, Ha), msg)) ->
          (((^) "% Unification failed with clause " headToString (__G, Hc)) ^
             ":\n")
            ^ msg
    let rec traceEvent (__G) e = print (eventToString (__G, e))
    let rec monitorHead __4__ __5__ =
      match (__4__, __5__) with
      | (cids, Const c) -> List.exists (fun c' -> c = c') cids
      | (cids, Def d) -> List.exists (fun c' -> d = c') cids
      | (cids, BVar k) -> false__
    let rec monitorHeads cids (Hc, Ha) =
      (monitorHead (cids, Hc)) || (monitorHead (cids, Ha))
    let rec monitorEvent __6__ __7__ =
      match (__6__, __7__) with
      | (cids, IntroHyp (__H, _)) -> monitorHead (cids, __H)
      | (cids, DischargeHyp (__H, _)) -> monitorHead (cids, __H)
      | (cids, IntroParm (__H, _)) -> monitorHead (cids, __H)
      | (cids, DischargeParm (__H, _)) -> monitorHead (cids, __H)
      | (cids, SolveGoal (_, __H, __V)) -> monitorHead (cids, __H)
      | (cids, SucceedGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, CommitGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, RetryGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, FailGoal (_, __H, _)) -> monitorHead (cids, __H)
      | (cids, Resolved (Hc, Ha)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, Subgoal ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, Unify ((Hc, Ha), _, _)) -> monitorHeads (cids, (Hc, Ha))
      | (cids, FailUnify ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
    let rec monitorDetail =
      function
      | Unify _ -> (!detail) >= 2
      | FailUnify _ -> (!detail) >= 2
      | _ -> (!detail) >= 1
    let rec maintain __8__ __9__ =
      match (__8__, __9__) with
      | (__G, SolveGoal (_, _, __V)) -> setGoal (__G, __V)
      | (__G, RetryGoal (_, _, __V)) -> setGoal (__G, __V)
      | (__G, FailGoal (_, _, __V)) -> setGoal (__G, __V)
      | (__G, Unify (_, __Q, __P)) ->
          setEVarInst
            (Abstract.collectEVars
               (__G, (__P, I.id),
                 (Abstract.collectEVars (__G, (__Q, I.id), nil))))
      | _ -> ()(* show substitution for variables in clause head if tracing unification *)
    let rec monitorBreak __10__ __11__ __12__ =
      match (__10__, __11__, __12__) with
      | (None, __G, e) -> false__
      | (Some cids, __G, e) ->
          if monitorEvent (cids, e)
          then
            (maintain (__G, e); traceEvent (__G, e); breakAction __G; true__)
          else false__
      | (All, __G, e) ->
          (maintain (__G, e); traceEvent (__G, e); breakAction __G; true__)
    let rec monitorTrace __13__ __14__ __15__ =
      match (__13__, __14__, __15__) with
      | (None, __G, e) -> false__
      | (Some cids, __G, e) ->
          if monitorEvent (cids, e)
          then (maintain (__G, e); traceEvent (__G, e); newline (); true__)
          else false__
      | (All, __G, e) ->
          (maintain (__G, e); traceEvent (__G, e); newline (); true__)
    let rec watchFor e =
      match !watchForTag with
      | NONE -> false__
      | Some t ->
          (match e with
           | SolveGoal (Some t', _, _) -> t' = t
           | SucceedGoal (Some t', _, _) -> t' = t
           | CommitGoal (Some t', _, _) -> t' = t
           | RetryGoal (Some t', _, _) -> t' = t
           | FailGoal (Some t', _, _) -> t' = t
           | _ -> false__)
    let rec skipping () =
      match !watchForTag with | NONE -> false__ | Some _ -> true__
    let rec signal (__G) e =
      ((if monitorDetail e
        then
          (if skipping ()
           then
             (if watchFor e
              then (watchForTag := NONE; signal (__G, e))
              else (monitorTrace ((!traceTSpec), __G, e); ()))
           else
             ((if monitorBreak ((!breakTSpec), __G, e)
               then ()
               else (monitorTrace ((!traceTSpec), __G, e); ()))
             (* stops, continues after input *)))
        else ())
      (* prints trace, continues *))
    let rec showSpec __16__ __17__ =
      match (__16__, __17__) with
      | (msg, None) -> print (msg ^ " = None\n")
      | (msg, Some names) ->
          (print (msg ^ " = Some [");
           List.app (fun name -> print (" " ^ name)) names;
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
