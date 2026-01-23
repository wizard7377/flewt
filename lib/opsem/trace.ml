module type TRACE  =
  sig
    type nonrec goalTag
    val tagGoal : unit -> goalTag
    type event_ =
      | IntroHyp of (IntSyn.head_ * IntSyn.dec_) 
      | DischargeHyp of (IntSyn.head_ * IntSyn.dec_) 
      | IntroParm of (IntSyn.head_ * IntSyn.dec_) 
      | DischargeParm of (IntSyn.head_ * IntSyn.dec_) 
      | Resolved of (IntSyn.head_ * IntSyn.head_) 
      | Subgoal of ((IntSyn.head_ * IntSyn.head_) * (unit -> int)) 
      | SolveGoal of (goalTag * IntSyn.head_ * IntSyn.exp_) 
      | SucceedGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) *
      IntSyn.exp_) 
      | CommitGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_)
      
      | RetryGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_)
      
      | FailGoal of (goalTag * IntSyn.head_ * IntSyn.exp_) 
      | Unify of ((IntSyn.head_ * IntSyn.head_) * IntSyn.exp_ * IntSyn.exp_)
      
      | FailUnify of ((IntSyn.head_ * IntSyn.head_) * string) 
    val signal : (IntSyn.dctx * event_) -> unit
    val init : unit -> unit
    val tracing : unit -> bool
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
    let rec headToString =
      begin function
      | (g_, Const c) -> N.qidToString (N.constQid c)
      | (g_, Def d) -> N.qidToString (N.constQid d)
      | (g_, BVar k) -> N.bvarName (g_, k) end
    let rec expToString (GU) = (P.expToString GU) ^ ". "
    let rec decToString (GD) = (P.decToString GD) ^ ". "
    let rec eqnToString (g_, u1_, u2_) =
      ((^) ((P.expToString (g_, u1_)) ^ " = ") P.expToString (g_, u2_)) ^
        ". "
    let rec newline () = print "\n"
    let rec printCtx =
      begin function
      | I.Null -> print "No hypotheses or parameters. "
      | Decl (I.Null, d_) -> print (decToString (I.Null, d_))
      | Decl (g_, d_) ->
          (begin printCtx g_; newline (); print (decToString (g_, d_)) end) end
let rec evarsToString (Xnames) =
  let inst = P.evarInstToString Xnames in
  let constrOpt = P.evarCnstrsToStringOpt Xnames in
  begin match constrOpt with
  | None -> inst
  | Some constr -> (inst ^ "\nConstraints:\n") ^ constr end
let rec varsToEVarInst =
  begin function
  | [] -> []
  | name::names ->
      (begin match N.getEVarOpt name with
       | None ->
           (begin print
                    (("Trace warning: ignoring unknown variable " ^ name) ^
                       "\n");
            varsToEVarInst names end)
      | Some (x_) -> (::) (x_, name) varsToEVarInst names end) end
let rec printVars names = print (evarsToString (varsToEVarInst names))
let rec printVarstring line =
  printVars (List.tl (String.tokens Char.isSpace line))
type 'a spec_ =
  | None 
  | Some of 'a list 
  | All 
let (traceSpec : string spec_ ref) = ref None
let (breakSpec : string spec_ ref) = ref None
let rec trace =
  begin function
  | None -> traceSpec := None
  | Some names -> (:=) traceSpec Some names
  | All -> traceSpec := All end
let rec break =
  begin function
  | None -> breakSpec := None
  | Some names -> (:=) breakSpec Some names
  | All -> breakSpec := All end
let detail = ref 1
let rec setDetail =
  begin function
  | None -> print "Trace warning: detail is not a valid integer\n"
  | Some n -> ((if 0 <= n then begin detail := n end
      else begin print "Trace warning: detail must be positive\n" end)
  (* andalso n <= 2 *)) end
let (traceTSpec : I.cid spec_ ref) = ref None
let (breakTSpec : I.cid spec_ ref) = ref None
let rec toCids =
  begin function
  | [] -> []
  | name::names ->
      (begin match N.stringToQid name with
       | None ->
           (begin print
                    (("Trace warning: ignoring malformed qualified identifier "
                        ^ name)
                       ^ "\n");
            toCids names end)
      | Some qid ->
          (begin match N.constLookup qid with
           | None ->
               (begin print
                        (((^) "Trace warning: ignoring undeclared constant "
                            N.qidToString qid)
                           ^ "\n");
                toCids names end)
          | Some cid -> (::) cid toCids names end) end) end
let rec initTrace =
  begin function
  | None -> traceTSpec := None
  | Some names -> (:=) traceTSpec Some (toCids names)
  | All -> traceTSpec := All end
let rec initBreak =
  begin function
  | None -> breakTSpec := None
  | Some names -> (:=) breakTSpec Some (toCids names)
  | All -> breakTSpec := All end
let rec printHelp () =
  print
    "<newline> - continue --- execute with current settings\nn - next --- take a single step\nr - run --- remove all breakpoints and continue\ns - skip --- skip until current subgoals succeeds, is retried, or fails\ns n - skip to n --- skip until goal (n) is considered\nt - trace --- trace all events\nu - untrace --- trace no events\nd n - detail --- set trace detail to n (0, 1, or 2)\nh - hypotheses --- show current hypotheses\ng - goal --- show current goal\ni - instantiation --- show instantiation of variables in current goal\nv X1 ... Xn - variables --- show instantiation of X1 ... Xn\n? for help"
let (currentGoal : (I.dctx * I.exp_) ref) = ref (I.Null, (I.Uni I.Type))
let (currentEVarInst : (I.exp_ * string) list ref) = ref []
let rec setEVarInst (xs_) =
  (:=) currentEVarInst List.map
    (begin function | x_ -> (x_, (N.evarName (I.Null, x_))) end)
  xs_
let rec setGoal (g_, v_) =
  begin currentGoal := (g_, v_);
  setEVarInst (Abstract.collectEVars (g_, (v_, I.id), [])) end
type nonrec goalTag = int option
let (tag : goalTag ref) = ref None
let rec tagGoal () =
  begin match !tag with
  | None -> None
  | Some n -> (begin (:=) tag Some (n + 1); !tag end) end
let (watchForTag : goalTag ref) = ref None
let rec initTag () =
  begin watchForTag := None;
  (begin match (!traceTSpec, !breakTSpec) with
   | (None, None) -> tag := None
   | _ -> (:=) tag Some 0 end) end
let rec setWatchForTag =
  begin function
  | None -> (!) ((:=) watchForTag) tag
  | Some n -> (:=) watchForTag Some n end
let rec breakAction (g_) =
  let _ = print " " in
  let line = Compat.inputLine97 TextIO.stdIn in
  begin match String.sub (line, 0) with
  | '\n' -> ()
  | 'n' -> breakTSpec := All
  | 'r' -> breakTSpec := None
  | 's' -> setWatchForTag (Int.fromString (String.extract (line, 1, None)))
  | 't' ->
      (begin traceTSpec := All; print "% Now tracing all"; breakAction g_ end)
    | 'u' ->
        (begin traceTSpec := None; print "% Now tracing none"; breakAction g_ end)
    | 'd' ->
        (begin setDetail (Int.fromString (String.extract (line, 1, None)));
         print ((^) "% Trace detail now " Int.toString !detail);
         breakAction g_ end)
  | 'h' -> (begin printCtx g_; breakAction g_ end)
  | 'g' -> (begin print (expToString !currentGoal); breakAction g_ end)
| 'i' ->
    (begin print (evarsToString (List.rev !currentEVarInst)); breakAction g_ end)
| 'v' -> (begin printVarstring line; breakAction g_ end)
| '?' -> (begin printHelp (); breakAction g_ end)
| _ -> (begin print "unrecognized command (? for help)"; breakAction g_ end) end
let rec init () =
  begin initTrace !traceSpec; initBreak !breakSpec; initTag () end
type event_ =
  | IntroHyp of (IntSyn.head_ * IntSyn.dec_) 
  | DischargeHyp of (IntSyn.head_ * IntSyn.dec_) 
  | IntroParm of (IntSyn.head_ * IntSyn.dec_) 
  | DischargeParm of (IntSyn.head_ * IntSyn.dec_) 
  | Resolved of (IntSyn.head_ * IntSyn.head_) 
  | Subgoal of ((IntSyn.head_ * IntSyn.head_) * (unit -> int)) 
  | SolveGoal of (goalTag * IntSyn.head_ * IntSyn.exp_) 
  | SucceedGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_) 
  | CommitGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_) 
  | RetryGoal of (goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_) 
  | FailGoal of (goalTag * IntSyn.head_ * IntSyn.exp_) 
  | Unify of ((IntSyn.head_ * IntSyn.head_) * IntSyn.exp_ * IntSyn.exp_) 
  | FailUnify of ((IntSyn.head_ * IntSyn.head_) * string) 
let rec eventToString =
  begin function
  | (g_, IntroHyp (_, d_)) ->
      (^) "% Introducing hypothesis\n" decToString (g_, d_)
  | (g_, DischargeHyp (_, Dec (Some x, _))) ->
      "% Discharging hypothesis " ^ x
  | (g_, IntroParm (_, d_)) ->
      (^) "% Introducing parameter\n" decToString (g_, d_)
  | (g_, DischargeParm (_, Dec (Some x, _))) ->
      "% Discharging parameter " ^ x
  | (g_, Resolved (Hc, Ha)) ->
      (^) (((^) "% Resolved with clause " headToString (g_, Hc)) ^ "\n")
        evarsToString (List.rev !currentEVarInst)
  | (g_, Subgoal ((Hc, Ha), msg)) ->
      (^) (((^) "% Solving subgoal (" Int.toString (msg ())) ^ ") of clause ")
        headToString (g_, Hc)
  | (g_, SolveGoal (Some tag, _, v_)) ->
      (^) (((^) "% Goal " Int.toString tag) ^ ":\n") expToString (g_, v_)
  | (g_, SucceedGoal (Some tag, _, v_)) ->
      ((^) "% Goal " Int.toString tag) ^ " succeeded"
  | (g_, CommitGoal (Some tag, _, v_)) ->
      ((^) "% Goal " Int.toString tag) ^ " committed to first solution"
  | (g_, RetryGoal (Some tag, (Hc, Ha), v_)) ->
      (^) (((^) ((((^) "% Backtracking from clause " headToString (g_, Hc)) ^
                    "\n")
                   ^ "% Retrying goal ")
              Int.toString tag)
             ^ ":\n")
        expToString (g_, v_)
  | (g_, FailGoal (Some tag, _, v_)) -> (^) "% Failed goal " Int.toString tag
  | (g_, Unify ((Hc, Ha), q_, p_)) ->
      (^) (((^) "% Trying clause " headToString (g_, Hc)) ^ "\n") eqnToString
        (g_, q_, p_)
  | (g_, FailUnify ((Hc, Ha), msg)) ->
      (((^) "% Unification failed with clause " headToString (g_, Hc)) ^
         ":\n")
        ^ msg end
let rec traceEvent (g_, e) = print (eventToString (g_, e))
let rec monitorHead =
  begin function
  | (cids, Const c) -> List.exists (begin function | c' -> c = c' end) cids
  | (cids, Def d) -> List.exists (begin function | c' -> d = c' end) cids
  | (cids, BVar k) -> false end
let rec monitorHeads (cids, (Hc, Ha)) =
  (monitorHead (cids, Hc)) || (monitorHead (cids, Ha))
let rec monitorEvent =
  begin function
  | (cids, IntroHyp (h_, _)) -> monitorHead (cids, h_)
  | (cids, DischargeHyp (h_, _)) -> monitorHead (cids, h_)
  | (cids, IntroParm (h_, _)) -> monitorHead (cids, h_)
  | (cids, DischargeParm (h_, _)) -> monitorHead (cids, h_)
  | (cids, SolveGoal (_, h_, v_)) -> monitorHead (cids, h_)
  | (cids, SucceedGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, CommitGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, RetryGoal (_, (Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, FailGoal (_, h_, _)) -> monitorHead (cids, h_)
  | (cids, Resolved (Hc, Ha)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, Subgoal ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, Unify ((Hc, Ha), _, _)) -> monitorHeads (cids, (Hc, Ha))
  | (cids, FailUnify ((Hc, Ha), _)) -> monitorHeads (cids, (Hc, Ha)) end
let rec monitorDetail =
  begin function
  | Unify _ -> !detail >= 2
  | FailUnify _ -> !detail >= 2
  | _ -> !detail >= 1 end
let rec maintain =
  begin function
  | (g_, SolveGoal (_, _, v_)) -> setGoal (g_, v_)
  | (g_, RetryGoal (_, _, v_)) -> setGoal (g_, v_)
  | (g_, FailGoal (_, _, v_)) -> setGoal (g_, v_)
  | (g_, Unify (_, q_, p_)) ->
      setEVarInst
        (Abstract.collectEVars
           (g_, (p_, I.id), (Abstract.collectEVars (g_, (q_, I.id), []))))
  | _ -> () end(* show substitution for variables in clause head if tracing unification *)
let rec monitorBreak =
  begin function
  | (None, g_, e) -> false
  | (Some cids, g_, e) ->
      if monitorEvent (cids, e)
      then
        begin (begin maintain (g_, e);
               traceEvent (g_, e);
               breakAction g_;
               true end) end
  else begin false end
| (All, g_, e) ->
    (begin maintain (g_, e); traceEvent (g_, e); breakAction g_; true end) end
let rec monitorTrace =
  begin function
  | (None, g_, e) -> false
  | (Some cids, g_, e) ->
      if monitorEvent (cids, e)
      then
        begin (begin maintain (g_, e); traceEvent (g_, e); newline (); true end) end
  else begin false end
| (All, g_, e) ->
    (begin maintain (g_, e); traceEvent (g_, e); newline (); true end) end
let rec watchFor e =
  begin match !watchForTag with
  | None -> false
  | Some t ->
      (begin match e with
       | SolveGoal (Some t', _, _) -> t' = t
       | SucceedGoal (Some t', _, _) -> t' = t
       | CommitGoal (Some t', _, _) -> t' = t
       | RetryGoal (Some t', _, _) -> t' = t
       | FailGoal (Some t', _, _) -> t' = t
       | _ -> false end) end
let rec skipping () =
  begin match !watchForTag with | None -> false | Some _ -> true end
let rec signal (g_, e) =
  ((if monitorDetail e
    then
      begin (if skipping ()
             then
               begin (if watchFor e
                      then
                        begin (begin watchForTag := None; signal (g_, e) end) end
             else begin (begin monitorTrace (!traceTSpec, g_, e); () end) end) end
else begin ((if monitorBreak (!breakTSpec, g_, e) then begin () end
  else begin (begin monitorTrace (!traceTSpec, g_, e); () end) end)
(* stops, continues after input *)) end) end
else begin () end)
(* prints trace, continues *))
let rec showSpec =
  begin function
  | (msg, None) -> print (msg ^ " = None\n")
  | (msg, Some names) ->
      (begin print (msg ^ " = Some [");
       List.app (begin function | name -> print (" " ^ name) end)
       names;
      print "]\n" end)
  | (msg, All) -> print (msg ^ " = All\n") end
let rec tracing () =
  begin match (!traceSpec, !breakSpec) with
  | (None, None) -> false
  | _ -> true end
let rec show () =
  begin showSpec ("trace", !traceSpec);
  showSpec ("break", !breakSpec);
  print (((^) "detail = " Int.toString !detail) ^ "\n") end
let rec reset () = begin trace None; break None; detail := 1 end end
