
(* Constraint Solver Manager *)
(* Author: Roberto Virga *)
module type CS_MANAGER  =
  sig
    (* structure IntSyn : INTSYN *)
    module Fixity : FIXITY
    (*! structure ModeSyn : MODESYN !*)
    type nonrec sigEntry =
      (IntSyn.__ConDec * Fixity.fixity option * ModeSyn.__ModeSpine list)
    type nonrec fgnConDec = < parse: string -> IntSyn.__ConDec option   > 
    type nonrec solver =
      <
        name: string  ;keywords: string  ;needs: string list  ;fgnConst: 
                                                                 fgnConDec
                                                                   option  ;
        init: (int * (sigEntry -> IntSyn.cid)) -> unit  ;reset: unit -> unit  ;
        mark: unit -> unit  ;unwind: unit -> unit   > 
    (* name is the name of the solver *)
    (* keywords identifying the type of solver *)
    (* NOTE: no two solvers with the same keywords may be active simultaneously *)
    (* names of other constraint solvers needed *)
    (* foreign constants declared (if any) *)
    (* install constants *)
    (* reset internal status *)
    (* trailing operations *)
    exception Error of string 
    (* solver handling functions *)
    val setInstallFN : (sigEntry -> IntSyn.cid) -> unit
    val installSolver : solver -> IntSyn.csid
    val resetSolvers : unit -> unit
    val useSolver : string -> unit
    (* parsing foreign constatnts *)
    val parse : string -> (IntSyn.csid * IntSyn.__ConDec) option
    (* trailing operations *)
    val reset : unit -> unit
    val trail : (unit -> 'a) -> 'a
  end;;




module CSManager(CSManager:sig
                             module Global : GLOBAL
                             module Unify : UNIFY
                             module Fixity : FIXITY
                           end) : CS_MANAGER =
  struct
    module IntSyn = IntSyn
    module Fixity = Fixity
    type nonrec sigEntry =
      (IntSyn.__ConDec * Fixity.fixity option * ModeSyn.__ModeSpine list)
    type nonrec fgnConDec = < parse: string -> IntSyn.__ConDec option   > 
    type nonrec solver =
      <
        name: string  ;keywords: string  ;needs: string list  ;fgnConst: 
                                                                 fgnConDec
                                                                   option  ;
        init: (int * (sigEntry -> IntSyn.cid)) -> unit  ;reset: unit -> unit  ;
        mark: unit -> unit  ;unwind: unit -> unit   > 
    exception Error of string 
    let emptySolver =
      {
        name = "";
        keywords = "";
        needs = nil;
        fgnConst = None;
        init = (function | _ -> ());
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
    let unifySolver =
      {
        name = "Unify";
        keywords = "unification";
        needs = nil;
        fgnConst = None;
        init = (function | _ -> ());
        reset = Unify.reset;
        mark = Unify.mark;
        unwind = Unify.unwind
      }
    type __Solver =
      | Solver of (solver * bool ref) 
    let maxCS = Global.maxCSid
    let csArray =
      (Array.array ((maxCS + 1), (Solver (emptySolver, (ref false__)))) : 
      __Solver Array.array)
    let _ = Array.update (csArray, 0, (Solver (unifySolver, (ref true__))))
    let nextCS = (ref 1 : int ref)
    let installFN =
      (ref (function | _ -> (-1)) : (sigEntry -> IntSyn.cid) ref)
    let rec setInstallFN f = installFN := f
    let rec installSolver solver =
      let cs = !nextCS in
      let _ =
        if (!nextCS) > maxCS
        then raise (Error "too many constraint solvers")
        else () in
      let _ = Array.update (csArray, cs, (Solver (solver, (ref false__)))) in
      let _ = ((!) ((:=) nextCS) nextCS) + 1 in cs
    let _ = installSolver unifySolver
    let activeKeywords = (ref nil : string list ref)
    let rec resetSolvers () =
      ArraySlice.appi
        (function
         | (cs, Solver (solver, active)) ->
             if !active
             then (active := false__; ((fun r -> r.reset)) solver ())
             else ()) (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
      activeKeywords := nil;
      useSolver "Unify"
    let rec useSolver name =
      let exception Found of IntSyn.csid  in
        let rec findSolver name =
          try
            ArraySlice.appi
              (function
               | (cs, Solver (solver, _)) ->
                   if ((fun r -> r.name) solver) = name
                   then raise (Found cs)
                   else ()) (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
            None
          with | Found cs -> Some cs in
        match findSolver name with
        | Some cs ->
            let Solver (solver, active) = Array.sub (csArray, cs) in
            if !active
            then ()
            else
              if
                List.exists
                  (function | s -> (=) s ((fun r -> r.keywords)) solver)
                  (!activeKeywords)
              then
                raise
                  (Error
                     (("solver " ^ name) ^
                        " is incompatible with a currently active solver"))
              else
                (active := true__;
                 ((:=) activeKeywords (fun r -> r.keywords) solver) ::
                   (!activeKeywords);
                 List.app useSolver ((fun r -> r.needs) solver);
                 ((fun r -> r.init)) solver (cs, (!installFN)))
        | None -> raise (Error (("solver " ^ name) ^ " not found"))
    let rec parse string =
      let exception Parsed of (IntSyn.csid * IntSyn.__ConDec)  in
        let rec parse' (cs, (solver : solver)) =
          match (fun r -> r.fgnConst) solver with
          | None -> ()
          | Some fgnConDec ->
              (match (fun r -> r.parse) fgnConDec string with
               | None -> ()
               | Some conDec -> raise (Parsed (cs, conDec))) in
        try
          ArraySlice.appi
            (function
             | (cs, Solver (solver, active)) ->
                 if !active then parse' (cs, solver) else ())
            (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
          None
        with | Parsed info -> Some info
    let markCount = (ref 0 : int ref)
    let rec reset () =
      ArraySlice.appi
        (function
         | (_, Solver (solver, active)) ->
             if !active
             then (markCount := 0; ((fun r -> r.reset)) solver ())
             else ()) (ArraySlice.slice (csArray, 0, (Some (!nextCS))))
    let rec mark () =
      ((!) ((:=) markCount) markCount) + 1;
      ArraySlice.appi
        (function
         | (_, Solver (solver, active)) ->
             if !active then ((fun r -> r.mark)) solver () else ())
        (ArraySlice.slice (csArray, 0, (Some (!nextCS))))
    let rec unwind targetCount =
      let rec unwind' =
        function
        | 0 -> markCount := targetCount
        | k ->
            (ArraySlice.appi
               (function
                | (_, Solver (solver, active)) ->
                    if !active then ((fun r -> r.unwind)) solver () else ())
               (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
             unwind' (k - 1)) in
      unwind' ((!markCount) - targetCount)
    let rec trail f =
      let current = !markCount in
      let _ = mark () in let r = f () in let _ = unwind current in r
    let setInstallFN = setInstallFN
    let installSolver = installSolver
    let resetSolvers = resetSolvers
    let useSolver = useSolver
    let parse = parse
    let reset = reset
    let trail = trail
  end  (* Constraint Solver Manager *)
(* Author: Roberto Virga *)
(*! structure IntSyn : INTSYN !*)
(*! sharing Unify.IntSyn = IntSyn !*)
(*! structure ModeSyn : MODESYN !*)
(* structure ModeSyn = ModeSyn *)
(* global signature entry *)
(* constant declaration plus optional precedence and mode information *)
(* foreign constant declaration *)
(* constraint solver *)
(* name is the name of the solver *)
(* keywords identifying the type of solver *)
(* NOTE: no two solvers with the same keywords may be active simultaneously *)
(* names of other constraint solvers needed *)
(* foreign constants declared (if any) *)
(* install constants *)
(* reset internal status *)
(* trailing operations *)
(* vacuous solver *)
(* Twelf unification as a constraint solver *)
(* List of installed solvers *)
(* Installing function *)
(* install the specified solver *)
(* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *)
(* install the unification solver *)
(* make all the solvers inactive *)
(* make the specified solver active *)
(* ask each active solver to try and parse the given string *)
(* reset the internal status of all the active solvers *)
(* mark all active solvers *)
(* unwind all active solvers *)
(* trail the give function *)
(* functor CSManager *)
module CSManager =
  (Make_CSManager)(struct
                     module Global = Global
                     (*! structure IntSyn = IntSyn !*)
                     module Unify = UnifyTrail
                     module Fixity = Names.Fixity
                   end);;
