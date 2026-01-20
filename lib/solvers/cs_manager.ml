
module type CS_MANAGER  =
  sig
    module Fixity : FIXITY
    type nonrec sigEntry =
      (IntSyn.__ConDec * Fixity.fixity option * ModeSyn.__ModeSpine list)
    type nonrec fgnConDec = < parse: string -> IntSyn.__ConDec option   > 
    type nonrec solver =
      ((<
          name: string
            (* trailing operations *)(* reset internal status *)
            (* install constants *)(* foreign constants declared (if any) *)
            (* names of other constraint solvers needed *)
            (* NOTE: no two solvers with the same keywords may be active simultaneously *)
            (* keywords identifying the type of solver *) ;
          keywords: string  ;needs: string list  ;fgnConst: fgnConDec option  ;
          init: int -> (sigEntry -> IntSyn.cid) -> unit  ;reset: unit -> unit
                                                             ;mark: unit ->
                                                                    unit  ;
          unwind: unit -> unit   > )(* name is the name of the solver *))
    exception Error of string 
    val setInstallFN : (sigEntry -> IntSyn.cid) -> unit
    val installSolver : solver -> IntSyn.csid
    val resetSolvers : unit -> unit
    val useSolver : string -> unit
    val parse : string -> (IntSyn.csid * IntSyn.__ConDec) option
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
      ((<
          name: string
            (* trailing operations *)(* reset internal status *)
            (* install constants *)(* foreign constants declared (if any) *)
            (* names of other constraint solvers needed *)
            (* NOTE: no two solvers with the same keywords may be active simultaneously *)
            (* keywords identifying the type of solver *) ;
          keywords: string  ;needs: string list  ;fgnConst: fgnConDec option  ;
          init: int -> (sigEntry -> IntSyn.cid) -> unit  ;reset: unit -> unit
                                                             ;mark: unit ->
                                                                    unit  ;
          unwind: unit -> unit   > )(* name is the name of the solver *))
    exception Error of string 
    let emptySolver =
      {
        name = "";
        keywords = "";
        needs = nil;
        fgnConst = NONE;
        init = (fun _ -> ());
        reset = (fun () -> ());
        mark = (fun () -> ());
        unwind = (fun () -> ())
      }
    let unifySolver =
      {
        name = "Unify";
        keywords = "unification";
        needs = nil;
        fgnConst = NONE;
        init = (fun _ -> ());
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
    let installFN = (ref (fun _ -> (-1)) : (sigEntry -> IntSyn.cid) ref)
    let rec setInstallFN f = installFN := f
    let rec installSolver solver =
      let cs = !nextCS in
      let _ =
        if (!nextCS) > maxCS
        then raise (Error "too many constraint solvers")
        else () in
      let _ = Array.update (csArray, cs, (Solver (solver, (ref false__)))) in
      let _ = ((!) ((:=) nextCS) nextCS) + 1 in ((cs)
        (* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *))
    let _ = installSolver unifySolver
    let activeKeywords = (ref nil : string list ref)
    let rec resetSolvers () =
      ArraySlice.appi
        (fun cs ->
           fun (Solver (solver, active)) ->
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
              (fun cs ->
                 fun (Solver (solver, _)) ->
                   if ((fun r -> r.name) solver) = name
                   then raise (Found cs)
                   else ()) (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
            NONE
          with | Found cs -> Some cs in
        match findSolver name with
        | Some cs ->
            let Solver (solver, active) = Array.sub (csArray, cs) in
            if !active
            then ()
            else
              if
                List.exists (fun s -> (=) s (fun r -> r.keywords) solver)
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
        | NONE -> raise (Error (("solver " ^ name) ^ " not found"))
    let rec parse string =
      let exception Parsed of (IntSyn.csid * IntSyn.__ConDec)  in
        let rec parse' cs (solver : solver) =
          match (fun r -> r.fgnConst) solver with
          | NONE -> ()
          | Some fgnConDec ->
              (match (fun r -> r.parse) fgnConDec string with
               | NONE -> ()
               | Some conDec -> raise (Parsed (cs, conDec))) in
        try
          ArraySlice.appi
            (fun cs ->
               fun (Solver (solver, active)) ->
                 if !active then parse' (cs, solver) else ())
            (ArraySlice.slice (csArray, 0, (Some (!nextCS))));
          NONE
        with | Parsed info -> Some info
    let markCount = (ref 0 : int ref)
    let rec reset () =
      ArraySlice.appi
        (fun _ ->
           fun (Solver (solver, active)) ->
             if !active
             then (markCount := 0; ((fun r -> r.reset)) solver ())
             else ()) (ArraySlice.slice (csArray, 0, (Some (!nextCS))))
    let rec mark () =
      ((!) ((:=) markCount) markCount) + 1;
      ArraySlice.appi
        (fun _ ->
           fun (Solver (solver, active)) ->
             if !active then (fun r -> r.mark) solver () else ())
        (ArraySlice.slice (csArray, 0, (Some (!nextCS))))
    let rec unwind targetCount =
      let rec unwind' =
        function
        | 0 -> markCount := targetCount
        | k ->
            (ArraySlice.appi
               (fun _ ->
                  fun (Solver (solver, active)) ->
                    if !active then (fun r -> r.unwind) solver () else ())
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
  end 
module CSManager =
  (Make_CSManager)(struct
                     module Global = Global
                     module Unify = UnifyTrail
                     module Fixity = Names.Fixity
                   end);;
