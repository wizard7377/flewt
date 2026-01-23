module type CS_MANAGER  =
  sig
    module Fixity : FIXITY
    type nonrec sigEntry =
      (IntSyn.conDec_ * Fixity.fixity option * ModeSyn.modeSpine_ list)
    type nonrec fgnConDec = < parse: string -> IntSyn.conDec_ option   > 
    type nonrec solver =
      ((<
          name: string
            (* trailing operations *)(* reset internal status *)
            (* install constants *)(* foreign constants declared (if any) *)
            (* names of other constraint solvers needed *)
            (* NOTE: no two solvers with the same keywords may be active simultaneously *)
            (* keywords identifying the type of solver *) ;
          keywords: string  ;needs: string list  ;fgnConst: fgnConDec option  ;
          init: (int * (sigEntry -> IntSyn.cid)) -> unit  ;reset: unit ->
                                                                    unit  ;
          mark: unit -> unit  ;unwind: unit -> unit   > )(* name is the name of the solver *))
    exception Error of string 
    val setInstallFN : (sigEntry -> IntSyn.cid) -> unit
    val installSolver : solver -> IntSyn.csid
    val resetSolvers : unit -> unit
    val useSolver : string -> unit
    val parse : string -> (IntSyn.csid * IntSyn.conDec_) option
    val reset : unit -> unit
    val trail : (unit -> 'a) -> 'a
  end


module CSManager(CSManager:sig
                             module Global : GLOBAL
                             module Unify : UNIFY
                             module Fixity : FIXITY
                           end) : CS_MANAGER =
  struct
    module IntSyn = IntSyn
    module Fixity = Fixity
    type nonrec sigEntry =
      (IntSyn.conDec_ * Fixity.fixity option * ModeSyn.modeSpine_ list)
    type nonrec fgnConDec = < parse: string -> IntSyn.conDec_ option   > 
    type nonrec solver =
      ((<
          name: string
            (* trailing operations *)(* reset internal status *)
            (* install constants *)(* foreign constants declared (if any) *)
            (* names of other constraint solvers needed *)
            (* NOTE: no two solvers with the same keywords may be active simultaneously *)
            (* keywords identifying the type of solver *) ;
          keywords: string  ;needs: string list  ;fgnConst: fgnConDec option  ;
          init: (int * (sigEntry -> IntSyn.cid)) -> unit  ;reset: unit ->
                                                                    unit  ;
          mark: unit -> unit  ;unwind: unit -> unit   > )(* name is the name of the solver *))
    exception Error of string 
    let emptySolver =
      {
        name = "";
        keywords = "";
        needs = [];
        fgnConst = None;
        init = (begin function | _ -> () end);
      reset = (begin function | () -> () end);
      mark = (begin function | () -> () end);
      unwind = (begin function | () -> () end)
    }
let unifySolver =
  {
    name = "Unify";
    keywords = "unification";
    needs = [];
    fgnConst = None;
    init = (begin function | _ -> () end);
  reset = Unify.reset;
  mark = Unify.mark;
  unwind = Unify.unwind }
type solver_ =
  | Solver of (solver * bool ref) 
let maxCS = Global.maxCSid
let csArray =
  (Array.array ((maxCS + 1), (Solver (emptySolver, (ref false)))) : solver_
                                                                    Array.array)
let _ = Array.update (csArray, 0, (Solver (unifySolver, (ref true))))
let nextCS = (ref 1 : int ref)
let installFN = (ref (begin function | _ -> (-1) end) : (sigEntry ->
                                                           IntSyn.cid)
                                                          ref)
let rec setInstallFN f = installFN := f
let rec installSolver solver =
  let cs = !nextCS in
  let _ =
    if !nextCS > maxCS
    then begin raise (Error "too many constraint solvers") end
    else begin () end in
let _ = Array.update (csArray, cs, (Solver (solver, (ref false)))) in
let _ = ((!) ((:=) nextCS) nextCS) + 1 in ((cs)
  (* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *))
let _ = installSolver unifySolver
let activeKeywords = (ref [] : string list ref)
let rec resetSolvers () =
  begin ArraySlice.appi
          (begin function
           | (cs, Solver (solver, active)) ->
               if !active
               then
                 begin (begin active := false; ((fun r -> r.reset)) solver () end) end
           else begin () end end)
(ArraySlice.slice (csArray, 0, (Some !nextCS))); activeKeywords := [];
useSolver "Unify" end
let rec useSolver name =
  let exception Found of IntSyn.csid  in
    let rec findSolver name =
      begin try
              begin ArraySlice.appi
                      (begin function
                       | (cs, Solver (solver, _)) ->
                           if ((fun r -> r.name) solver) = name
                           then begin raise (Found cs) end else begin () end end)
      (ArraySlice.slice (csArray, 0, (Some !nextCS))); None end
  with | Found cs -> Some cs end in
begin match findSolver name with
| Some cs ->
  let Solver (solver, active) = Array.sub (csArray, cs) in
  if !active then begin () end
    else begin
      if
        List.exists
          (begin function | s -> (=) s ((fun r -> r.keywords)) solver end)
        !activeKeywords
      then
        begin raise
                (Error
                   (("solver " ^ name) ^
                      " is incompatible with a currently active solver")) end
    else begin
      (begin active := true;
       ((:=) activeKeywords (fun r -> r.keywords) solver) :: !activeKeywords;
       List.app useSolver ((fun r -> r.needs) solver);
       ((fun r -> r.init)) solver (cs, !installFN) end) end end
| None -> raise (Error (("solver " ^ name) ^ " not found")) end
let rec parse string =
  let exception Parsed of (IntSyn.csid * IntSyn.conDec_)  in
    let rec parse' (cs, (solver : solver)) =
      begin match (fun r -> r.fgnConst) solver with
      | None -> ()
      | Some fgnConDec ->
          (begin match (fun r -> r.parse) fgnConDec string with
           | None -> ()
           | Some conDec -> raise (Parsed (cs, conDec)) end) end in
begin try
        begin ArraySlice.appi
                (begin function
                 | (cs, Solver (solver, active)) ->
                     if !active then begin parse' (cs, solver) end
                     else begin () end end)
(ArraySlice.slice (csArray, 0, (Some !nextCS))); None end
with | Parsed info -> Some info end
let markCount = (ref 0 : int ref)
let rec reset () =
  ArraySlice.appi
    (begin function
     | (_, Solver (solver, active)) ->
         if !active
         then begin (begin markCount := 0; ((fun r -> r.reset)) solver () end) end
     else begin () end end)
(ArraySlice.slice (csArray, 0, (Some !nextCS)))
let rec mark () =
  begin ((!) ((:=) markCount) markCount) + 1;
  ArraySlice.appi
    (begin function
     | (_, Solver (solver, active)) ->
         if !active then begin ((fun r -> r.mark)) solver () end
         else begin () end end)
  (ArraySlice.slice (csArray, 0, (Some !nextCS))) end
let rec unwind targetCount =
  let rec unwind' =
    begin function
    | 0 -> markCount := targetCount
    | k ->
        (begin ArraySlice.appi
                 (begin function
                  | (_, Solver (solver, active)) ->
                      if !active
                      then begin ((fun r -> r.unwind)) solver () end
                      else begin () end end)
    (ArraySlice.slice (csArray, 0, (Some !nextCS))); unwind' (k - 1) end) end in
unwind' (!markCount - targetCount)
let rec trail f =
  let current = !markCount in
  let _ = mark () in let r = f () in let _ = unwind current in r
let setInstallFN = setInstallFN
let installSolver = installSolver
let resetSolvers = resetSolvers
let useSolver = useSolver
let parse = parse
let reset = reset
let trail = trail end 
module CSManager =
  (CSManager)(struct
                     module Global = Global
                     module Unify = UnifyTrail
                     module Fixity = Names.Fixity
                   end)