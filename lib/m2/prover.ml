module type PROVER  =
  sig
    exception Error of string 
    val init : (int * IntSyn.cid list) -> unit
    val auto : unit -> unit
    val print : unit -> unit
    val install : (IntSyn.conDec_ -> IntSyn.cid) -> unit
  end


module Prover(Prover:sig
                       module MetaGlobal : METAGLOBAL
                       module MetaSyn' : METASYN
                       module Init : INIT
                       module Strategy : STRATEGY
                       module Filling : FILLING
                       module Splitting : SPLITTING
                       module Recursion : RECURSION
                       module Qed : QED
                       module MetaPrint : METAPRINT
                       module Names : NAMES
                       module Timers : TIMERS
                     end) : PROVER =
  struct
    exception Error of string 
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    module I = IntSyn
    let (openStates : MetaSyn.state_ list ref) = ref []
    let (solvedStates : MetaSyn.state_ list ref) = ref []
    let rec error s = raise (Error s)
    let rec reset () = begin openStates := []; solvedStates := [] end
    let rec contains =
      begin function
      | ([], _) -> true
      | (x::l_, l'_) -> (List.exists (begin function | x' -> x = x' end) l'_)
          && (contains (l_, l'_)) end
let rec equiv (l1_, l2_) = (contains (l1_, l2_)) && (contains (l2_, l1_))
let rec insertState (s_) =
  if Qed.subgoal s_ then begin (solvedStates := s_) :: !solvedStates end
  else begin (openStates := s_) :: !openStates end
let rec cLToString =
  begin function
  | [] -> ""
  | c::[] -> I.conDecName (I.sgnLookup c)
  | c::l_ -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString l_) end
let rec init (k, (c::_ as cL)) =
  let _ = MetaGlobal.maxFill := k in
  let _ = reset () in
  let cL' = begin try Order.closure c with | Error _ -> cL end in
  ((if equiv (cL, cL')
    then begin List.app (begin function | s_ -> insertState s_ end)
      (Init.init cL) end
    else begin
      raise
        (Error
           (("Theorem by simultaneous induction not correctly stated:" ^
               "\n            expected: ")
              ^ (cLToString cL'))) end)
  (* if no termination ordering given! *))
let rec auto () =
  let _ = print "M2.Prover.auto\n" in
  let (Open, solvedStates') =
    begin try Strategy.run !openStates
    with | Error s -> error ("Splitting Error: " ^ s)
    | Error s -> error ("A proof could not be found -- Filling Error: " ^ s)
    | Error s -> error ("Recursion Error: " ^ s)
    | Filling.TimeOut ->
        error "A proof could not be found -- Exceeding Time Limit\n" end in
  let _ = openStates := Open in
  let _ = (solvedStates := !solvedStates) @ solvedStates' in
  if (List.length !openStates) > 0
  then begin raise (Error "A proof could not be found") end else begin () end
let rec makeConDec (State (name, Prefix (g_, m_, b_), v_)) =
  let rec makeConDec' =
    begin function
    | (I.Null, v_, k) -> I.ConDec (name, None, k, I.Normal, v_, I.Type)
    | (Decl (g_, d_), v_, k) ->
        makeConDec' (g_, (I.Pi ((d_, I.Maybe), v_)), (k + 1)) end in
makeConDec' (g_, v_, 0)
let rec makeSignature =
  begin function
  | [] -> M.SgnEmpty
  | (s_)::SL -> M.ConDec ((makeConDec s_), (makeSignature SL)) end
let rec install installConDec =
  let rec install' =
    begin function
    | M.SgnEmpty -> ()
    | ConDec (e, s_) -> (begin installConDec e; install' s_ end) end in
let IS =
  if (List.length !openStates) > 0
  then begin raise (Error "Theorem not proven") end
  else begin makeSignature !solvedStates end in
begin install' IS;
if !Global.chatter > 2
then
begin (begin print "% ------------------\n";
       print (MetaPrint.sgnToString IS);
       print "% ------------------\n" end) end
else begin () end end
let rec printState () =
  let rec print' =
    begin function
    | [] -> ()
    | (s_)::l_ -> (begin print (MetaPrint.stateToString s_); print' l_ end) end in
begin print "Open problems:\n";
print "==============\n\n";
print' !openStates;
print "Solved problems:\n";
print "================\n\n";
print' !solvedStates end
let print = printState
let init = init
let auto = auto
let install = install end
