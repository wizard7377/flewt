
(* Meta Prover *)
(* Author: Carsten Schuermann *)
module type PROVER  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    val init : (int * IntSyn.cid list) -> unit
    val auto : unit -> unit
    val print : unit -> unit
    val install : (IntSyn.__ConDec -> IntSyn.cid) -> unit
  end;;




(* Meta Prover *)
(* Author: Carsten Schuermann *)
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
                       (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                       module Timers : TIMERS
                     end) : PROVER =
  struct
    (*! structure IntSyn = MetaSyn'.IntSyn !*)
    exception Error of string 
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    module I = IntSyn
    let (openStates : MetaSyn.__State list ref) = ref nil
    let (solvedStates : MetaSyn.__State list ref) = ref nil
    let rec error s = raise (Error s)
    let rec reset () = openStates := nil; solvedStates := nil
    let rec contains =
      function
      | (nil, _) -> true__
      | (x::L, L') ->
          (List.exists (function | x' -> x = x') L') && (contains (L, L'))
    let rec equiv (L1, L2) = (contains (L1, L2)) && (contains (L2, L1))
    let rec insertState (S) =
      if Qed.subgoal S
      then (solvedStates := S) :: (!solvedStates)
      else (openStates := S) :: (!openStates)
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString L)
    let rec init (k, (c::_ as cL)) =
      let _ = MetaGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      if equiv (cL, cL')
      then List.app (function | S -> insertState S) (Init.init cL)
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:" ^
                 "\n            expected: ")
                ^ (cLToString cL')))
    let rec auto () =
      let _ = print "M2.Prover.auto\n" in
      let (Open, solvedStates') =
        try Strategy.run (!openStates)
        with | Error s -> error ("Splitting Error: " ^ s)
        | Error s ->
            error ("A proof could not be found -- Filling Error: " ^ s)
        | Error s -> error ("Recursion Error: " ^ s)
        | Filling.TimeOut ->
            error "A proof could not be found -- Exceeding Time Limit\n" in
      let _ = openStates := Open in
      let _ = (solvedStates := (!solvedStates)) @ solvedStates' in
      if (List.length (!openStates)) > 0
      then raise (Error "A proof could not be found")
      else ()
    let rec makeConDec (State (name, Prefix (G, M, B), V)) =
      let rec makeConDec' =
        function
        | (I.Null, V, k) -> I.ConDec (name, NONE, k, I.Normal, V, I.Type)
        | (Decl (G, D), V, k) ->
            makeConDec' (G, (I.Pi ((D, I.Maybe), V)), (k + 1)) in
      makeConDec' (G, V, 0)
    let rec makeSignature =
      function
      | nil -> M.SgnEmpty
      | (S)::SL -> M.ConDec ((makeConDec S), (makeSignature SL))
    let rec install installConDec =
      let rec install' =
        function
        | M.SgnEmpty -> ()
        | ConDec (e, S) -> (installConDec e; install' S) in
      let IS =
        if (List.length (!openStates)) > 0
        then raise (Error "Theorem not proven")
        else makeSignature (!solvedStates) in
      install' IS;
      if (!Global.chatter) > 2
      then
        (print "% ------------------\n";
         print (MetaPrint.sgnToString IS);
         print "% ------------------\n")
      else ()
    let rec printState () =
      let rec print' =
        function
        | nil -> ()
        | (S)::L -> (print (MetaPrint.stateToString S); print' L) in
      print "Open problems:\n";
      print "==============\n\n";
      print' (!openStates);
      print "Solved problems:\n";
      print "================\n\n";
      print' (!solvedStates)
    (* List of open states *)
    (* List of solved states *)
    (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
    (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
    (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
    (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
    (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
    (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
    (* if no termination ordering given! *)
    (* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
    (* makeConDec (name, (G, M), V) = e'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : type
       then e' = (name, |G|, {G}.V, Type) is a signature conDec
    *)
    (* makeSignature (SL) = IS'

       Invariant:
       If   SL is a list of states,
       then IS' is the corresponding interface signaure
    *)
    (* install () = ()

       Invariant:
       Installs solved states into the global signature.
    *)
    (* print () = ()

       Invariant:
       Prints the list of open States and the list of closed states.
    *)
    let print = printState
    let init = init
    let auto = auto
    let install = install
  end ;;
