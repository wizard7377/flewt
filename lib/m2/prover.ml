
module type PROVER  =
  sig
    exception Error of string 
    val init : int -> IntSyn.cid list -> unit
    val auto : unit -> unit
    val print : unit -> unit
    val install : (IntSyn.__ConDec -> IntSyn.cid) -> unit
  end;;




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
    let (openStates : MetaSyn.__State list ref) = ref nil
    let (solvedStates : MetaSyn.__State list ref) = ref nil
    let rec error s = raise (Error s)
    let rec reset () = openStates := nil; solvedStates := nil
    let rec contains __0__ __1__ =
      match (__0__, __1__) with
      | (nil, _) -> true
      | (x::__L, __L') ->
          (List.exists (fun x' -> x = x') __L') && (contains (__L, __L'))
    let rec equiv (__L1) (__L2) =
      (contains (__L1, __L2)) && (contains (__L2, __L1))
    let rec insertState (__S) =
      if Qed.subgoal __S
      then (solvedStates := __S) :: (!solvedStates)
      else (openStates := __S) :: (!openStates)
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::__L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __L)
    let rec init k (c::_ as cL) =
      let _ = MetaGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      ((if equiv (cL, cL')
        then List.app (fun (__S) -> insertState __S) (Init.init cL)
        else
          raise
            (Error
               (("Theorem by simultaneous induction not correctly stated:" ^
                   "\n            expected: ")
                  ^ (cLToString cL'))))
        (* if no termination ordering given! *))
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
    let rec makeConDec (State (name, Prefix (__G, __M, __B), __V)) =
      let rec makeConDec' __2__ __3__ __4__ =
        match (__2__, __3__, __4__) with
        | (I.Null, __V, k) -> I.ConDec (name, None, k, I.Normal, __V, I.Type)
        | (Decl (__G, __D), __V, k) ->
            makeConDec' (__G, (I.Pi ((__D, I.Maybe), __V)), (k + 1)) in
      makeConDec' (__G, __V, 0)
    let rec makeSignature =
      function
      | nil -> M.SgnEmpty
      | (__S)::SL -> M.ConDec ((makeConDec __S), (makeSignature SL))
    let rec install installConDec =
      let rec install' =
        function
        | M.SgnEmpty -> ()
        | ConDec (e, __S) -> (installConDec e; install' __S) in
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
        | (__S)::__L -> (print (MetaPrint.stateToString __S); print' __L) in
      print "Open problems:\n";
      print "==============\n\n";
      print' (!openStates);
      print "Solved problems:\n";
      print "================\n\n";
      print' (!solvedStates)
    let print = printState
    let init = init
    let auto = auto
    let install = install
  end ;;
