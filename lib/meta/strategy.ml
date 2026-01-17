
module type MTPSTRATEGY  =
  sig
    module StateSyn :
    ((STATESYN)(* MTPStrategy : Version 1.3 *)(* Author: Carsten Schuermann *))
    val run :
      StateSyn.__State list ->
        (StateSyn.__State list * StateSyn.__State list)
  end;;




module MTPStrategy(MTPStrategy:sig
                                 module MTPGlobal : MTPGLOBAL
                                 module StateSyn' : STATESYN
                                 module MTPFilling : MTPFILLING
                                 module MTPData : MTPDATA
                                 module MTPSplitting : MTPSPLITTING
                                 module MTPRecursion : MTPRECURSION
                                 module Inference : INFERENCE
                                 module MTPrint : MTPRINT
                                 module Timers :
                                 ((TIMERS)(* MTP Strategy: Version 1.3 *)
                                 (* Author: Carsten Schuermann *))
                               end) : MTPSTRATEGY =
  struct
    module StateSyn = StateSyn'
    module S = StateSyn
    let rec printInit () =
      if (!Global.chatter) > 3 then print "Strategy\n" else ()
    let rec printFilling () =
      if (!Global.chatter) > 5
      then print "[Filling ... "
      else if (!Global.chatter) > 4 then print "F" else ()
    let rec printRecursion () =
      if (!Global.chatter) > 5
      then print "[Recursion ..."
      else if (!Global.chatter) > 4 then print "R" else ()
    let rec printInference () =
      if (!Global.chatter) > 5
      then print "[Inference ..."
      else if (!Global.chatter) > 4 then print "I" else ()
    let rec printSplitting splitOp =
      if (!Global.chatter) > 5
      then print "[Splitting ..."
      else if (!Global.chatter) > 4 then print "S" else ()
    let rec printCloseBracket () =
      if (!Global.chatter) > 5 then print "]\n" else ()
    let rec printQed () =
      if (!Global.chatter) > 3 then print "[QED]\n" else ();
      if (!Global.chatter) > 4
      then
        print
          (("Statistics: required Twelf.Prover.maxFill := " ^
              (Int.toString (!MTPData.maxFill)))
             ^ "\n")
      else ()
    let rec findMin =
      function
      | nil -> NONE
      | L ->
          let findMin' =
            function
            | (nil, result) -> result
            | ((O')::L', NONE) ->
                if MTPSplitting.applicable O'
                then findMin' (L', (SOME O'))
                else findMin' (L', NONE)
            | ((O')::L', SOME (O)) ->
                if MTPSplitting.applicable O'
                then
                  (match MTPSplitting.compare (O', O) with
                   | LESS -> findMin' (L', (SOME O'))
                   | _ -> findMin' (L', (SOME O)))
                else findMin' (L', (SOME O)) in
          findMin' (L, NONE)
    let rec split ((S)::givenStates, ((openStates, solvedStates) as os)) =
      match findMin (Timers.time Timers.splitting MTPSplitting.expand S) with
      | NONE -> fill (givenStates, ((S :: openStates), solvedStates))
      | SOME splitOp ->
          let _ = printSplitting splitOp in
          let SL = Timers.time Timers.splitting MTPSplitting.apply splitOp in
          let _ = printCloseBracket () in
          let _ = printRecursion () in
          let SL' =
            map
              (function
               | S ->
                   Timers.time Timers.recursion MTPRecursion.apply
                     (MTPRecursion.expand S)) SL in
          let _ = printInference () in
          let SL'' =
            map
              (function
               | S ->
                   Timers.time Timers.inference Inference.apply
                     (Inference.expand S)) SL' in
          fill ((SL'' @ givenStates), os)
    let rec fill =
      function
      | (nil, os) -> os
      | ((S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.recursion MTPFilling.expand S with
           | fillingOp ->
               (try
                  let _ = printFilling () in
                  let (max, P) =
                    TimeLimit.timeLimit (!Global.timeLimit)
                      (Timers.time Timers.filling MTPFilling.apply) fillingOp in
                  let _ = printCloseBracket () in fill (givenStates, os)
                with | Error _ -> split ((S :: givenStates), os)))
    let rec run givenStates =
      let _ = printInit () in
      let (openStates, solvedStates) = fill (givenStates, (nil, nil)) in
      let openStates' = map MTPrint.nameState openStates in
      let solvedStates' = map MTPrint.nameState solvedStates in
      let _ = match openStates with | nil -> printQed () | _ -> () in
      (openStates', solvedStates')
    let ((run)(* if !Global.chatter > 5 then print ("[" ^ MTPSplitting.menu splitOp) *)
      (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
      (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
      (* Note: calling splitting in case filling fails, may cause the prover to succeed
              if there are no cases to split -- however this may in fact be wrong -bp*)
      (* for comparing depth-first search (logic programming) with iterative deepening search
              in the meta-theorem prover, we must disallow splitting :

                handle TimeLimit.TimeOut =>  raise Filling.Error "Time Out: Time limit exceeded\n"
                handle MTPFilling.Error msg =>  raise Filling.Error msg
                  ) handle MTPFilling.Error msg =>  raise Filling.Error msg
            *)
      (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *))
      = run
  end ;;
