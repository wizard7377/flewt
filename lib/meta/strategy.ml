
module type MTPSTRATEGY  =
  sig
    module StateSyn : STATESYN
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
                                 module Timers : TIMERS
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
      else if (!Global.chatter) > 4 then print "S" else ()(* if !Global.chatter > 5 then print ("[" ^ MTPSplitting.menu splitOp) *)
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
      | nil -> None
      | __L ->
          let rec findMin' __0__ __1__ =
            match (__0__, __1__) with
            | (nil, result) -> result
            | ((__O')::__L', None) ->
                if MTPSplitting.applicable __O'
                then findMin' (__L', (Some __O'))
                else findMin' (__L', None)
            | ((__O')::__L', Some (__O)) ->
                if MTPSplitting.applicable __O'
                then
                  (match MTPSplitting.compare (__O', __O) with
                   | LESS -> findMin' (__L', (Some __O'))
                   | _ -> findMin' (__L', (Some __O)))
                else findMin' (__L', (Some __O)) in
          findMin' (__L, None)
    let rec split ((__S)::givenStates) ((openStates, solvedStates) as os) =
      match findMin (Timers.time Timers.splitting MTPSplitting.expand __S)
      with
      | None -> fill (givenStates, ((__S :: openStates), solvedStates))
      | Some splitOp ->
          let _ = printSplitting splitOp in
          let SL = Timers.time Timers.splitting MTPSplitting.apply splitOp in
          let _ = printCloseBracket () in
          let _ = printRecursion () in
          let SL' =
            map
              (fun (__S) ->
                 Timers.time Timers.recursion MTPRecursion.apply
                   (MTPRecursion.expand __S)) SL in
          let _ = printInference () in
          let SL'' =
            map
              (fun (__S) ->
                 Timers.time Timers.inference Inference.apply
                   (Inference.expand __S)) SL' in
          fill ((SL'' @ givenStates), os)
    let rec fill __2__ __3__ =
      match (__2__, __3__) with
      | (nil, os) -> os
      | ((__S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.recursion MTPFilling.expand __S with
           | fillingOp ->
               (try
                  let _ = printFilling () in
                  let (max, __P) =
                    TimeLimit.timeLimit (!Global.timeLimit)
                      (Timers.time Timers.filling MTPFilling.apply) fillingOp in
                  let _ = printCloseBracket () in fill (givenStates, os)
                with | Error _ -> split ((__S :: givenStates), os)))
    let rec run givenStates =
      let _ = printInit () in
      let (openStates, solvedStates) = fill (givenStates, (nil, nil)) in
      let openStates' = map MTPrint.nameState openStates in
      let solvedStates' = map MTPrint.nameState solvedStates in
      let _ = match openStates with | nil -> printQed () | _ -> () in
      (openStates', solvedStates')
    let run = run
  end ;;
