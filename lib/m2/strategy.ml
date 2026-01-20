
module type STRATEGY  =
  sig
    module MetaSyn : METASYN
    val run :
      MetaSyn.__State list -> (MetaSyn.__State list * MetaSyn.__State list)
  end;;




module StrategyFRS(StrategyFRS:sig
                                 module MetaGlobal : METAGLOBAL
                                 module MetaSyn' : METASYN
                                 module Filling : FILLING
                                 module Splitting : SPLITTING
                                 module Recursion : RECURSION
                                 module Lemma : LEMMA
                                 module Qed : QED
                                 module MetaPrint : METAPRINT
                                 module Timers : TIMERS
                               end) : STRATEGY =
  struct
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    let rec printInit () =
      if (!Global.chatter) > 3 then print "Strategy 1.0: FRS\n" else ()
    let rec printFinish (State (name, _, _)) =
      if (!Global.chatter) > 5
      then print (("[Finished: " ^ name) ^ "]\n")
      else
        if (!Global.chatter) > 4
        then print (("[" ^ name) ^ "]\n")
        else if (!Global.chatter) > 3 then print (("[" ^ name) ^ "]") else ()
    let rec printFilling () =
      if (!Global.chatter) > 5
      then print "[Filling ... "
      else if (!Global.chatter) > 4 then print "F" else ()
    let rec printRecursion () =
      if (!Global.chatter) > 5
      then print "[Recursion ..."
      else if (!Global.chatter) > 4 then print "R" else ()
    let rec printSplitting () =
      if (!Global.chatter) > 5
      then print "[Splitting ..."
      else if (!Global.chatter) > 4 then print "S" else ()
    let rec printCloseBracket () =
      if (!Global.chatter) > 5 then print "]\n" else ()
    let rec printQed () =
      if (!Global.chatter) > 3 then print "[QED]\n" else ()
    let rec findMin =
      function
      | nil -> None
      | (__O)::__L ->
          let rec findMin' __7__ __8__ __9__ =
            match (__7__, __8__, __9__) with
            | (nil, k, result) -> result
            | ((__O')::__L', k, result) ->
                let k' = Splitting.index __O' in
                if (Splitting.index __O') < k
                then findMin' (__L', k', (Some __O'))
                else findMin' (__L', k, result) in
          findMin' (__L, (Splitting.index __O), (Some __O))
    let rec split ((__S)::givenStates) ((openStates, solvedStates) as os) =
      match findMin (Timers.time Timers.splitting Splitting.expand __S) with
      | None -> fill (givenStates, ((__S :: openStates), solvedStates))
      | Some splitOp ->
          let _ = printSplitting () in
          let SL = Timers.time Timers.splitting Splitting.apply splitOp in
          let _ = printCloseBracket () in
          (try fill ((SL @ givenStates), os)
           with
           | Error _ ->
               fill (givenStates, ((__S :: openStates), solvedStates)))
    let rec recurse ((__S)::givenStates) ((openStates, solvedStates) as os) =
      match Timers.time Timers.recursion Recursion.expandEager __S with
      | nil -> split ((__S :: givenStates), os)
      | recursionOp::_ ->
          let _ = printRecursion () in
          let __S' = Timers.time Timers.recursion Recursion.apply recursionOp in
          let _ = printCloseBracket () in
          (try fill ((__S' :: givenStates), (openStates, solvedStates))
           with | Error _ -> split ((__S :: givenStates), os))
    let rec fill __10__ __11__ =
      match (__10__, __11__) with
      | (nil, os) -> os
      | ((__S)::givenStates, ((openStates, solvedStates) as os)) ->
          let rec fillOp () =
            match Timers.time Timers.filling Filling.expand __S with
            | (_, fillingOp) ->
                (try
                   let _ = printFilling () in
                   let (__S')::[] =
                     Timers.time Timers.filling Filling.apply fillingOp in
                   let _ = printCloseBracket () in
                   if Qed.subgoal __S'
                   then
                     (printFinish __S';
                      fill
                        (givenStates, (openStates, (__S' :: solvedStates))))
                   else fill ((__S' :: givenStates), os)
                 with | Error _ -> recurse ((__S :: givenStates), os)) in
          (try TimeLimit.timeLimit (!Global.timeLimit) fillOp ()
           with
           | TimeLimit.TimeOut ->
               (print "\n----------- TIME OUT ---------------\n";
                raise Filling.TimeOut))
    let rec run givenStates =
      let _ = printInit () in
      let os = fill (givenStates, (nil, nil)) in
      let _ = match os with | (nil, _) -> printQed () | _ -> () in os
    let run = run
  end 
module StrategyRFS(StrategyRFS:sig
                                 module MetaGlobal : METAGLOBAL
                                 module MetaSyn' : METASYN
                                 module Filling : FILLING
                                 module Splitting : SPLITTING
                                 module Recursion : RECURSION
                                 module Lemma : LEMMA
                                 module Qed : QED
                                 module MetaPrint : METAPRINT
                                 module Timers : TIMERS
                               end) : STRATEGY =
  struct
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    let rec printInit () =
      if (!Global.chatter) > 3 then print "Strategy 1.0: RFS\n" else ()
    let rec printFinish (State (name, _, _)) =
      if (!Global.chatter) > 5
      then print (("[Finished: " ^ name) ^ "]\n")
      else
        if (!Global.chatter) > 4
        then print (("[" ^ name) ^ "]\n")
        else if (!Global.chatter) > 3 then print (("[" ^ name) ^ "]") else ()
    let rec printFilling () =
      if (!Global.chatter) > 5
      then print "[Filling ... "
      else if (!Global.chatter) > 4 then print "F" else ()
    let rec printRecursion () =
      if (!Global.chatter) > 5
      then print "[Recursion ..."
      else if (!Global.chatter) > 4 then print "R" else ()
    let rec printSplitting () =
      if (!Global.chatter) > 5
      then print "[Splitting ..."
      else if (!Global.chatter) > 4 then print "S" else ()
    let rec printCloseBracket () =
      if (!Global.chatter) > 5 then print "]\n" else ()
    let rec printQed () =
      if (!Global.chatter) > 3 then print "[QED]\n" else ()
    let rec findMin =
      function
      | nil -> None
      | (__O)::__L ->
          let rec findMin' __0__ __1__ __2__ =
            match (__0__, __1__, __2__) with
            | (nil, k, result) -> result
            | ((__O')::__L', k, result) ->
                let k' = Splitting.index __O' in
                if (Splitting.index __O') < k
                then findMin' (__L', k', (Some __O'))
                else findMin' (__L', k, result) in
          findMin' (__L, (Splitting.index __O), (Some __O))
    let rec split ((__S)::givenStates) ((openStates, solvedStates) as os) =
      match findMin (Timers.time Timers.splitting Splitting.expand __S) with
      | None -> recurse (givenStates, ((__S :: openStates), solvedStates))
      | Some splitOp ->
          let _ = printSplitting () in
          let SL = Timers.time Timers.splitting Splitting.apply splitOp in
          let _ = printCloseBracket () in
          (try recurse ((SL @ givenStates), os)
           with
           | Error _ ->
               recurse (givenStates, ((__S :: openStates), solvedStates)))
    let rec fill __3__ __4__ =
      match (__3__, __4__) with
      | (nil, os) -> os
      | ((__S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.filling Filling.expand __S with
           | (_, fillingOp) ->
               (try
                  let _ = printFilling () in
                  let (__S')::[] =
                    Timers.time Timers.filling Filling.apply fillingOp in
                  let _ = printCloseBracket () in
                  if Qed.subgoal __S'
                  then
                    (printFinish __S';
                     recurse
                       (givenStates, (openStates, (__S' :: solvedStates))))
                  else fill ((__S' :: givenStates), os)
                with | Error _ -> split ((__S :: givenStates), os)))
    let rec recurse __5__ __6__ =
      match (__5__, __6__) with
      | (nil, os) -> os
      | ((__S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.recursion Recursion.expandEager __S with
           | nil -> fill ((__S :: givenStates), os)
           | recursionOp::_ ->
               let _ = printRecursion () in
               let __S' =
                 Timers.time Timers.recursion Recursion.apply recursionOp in
               let _ = printCloseBracket () in
               (try
                  recurse ((__S' :: givenStates), (openStates, solvedStates))
                with | Error _ -> fill ((__S :: givenStates), os)))
    let rec run givenStates =
      let _ = printInit () in
      let os = recurse (givenStates, (nil, nil)) in
      let _ = match os with | (nil, _) -> printQed () | _ -> () in os
    let run = run
  end 
module Strategy(Strategy:sig
                           module MetaGlobal : METAGLOBAL
                           module MetaSyn' : METASYN
                           module StrategyFRS : STRATEGY
                           module StrategyRFS : STRATEGY
                         end) : STRATEGY =
  struct
    module MetaSyn = MetaSyn'
    let rec run (SL) =
      match !MetaGlobal.strategy with
      | MetaGlobal.RFS -> StrategyRFS.run SL
      | MetaGlobal.FRS -> StrategyFRS.run SL
  end ;;
