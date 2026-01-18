
(* Strategy *)
(* Author: Carsten Schuermann *)
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
      | (O)::__l ->
          let rec findMin' =
            function
            | (nil, k, result) -> result
            | ((O')::__l', k, result) ->
                let k' = Splitting.index O' in
                if (Splitting.index O') < k
                then findMin' (__l', k', (Some O'))
                else findMin' (__l', k, result) in
          findMin' (__l, (Splitting.index O), (Some O))
    let rec split ((S)::givenStates, ((openStates, solvedStates) as os)) =
      match findMin (Timers.time Timers.splitting Splitting.expand S) with
      | None -> fill (givenStates, ((S :: openStates), solvedStates))
      | Some splitOp ->
          let _ = printSplitting () in
          let SL = Timers.time Timers.splitting Splitting.apply splitOp in
          let _ = printCloseBracket () in
          (try fill ((SL @ givenStates), os)
           with
           | Error _ -> fill (givenStates, ((S :: openStates), solvedStates)))
    let rec recurse ((S)::givenStates, ((openStates, solvedStates) as os)) =
      match Timers.time Timers.recursion Recursion.expandEager S with
      | nil -> split ((S :: givenStates), os)
      | recursionOp::_ ->
          let _ = printRecursion () in
          let S' = Timers.time Timers.recursion Recursion.apply recursionOp in
          let _ = printCloseBracket () in
          (try fill ((S' :: givenStates), (openStates, solvedStates))
           with | Error _ -> split ((S :: givenStates), os))
    let rec fill =
      function
      | (nil, os) -> os
      | ((S)::givenStates, ((openStates, solvedStates) as os)) ->
          let rec fillOp () =
            match Timers.time Timers.filling Filling.expand S with
            | (_, fillingOp) ->
                (try
                   let _ = printFilling () in
                   let (S')::[] =
                     Timers.time Timers.filling Filling.apply fillingOp in
                   let _ = printCloseBracket () in
                   if Qed.subgoal S'
                   then
                     (printFinish S';
                      fill (givenStates, (openStates, (S' :: solvedStates))))
                   else fill ((S' :: givenStates), os)
                 with | Error _ -> recurse ((S :: givenStates), os)) in
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
      | (O)::__l ->
          let rec findMin' =
            function
            | (nil, k, result) -> result
            | ((O')::__l', k, result) ->
                let k' = Splitting.index O' in
                if (Splitting.index O') < k
                then findMin' (__l', k', (Some O'))
                else findMin' (__l', k, result) in
          findMin' (__l, (Splitting.index O), (Some O))
    let rec split ((S)::givenStates, ((openStates, solvedStates) as os)) =
      match findMin (Timers.time Timers.splitting Splitting.expand S) with
      | None -> recurse (givenStates, ((S :: openStates), solvedStates))
      | Some splitOp ->
          let _ = printSplitting () in
          let SL = Timers.time Timers.splitting Splitting.apply splitOp in
          let _ = printCloseBracket () in
          (try recurse ((SL @ givenStates), os)
           with
           | Error _ ->
               recurse (givenStates, ((S :: openStates), solvedStates)))
    let rec fill =
      function
      | (nil, os) -> os
      | ((S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.filling Filling.expand S with
           | (_, fillingOp) ->
               (try
                  let _ = printFilling () in
                  let (S')::[] =
                    Timers.time Timers.filling Filling.apply fillingOp in
                  let _ = printCloseBracket () in
                  if Qed.subgoal S'
                  then
                    (printFinish S';
                     recurse
                       (givenStates, (openStates, (S' :: solvedStates))))
                  else fill ((S' :: givenStates), os)
                with | Error _ -> split ((S :: givenStates), os)))
    let rec recurse =
      function
      | (nil, os) -> os
      | ((S)::givenStates, ((openStates, solvedStates) as os)) ->
          (match Timers.time Timers.recursion Recursion.expandEager S with
           | nil -> fill ((S :: givenStates), os)
           | recursionOp::_ ->
               let _ = printRecursion () in
               let S' =
                 Timers.time Timers.recursion Recursion.apply recursionOp in
               let _ = printCloseBracket () in
               (try recurse ((S' :: givenStates), (openStates, solvedStates))
                with | Error _ -> fill ((S :: givenStates), os)))
    let rec run givenStates =
      let _ = printInit () in
      let os = recurse (givenStates, (nil, nil)) in
      let _ = match os with | (nil, _) -> printQed () | _ -> () in os
    let run = run
  end  (* Strategy *)
(* Author: Carsten Schuermann *)
(* findMin __l = Sopt

       Invariant:

       If   __l be a set of splitting operators
       then Sopt = None if __l = []
       else Sopt = Some S, s.t. index S is minimal among all elements in __l
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
(* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
(* local *) (* functor StrategyFRS *)
(* findMin __l = Sopt

       Invariant:

       If   __l be a set of splitting operators
       then Sopt = None if __l = []
       else Sopt = Some S, s.t. index S is minimal among all elements in __l
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
(* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
(* local *) (* functor StrategyRFS *)
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
