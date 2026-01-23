module type MTPSTRATEGY  =
  sig
    module StateSyn : STATESYN
    val run :
      StateSyn.state_ list -> (StateSyn.state_ list * StateSyn.state_ list)
  end


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
      if !Global.chatter > 3 then begin print "Strategy\n" end
      else begin () end
  let rec printFilling () =
    if !Global.chatter > 5 then begin print "[Filling ... " end
    else begin if !Global.chatter > 4 then begin print "F" end
      else begin () end end
let rec printRecursion () =
  if !Global.chatter > 5 then begin print "[Recursion ..." end
  else begin if !Global.chatter > 4 then begin print "R" end
    else begin () end end
let rec printInference () =
  if !Global.chatter > 5 then begin print "[Inference ..." end
  else begin if !Global.chatter > 4 then begin print "I" end
    else begin () end end
let rec printSplitting splitOp =
  if !Global.chatter > 5 then begin print "[Splitting ..." end
  else begin if !Global.chatter > 4 then begin print "S" end
    else begin () end end(* if !Global.chatter > 5 then print ("[" ^ MTPSplitting.menu splitOp) *)
let rec printCloseBracket () =
  if !Global.chatter > 5 then begin print "]\n" end else begin () end
let rec printQed () =
  begin if !Global.chatter > 3 then begin print "[QED]\n" end
  else begin () end;
  if !Global.chatter > 4
  then
    begin print
            (("Statistics: required Twelf.Prover.maxFill := " ^
                (Int.toString !MTPData.maxFill))
               ^ "\n") end
  else begin () end end
let rec findMin =
  begin function
  | [] -> None
  | l_ ->
      let rec findMin' =
        begin function
        | ([], result) -> result
        | ((o'_)::l'_, None) ->
            if MTPSplitting.applicable o'_
            then begin findMin' (l'_, (Some o'_)) end
            else begin findMin' (l'_, None) end
        | ((o'_)::l'_, Some (o_)) ->
            if MTPSplitting.applicable o'_
            then
              begin (begin match MTPSplitting.compare (o'_, o_) with
                     | LESS -> findMin' (l'_, (Some o'_))
                     | _ -> findMin' (l'_, (Some o_)) end) end
        else begin findMin' (l'_, (Some o_)) end end in
findMin' (l_, None) end
let rec split ((s_)::givenStates, ((openStates, solvedStates) as os)) =
  begin match findMin (Timers.time Timers.splitting MTPSplitting.expand s_)
        with
  | None -> fill (givenStates, ((s_ :: openStates), solvedStates))
  | Some splitOp ->
      let _ = printSplitting splitOp in
      let SL = Timers.time Timers.splitting MTPSplitting.apply splitOp in
      let _ = printCloseBracket () in
      let _ = printRecursion () in
      let SL' =
        map
          (begin function
           | s_ ->
               Timers.time Timers.recursion MTPRecursion.apply
                 (MTPRecursion.expand s_) end)
        SL in
      let _ = printInference () in
      let SL'' =
        map
          (begin function
           | s_ ->
               Timers.time Timers.inference Inference.apply
                 (Inference.expand s_) end)
        SL' in
      fill ((SL'' @ givenStates), os) end
let rec fill =
  begin function
  | ([], os) -> os
  | ((s_)::givenStates, ((openStates, solvedStates) as os)) ->
      (begin match Timers.time Timers.recursion MTPFilling.expand s_ with
       | fillingOp ->
           (begin try
                    let _ = printFilling () in
                    let (max, p_) =
                      TimeLimit.timeLimit !Global.timeLimit
                        (Timers.time Timers.filling MTPFilling.apply)
                        fillingOp in
                    let _ = printCloseBracket () in fill (givenStates, os)
            with | Error _ -> split ((s_ :: givenStates), os) end) end) end
let rec run givenStates =
  let _ = printInit () in
  let (openStates, solvedStates) = fill (givenStates, ([], [])) in
  let openStates' = map MTPrint.nameState openStates in
  let solvedStates' = map MTPrint.nameState solvedStates in
  let _ = begin match openStates with | [] -> printQed () | _ -> () end in
  (openStates', solvedStates')
let run = run end
