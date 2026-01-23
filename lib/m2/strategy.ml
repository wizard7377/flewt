module type STRATEGY  =
  sig
    module MetaSyn : METASYN
    val run :
      MetaSyn.state_ list -> (MetaSyn.state_ list * MetaSyn.state_ list)
  end


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
      if !Global.chatter > 3 then begin print "Strategy 1.0: FRS\n" end
      else begin () end
  let rec printFinish (State (name, _, _)) =
    if !Global.chatter > 5
    then begin print (("[Finished: " ^ name) ^ "]\n") end
    else begin
      if !Global.chatter > 4 then begin print (("[" ^ name) ^ "]\n") end
      else begin
        if !Global.chatter > 3 then begin print (("[" ^ name) ^ "]") end
        else begin () end end end
let rec printFilling () =
  if !Global.chatter > 5 then begin print "[Filling ... " end
  else begin if !Global.chatter > 4 then begin print "F" end
    else begin () end end
let rec printRecursion () =
  if !Global.chatter > 5 then begin print "[Recursion ..." end
  else begin if !Global.chatter > 4 then begin print "R" end
    else begin () end end
let rec printSplitting () =
  if !Global.chatter > 5 then begin print "[Splitting ..." end
  else begin if !Global.chatter > 4 then begin print "S" end
    else begin () end end
let rec printCloseBracket () =
  if !Global.chatter > 5 then begin print "]\n" end else begin () end
let rec printQed () = if !Global.chatter > 3 then begin print "[QED]\n" end
  else begin () end
let rec findMin =
  begin function
  | [] -> None
  | (o_)::l_ ->
      let rec findMin' =
        begin function
        | ([], k, result) -> result
        | ((o'_)::l'_, k, result) ->
            let k' = Splitting.index o'_ in
            if (Splitting.index o'_) < k
            then begin findMin' (l'_, k', (Some o'_)) end
              else begin findMin' (l'_, k, result) end end in
findMin' (l_, (Splitting.index o_), (Some o_)) end
let rec split ((s_)::givenStates, ((openStates, solvedStates) as os)) =
  begin match findMin (Timers.time Timers.splitting Splitting.expand s_) with
  | None -> fill (givenStates, ((s_ :: openStates), solvedStates))
  | Some splitOp ->
      let _ = printSplitting () in
      let SL = Timers.time Timers.splitting Splitting.apply splitOp in
      let _ = printCloseBracket () in
      (begin try fill ((SL @ givenStates), os)
       with
       | Error _ -> fill (givenStates, ((s_ :: openStates), solvedStates)) end) end
let rec recurse ((s_)::givenStates, ((openStates, solvedStates) as os)) =
  begin match Timers.time Timers.recursion Recursion.expandEager s_ with
  | [] -> split ((s_ :: givenStates), os)
  | recursionOp::_ ->
      let _ = printRecursion () in
      let s'_ = Timers.time Timers.recursion Recursion.apply recursionOp in
      let _ = printCloseBracket () in
      (begin try fill ((s'_ :: givenStates), (openStates, solvedStates))
       with | Error _ -> split ((s_ :: givenStates), os) end) end
let rec fill =
  begin function
  | ([], os) -> os
  | ((s_)::givenStates, ((openStates, solvedStates) as os)) ->
      let rec fillOp () =
        begin match Timers.time Timers.filling Filling.expand s_ with
        | (_, fillingOp) ->
            (begin try
                     let _ = printFilling () in
                     let (s'_)::[] =
                       Timers.time Timers.filling Filling.apply fillingOp in
                     let _ = printCloseBracket () in
                     if Qed.subgoal s'_
                     then
                       begin (begin printFinish s'_;
                              fill
                                (givenStates,
                                  (openStates, (s'_ :: solvedStates))) end) end
                       else begin fill ((s'_ :: givenStates), os) end
        with | Error _ -> recurse ((s_ :: givenStates), os) end) end in
(begin try TimeLimit.timeLimit !Global.timeLimit fillOp ()
with
| TimeLimit.TimeOut ->
   (begin print "\n----------- TIME OUT ---------------\n";
    raise Filling.TimeOut end) end) end
let rec run givenStates =
  let _ = printInit () in
  let os = fill (givenStates, ([], [])) in
  let _ = begin match os with | ([], _) -> printQed () | _ -> () end in os
let run = run end 
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
      if !Global.chatter > 3 then begin print "Strategy 1.0: RFS\n" end
      else begin () end
  let rec printFinish (State (name, _, _)) =
    if !Global.chatter > 5
    then begin print (("[Finished: " ^ name) ^ "]\n") end
    else begin
      if !Global.chatter > 4 then begin print (("[" ^ name) ^ "]\n") end
      else begin
        if !Global.chatter > 3 then begin print (("[" ^ name) ^ "]") end
        else begin () end end end
let rec printFilling () =
  if !Global.chatter > 5 then begin print "[Filling ... " end
  else begin if !Global.chatter > 4 then begin print "F" end
    else begin () end end
let rec printRecursion () =
  if !Global.chatter > 5 then begin print "[Recursion ..." end
  else begin if !Global.chatter > 4 then begin print "R" end
    else begin () end end
let rec printSplitting () =
  if !Global.chatter > 5 then begin print "[Splitting ..." end
  else begin if !Global.chatter > 4 then begin print "S" end
    else begin () end end
let rec printCloseBracket () =
  if !Global.chatter > 5 then begin print "]\n" end else begin () end
let rec printQed () = if !Global.chatter > 3 then begin print "[QED]\n" end
  else begin () end
let rec findMin =
  begin function
  | [] -> None
  | (o_)::l_ ->
      let rec findMin' =
        begin function
        | ([], k, result) -> result
        | ((o'_)::l'_, k, result) ->
            let k' = Splitting.index o'_ in
            if (Splitting.index o'_) < k
            then begin findMin' (l'_, k', (Some o'_)) end
              else begin findMin' (l'_, k, result) end end in
findMin' (l_, (Splitting.index o_), (Some o_)) end
let rec split ((s_)::givenStates, ((openStates, solvedStates) as os)) =
  begin match findMin (Timers.time Timers.splitting Splitting.expand s_) with
  | None -> recurse (givenStates, ((s_ :: openStates), solvedStates))
  | Some splitOp ->
      let _ = printSplitting () in
      let SL = Timers.time Timers.splitting Splitting.apply splitOp in
      let _ = printCloseBracket () in
      (begin try recurse ((SL @ givenStates), os)
       with
       | Error _ -> recurse (givenStates, ((s_ :: openStates), solvedStates)) end) end
let rec fill =
  begin function
  | ([], os) -> os
  | ((s_)::givenStates, ((openStates, solvedStates) as os)) ->
      (begin match Timers.time Timers.filling Filling.expand s_ with
       | (_, fillingOp) ->
           (begin try
                    let _ = printFilling () in
                    let (s'_)::[] =
                      Timers.time Timers.filling Filling.apply fillingOp in
                    let _ = printCloseBracket () in
                    if Qed.subgoal s'_
                    then
                      begin (begin printFinish s'_;
                             recurse
                               (givenStates,
                                 (openStates, (s'_ :: solvedStates))) end) end
                      else begin fill ((s'_ :: givenStates), os) end
      with | Error _ -> split ((s_ :: givenStates), os) end) end) end
let rec recurse =
  begin function
  | ([], os) -> os
  | ((s_)::givenStates, ((openStates, solvedStates) as os)) ->
      (begin match Timers.time Timers.recursion Recursion.expandEager s_ with
       | [] -> fill ((s_ :: givenStates), os)
       | recursionOp::_ ->
           let _ = printRecursion () in
           let s'_ = Timers.time Timers.recursion Recursion.apply recursionOp in
           let _ = printCloseBracket () in
           (begin try
                    recurse
                      ((s'_ :: givenStates), (openStates, solvedStates))
            with | Error _ -> fill ((s_ :: givenStates), os) end) end) end
let rec run givenStates =
  let _ = printInit () in
  let os = recurse (givenStates, ([], [])) in
  let _ = begin match os with | ([], _) -> printQed () | _ -> () end in os
let run = run end 
module Strategy(Strategy:sig
                           module MetaGlobal : METAGLOBAL
                           module MetaSyn' : METASYN
                           module StrategyFRS : STRATEGY
                           module StrategyRFS : STRATEGY
                         end) : STRATEGY =
  struct
    module MetaSyn = MetaSyn'
    let rec run (SL) =
      begin match !MetaGlobal.strategy with
      | MetaGlobal.RFS -> StrategyRFS.run SL
      | MetaGlobal.FRS -> StrategyFRS.run SL end end
