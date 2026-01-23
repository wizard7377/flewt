module SigINT : SIGINT =
  struct
    let rec interruptLoop (loop : unit -> unit) =
      begin SMLofNJ.Cont.callcc
              (begin function
               | k ->
                   (begin Signals.setHandler
                            (Signals.sigINT,
                              (Signals.HANDLER
                                 (begin function
                                  | _ -> (begin print "\ninterrupt\n"; k end) end)));
               () end) end);
    loop () end end
