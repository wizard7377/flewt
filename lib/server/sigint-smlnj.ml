
module SigINT : SIGINT =
  struct
    let rec interruptLoop (loop : unit -> unit) =
      SMLofNJ.Cont.callcc
        (function
         | k ->
             (Signals.setHandler
                (Signals.sigINT,
                  (Signals.HANDLER
                     (function | _ -> (print "\ninterrupt\n"; k))));
              ()));
      loop ()
  end ;;
