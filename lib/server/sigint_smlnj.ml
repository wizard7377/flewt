
module SigINT : SIGINT =
  struct
    let rec interruptLoop loop =
      SMLofNJ.Cont.callcc
        (fun k ->
           Signals.setHandler
             (Signals.sigINT,
               (Signals.HANDLER (fun _ -> print "\ninterrupt\n"; k)));
           ());
      loop ()
  end ;;
