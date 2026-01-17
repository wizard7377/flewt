
module TimeLimit : TIME_LIMIT =
  struct
    exception TimeOut (* Other implementations possible via ALRM signal? *)
    (* SML/NJ implementation of timeLimit *)
    let rec timeLimit arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (NONE, f, x) -> f x
      | (SOME t, f, x) ->
          let _ = print (((^) "TIME LIMIT : " Time.toString t) ^ "sec \n") in
          let setitimer = SMLofNJ.IntervalTimer.setIntTimer in
          let timerOn () = ignore (setitimer (SOME t)) in
          let timerOff () = ignore (setitimer NONE) in
          let escapeCont =
            SMLofNJ.Cont.callcc
              (function
               | k ->
                   (SMLofNJ.Cont.callcc
                      (function | k' -> SMLofNJ.Cont.throw k k');
                    timerOff ();
                    raise TimeOut)) in
          let handler _ = escapeCont in
          (Signals.setHandler (Signals.sigALRM, (Signals.HANDLER handler));
           timerOn ();
           ((try f x with | ex -> (timerOff (); raise ex))) before timerOff
             ())
  end ;;
