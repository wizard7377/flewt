module TimeLimit : TIME_LIMIT =
  struct
    exception TimeOut 
    let rec timeLimit arg__0 arg__1 arg__2 =
      begin match (arg__0, arg__1, arg__2) with
      | (None, f, x) -> f x
      | (Some t, f, x) ->
          let _ = print (((^) "TIME LIMIT : " Time.toString t) ^ "sec \n") in
          let setitimer = SMLofNJ.IntervalTimer.setIntTimer in
          let rec timerOn () = ignore (setitimer (Some t)) in
          let rec timerOff () = ignore (setitimer None) in
          let escapeCont =
            SMLofNJ.Cont.callcc
              (begin function
               | k ->
                   (begin SMLofNJ.Cont.callcc
                            (begin function | k' -> SMLofNJ.Cont.throw k k' end);
                   timerOff (); raise TimeOut end) end) in
          let rec handler _ = escapeCont in
          (begin Signals.setHandler
                   (Signals.sigALRM, (Signals.HANDLER handler));
           timerOn ();
           ((begin try f x with | ex -> (begin timerOff (); raise ex end) end))
            before timerOff () end) end end
