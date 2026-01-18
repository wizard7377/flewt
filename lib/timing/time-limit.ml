
(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 * Modified: Brigitte Pientka
 *)
module TimeLimit :
  sig
    exception TimeOut 
    val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end =
  struct
    exception TimeOut 
    let rec timeLimit arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (NONE, f, x) -> f x
      | (SOME t, f, x) ->
          let _ = print (((^) "TIME LIMIT : " Time.toString t) ^ "sec \n") in
          let setitimer = SMLofNJ.IntervalTimer.setIntTimer in
          let rec timerOn () = ignore (setitimer (SOME t)) in
          let rec timerOff () = ignore (setitimer NONE) in
          let escapeCont =
            SMLofNJ.Cont.callcc
              (function
               | k ->
                   (SMLofNJ.Cont.callcc
                      (function | k' -> SMLofNJ.Cont.throw k k');
                    timerOff ();
                    raise TimeOut)) in
          let rec handler _ = escapeCont in
          (Signals.setHandler (Signals.sigALRM, (Signals.HANDLER handler));
           timerOn ();
           ((try f x with | ex -> (timerOff (); raise ex))) before timerOff
             ())
  end ;;
