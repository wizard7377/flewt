
module type TIMERS  =
  sig
    (* Programming interface *)
    val checking : Timing.center
    (* redundant type-checking *)
    val eta_normal : Timing.center
    (* redundant type-checking *)
    val printing : Timing.center
    (* printing *)
    val translation : Timing.center
    (* printing *)
    val total : Timing.sum
    (* total time *)
    (* time center f x = y
     if f x = y and time of computing f x is added to center.
     If f x raises an exception, it is re-raised.
  *)
    val time : Timing.center -> ('a -> 'b) -> 'a -> 'b
    (* External interface *)
    val reset : unit -> unit
    (* reset above centers *)
    val check : unit -> unit
    (* check timer values *)
    val show : unit -> unit
  end;;




module Timers : TIMERS =
  struct
    let (centers : Timing.center list ref) = ref []
    let rec add_timer name =
      let center = Timing.newCenter name in
      ((!) ((:=) centers) centers) @ [center]; center
    let checking = add_timer "Checking      "
    let eta_normal = add_timer "Eta Normal    "
    let printing = add_timer "Printing      "
    let translation = add_timer "Translation   "
    let total = Timing.sumCenter ("Total         ", (!centers))
    let time = Timing.time
    let rec reset () = List.app Timing.reset (!centers)
    let rec check () =
      List.app (print o Timing.toString) (!centers);
      print (Timing.sumToString total)
    let rec show () = check (); reset ()
  end ;;
