module type TIMERS  =
  sig
    val checking : Timing.center
    val eta_normal : Timing.center
    val printing : Timing.center
    val translation : Timing.center
    val total : Timing.sum
    val time : Timing.center -> ('a -> 'b) -> 'a -> 'b
    val reset : unit -> unit
    val check : unit -> unit
    val show : unit -> unit
  end


module Timers : TIMERS =
  struct
    let (centers : Timing.center list ref) = ref []
    let rec add_timer name =
      let center = Timing.newCenter name in
      begin ((!) ((:=) centers) centers) @ [center]; center end
    let checking = add_timer "Checking      "
    let eta_normal = add_timer "Eta Normal    "
    let printing = add_timer "Printing      "
    let translation = add_timer "Translation   "
    let total = Timing.sumCenter ("Total         ", !centers)
    let time = Timing.time
    let rec reset () = List.app Timing.reset !centers
    let rec check () =
      begin List.app (print o Timing.toString) !centers;
      print (Timing.sumToString total) end
  let rec show () = begin check (); reset () end end
