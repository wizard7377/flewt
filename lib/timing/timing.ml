
module type TIMING  =
  sig
    val init : unit -> unit
    type nonrec center
    val newCenter : string -> center
    val reset : center -> unit
    val time : center -> ('a -> 'b) -> 'a -> 'b
    type nonrec sum
    val sumCenter : (string * center list) -> sum
    val toString : center -> string
    val sumToString : sum -> string
  end
module Timing : TIMING =
  struct
    type nonrec cpuTime =
      <
        usr: ((Time.time)(* gc time is a portion of the total CPU time devoted to garbage collection *)
          (* user and system time add up to total CPU time used *)
          (* signature TIMING *)(*
   For documentation on timers and time, see also the
   SML'97 Standard Library structures Time and Timer

   In saved heaps in SML of NJ, a global timer must
   be initialized, otherwise exception Time.Time is raised
   somewhere.
*)
          (* Author: Frank Pfenning *)(* Timing utilities based on SML'97 Standard Library *))
           ;sys: Time.time  ;gc: Time.time   > 
    type nonrec realTime = Time.time
    let rec init () = ()
    type 'a result =
      | Value of 'a 
      | Exception of exn 
    type nonrec center = (string * (cpuTime * realTime) ref)
    type nonrec sum = (string * center list)
    let zero =
      { usr = Time.zeroTime; sys = Time.zeroTime; gc = Time.zeroTime }
    let rec minus
      ({ usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 },
       { usr = s1; sys = s2; gc = s3; sys = s2; gc = s3; gc = s3 })
      =
      {
        usr = (Time.(-) (t1, s1));
        sys = (Time.(-) (t2, s2));
        gc = (Time.(-) (t3, s3))
      }
    let rec plus
      ({ usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 },
       { usr = s1; sys = s2; gc = s3; sys = s2; gc = s3; gc = s3 })
      =
      {
        usr = (Time.(+) (t1, s1));
        sys = (Time.(+) (t2, s2));
        gc = (Time.(+) (t3, s3))
      }
    let rec sum { usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 } =
      Time.(+) (t1, t2)
    let rec newCenter
      ((name)(* We use only one global timer each for CPU time and real time *)
      (* val CPUTimer = Timer.startCPUTimer () *)(* val realTimer = Timer.startRealTimer () *)
      (* newCenter (name) = new center, initialized to 0 *))
      = (name, (ref (zero, Time.zeroTime)))
    let rec reset
      (((_)(* reset (center) = (), reset center to 0 as effect *)),
       counters)
      = counters := (zero, Time.zeroTime)
    let rec checkCPUAndGCTimer
      ((timer)(* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for those will be counted twice!
    *))
      =
      let { usr; sys; sys } = Compat.Timer.checkCPUTimer timer in
      let gc = Compat.Timer.checkGCTime timer in { usr; sys; gc }
    let rec time (_, counters) (f : 'a -> 'b) (x : 'a) =
      let realTimer = Timer.startRealTimer () in
      let CPUTimer = Timer.startCPUTimer () in
      let result = try Value (f x) with | exn -> Exception exn in
      let evalCPUTime = checkCPUAndGCTimer CPUTimer in
      let evalRealTime = Timer.checkRealTimer realTimer in
      let (CPUTime, realTime) = !counters in
      let _ =
        counters :=
          ((plus (CPUTime, evalCPUTime)),
            (Time.(+) (realTime, evalRealTime))) in
      match result with | Value v -> v | Exception e -> raise e
    let rec sumCenter
      (((name)(* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)),
       l)
      = (name, l)
    let rec stdTime (n, time) = StringCvt.padLeft ' ' n (Time.toString time)
    let rec timesToString
      (name,
       (({ usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 } as
           CPUTime),
        realTime))
      =
      (((^) (((^) ((((^) ((((^) ((name ^ ": ") ^ "Real = ") stdTime
                              (7, realTime))
                             ^ ", ")
                            ^ "Run = ")
                       stdTime (7, (sum CPUTime)))
                      ^ " ")
                     ^ "(")
                stdTime (7, t1))
               ^ " usr, ")
          ((stdTime)
          (* ^ stdTime (5, t2) ^ " sys, " ^ *)(* elide sys time *))
          (6, t3))
         ^ " gc)")
        ^ "\n"
    let rec toString (name, ref (CPUTime, realTime)) =
      timesToString (name, (CPUTime, realTime))
    let rec sumToString (name, centers) =
      let sumup =
        function
        | (nil, (CPUTime, realTime)) ->
            timesToString (name, (CPUTime, realTime))
        | ((_, ref (C, R))::centers, (CPUTime, realTime)) ->
            sumup (centers, ((plus (CPUTime, C)), (Time.(+) (realTime, R)))) in
      sumup (centers, (zero, Time.zeroTime))
  end 
module Counting : TIMING =
  struct
    type 'a result =
      | Value of
      (('a)(* passed as a paramter to Timers *)(* Unused in the default linking, but could be *)
      (* This version only counts, but does not time *)
      (* structure Timing *)(* local ... *))
      
      | Exception of exn 
    type nonrec center = (string * int ref)
    type nonrec sum = (string * center list)
    let rec init () = ()
    let rec newCenter name = (name, (ref 0))
    let rec reset (_, counters) = counters := 0
    let rec time (_, counters) (f : 'a -> 'b) (x : 'a) =
      let _ = ((!) ((:=) counters) counters) + 1 in f x
    let rec sumCenter (name, l) = (name, l)
    let rec toString' (name, n) = ((^) (name ^ ": ") Int.toString n) ^ "\n"
    let rec toString (name, ref n) = toString' (name, n)
    let rec sumToString (name, centers) =
      let sumup =
        function
        | (nil, total) -> toString' (name, total)
        | ((_, ref n)::centers, total) -> sumup (centers, (total + n)) in
      sumup (centers, 0)
  end ;;
