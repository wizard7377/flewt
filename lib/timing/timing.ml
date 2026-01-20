
module type TIMING  =
  sig
    val init : unit -> unit
    type nonrec center
    val newCenter : string -> center
    val reset : center -> unit
    val time : center -> ('a -> 'b) -> 'a -> 'b
    type nonrec sum
    val sumCenter : string -> center list -> sum
    val toString : center -> string
    val sumToString : sum -> string
  end
module Timing : TIMING =
  struct
    type nonrec cpuTime =
      < usr: Time.time  ;sys: Time.time  ;gc: Time.time   > 
    type nonrec realTime = Time.time
    let rec init () = ()
    type 'a result =
      | Value of 'a 
      | Exception of exn 
    type nonrec center = (string * (cpuTime * realTime) ref)
    type nonrec sum = (string * center list)
    let zero =
      { usr = Time.zeroTime; sys = Time.zeroTime; gc = Time.zeroTime }
    let rec minus { usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 }
      { usr = s1; sys = s2; gc = s3; sys = s2; gc = s3; gc = s3 } =
      {
        usr = (Time.(-) (t1, s1));
        sys = (Time.(-) (t2, s2));
        gc = (Time.(-) (t3, s3))
      }
    let rec plus { usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 }
      { usr = s1; sys = s2; gc = s3; sys = s2; gc = s3; gc = s3 } =
      {
        usr = (Time.(+) (t1, s1));
        sys = (Time.(+) (t2, s2));
        gc = (Time.(+) (t3, s3))
      }
    let rec sum { usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 } =
      Time.(+) (t1, t2)
    let rec newCenter name = (name, (ref (zero, Time.zeroTime)))
    let rec reset _ counters = counters := (zero, Time.zeroTime)
    let rec checkCPUAndGCTimer timer =
      let { usr; sys; sys } = Compat.Timer.checkCPUTimer timer in
      let gc = Compat.Timer.checkGCTime timer in { usr; sys; gc }
    let rec time _ counters f x =
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
    let rec sumCenter name l = (name, l)
    let rec stdTime n time = StringCvt.padLeft ' ' n (Time.toString time)
    let rec timesToString name
      (({ usr = t1; sys = t2; gc = t3; sys = t2; gc = t3; gc = t3 } as
          CPUTime),
       realTime)
      =
      (((((^) (((^) ((((^) ((((^) ((name ^ ": ") ^ "Real = ") stdTime
                                (7, realTime))
                               ^ ", ")
                              ^ "Run = ")
                         stdTime (7, (sum CPUTime)))
                        ^ " ")
                       ^ "(")
                  stdTime (7, t1))
                 ^ " usr, ")
            stdTime (6, t3))
           ^ " gc)")
          ^ "\n")
      (* ^ stdTime (5, t2) ^ " sys, " ^ *)(* elide sys time *))
    let rec toString name { contents = (CPUTime, realTime) } =
      timesToString (name, (CPUTime, realTime))
    let rec sumToString name centers =
      let rec sumup __0__ __1__ =
        match (__0__, __1__) with
        | (nil, (CPUTime, realTime)) ->
            timesToString (name, (CPUTime, realTime))
        | ((_, { contents = (__C, __R) })::centers, (CPUTime, realTime)) ->
            sumup
              (centers, ((plus (CPUTime, __C)), (Time.(+) (realTime, __R)))) in
      sumup (centers, (zero, Time.zeroTime))
  end 
module Counting : TIMING =
  struct
    type 'a result =
      | Value of 'a 
      | Exception of exn 
    type nonrec center = (string * int ref)
    type nonrec sum = (string * center list)
    let rec init () = ()
    let rec newCenter name = (name, (ref 0))
    let rec reset _ counters = counters := 0
    let rec time _ counters f x =
      let _ = ((!) ((:=) counters) counters) + 1 in f x
    let rec sumCenter name l = (name, l)
    let rec toString' name n = ((^) (name ^ ": ") Int.toString n) ^ "\n"
    let rec toString name { contents = n } = toString' (name, n)
    let rec sumToString name centers =
      let rec sumup __2__ __3__ =
        match (__2__, __3__) with
        | (nil, total) -> toString' (name, total)
        | ((_, { contents = n })::centers, total) ->
            sumup (centers, (total + n)) in
      sumup (centers, 0)
  end ;;
