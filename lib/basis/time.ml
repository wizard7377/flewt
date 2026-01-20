open StringCvt
module type TIME  =
  sig
    type nonrec time
    exception Time 
    val (+) : time -> time -> time
    val (-) : time -> time -> time
    val (<) : time -> time -> bool
    val (<=) : time -> time -> bool
    val (>) : time -> time -> bool
    val (>=) : time -> time -> bool
    val compare : time -> time -> int
    val fmt : int -> time -> string
    val fromMicroseconds : Int.t -> time
    val fromMilliseconds : Int.t -> time
    val fromNanoseconds : Int.t -> time
    val fromReal : float -> time
    val fromSeconds : Int.t -> time
    val fromString : string -> time option
    val now : unit -> time
    val scan : (char, 'a) StringCvt.reader -> (time, 'a) StringCvt.reader
    val toMicroseconds : time -> Int.t
    val toMilliseconds : time -> Int.t
    val toNanoseconds : time -> Int.t
    val toReal : time -> float
    val toSeconds : time -> Int.t
    val toString : time -> string
    val zeroTime : time
  end





module Time : TIME =
  struct


    type time =
      | T of Int.t 
    let ticksPerSecond = 10000000
    exception Time 
    let zeroTime = T 0
    let rec fromReal r =
      try
        T
          (Float.to_int
             ( (r *. (Float.of_int ticksPerSecond))))
      with | _ -> raise Time
    let rec toReal (T i) =
        ((Float.of_int i) /. (Float.of_int ticksPerSecond))
    let rec make ticksPer =
      let d = ( / ) (ticksPerSecond) (ticksPer) in
      ((fun i -> T ( (i * d))),
        (fun (T i) -> (i / d)))
    let (fromSeconds, toSeconds) = make 1
    let (fromMilliseconds, toMilliseconds) = make 1000
    let (fromMicroseconds, toMicroseconds) = make 1000000
    let (fromNanoseconds, toNanoseconds) = make 1000000000
    let rec make f (T i) (T i') = f i i'
    let compare = make Int.compare
    let (<) = make (<)
    let (<=) = make (<=)
    let (>) = make (>)
    let (>=) = make (>=)
    let rec make f (T i) (T i') = T (f i i')
    let timeAdd = make (+)
    let timeSub = make (-) 
    let rec getNow () = assert false (*
      (let sec = ref (Ptime.castFromFixedInt 0) in
       let usec = ref (C_SUSeconds.castFromFixedInt 0) in
       if (=) (-1) Prim.getTimeOfDay (sec, usec)
       then raise (Fail "Time.now")
       else
         timeAdd
           ((fromSeconds (C_Time.toLargeInt (!sec))),
             (fromMicroseconds (C_SUSeconds.toLargeInt (!usec)))) : time) *)
    let prev = ref (getNow ())
    let rec now () =
      (let old = !prev in
       let t = getNow () in
       match compare old t with | 1 -> old | _ -> (prev := t; t) : 
      time)
    let (fmt : int -> time -> string) =
      fun n t -> Printf.sprintf "%.*f" n (toReal t)
    let toString = fmt 3
    let rec scan getc src =
        let charToDigit = StringCvt.charToDigit StringCvt.DEC in
        let isDigit c = Stdlib.(>=) c '0' && Stdlib.(<=) c '9' in
        let rec pow10 = function | 0 -> 1 | n -> 10 * pow10 (n - 1) in
        let rec mkTime sign intv fracv decs =
          let nsec =
            ((pow10 (10 - decs)) * fracv + 5) / 10 in
          let t = intv * ticksPerSecond + nsec in
          let t = if sign then t else -t in T t in
        let rec frac' sign intv fracv decs src =
          if Stdlib.(>=) decs 7
          then
            Some
              ((mkTime sign intv fracv decs),
                (StringCvt.dropl isDigit getc src))
          else
            (match getc src with
             | None -> Some ((mkTime sign intv fracv decs), src)
             | Some (c, rest) ->
                 (match charToDigit c with
                  | None -> Some ((mkTime sign intv fracv decs), src)
                  | Some d ->
                      frac' sign intv (Stdlib.(+) (10 * fracv) d) (Stdlib.(+) decs 1) rest)) in
        let rec frac sign intv src =
          match getc src with
          | None -> None
          | Some (c, rest) ->
              (match charToDigit c with
               | None -> None
               | Some d -> frac' sign intv d 1 rest) in
        let rec int' sign intv src =
          match getc src with
          | None -> Some ((mkTime sign intv 0 7), src)
          | Some ('.', rest) -> frac sign intv rest
          | Some (c, rest) ->
              (match charToDigit c with
               | None -> Some ((mkTime sign intv 0 7), src)
               | Some d -> int' sign ((10 * intv) + d) rest) in
        let rec int sign src =
          match getc src with
          | None -> None
          | Some ('.', rest) -> frac sign 0 rest
          | Some (c, rest) ->
              (match charToDigit c with
               | None -> None
               | Some d -> int' sign d rest) in
        match getc (StringCvt.skipWS getc src) with
        | None -> None
        | Some ('+', rest) -> int true rest
        | Some ('~', rest) -> int false rest
        | Some ('-', rest) -> int false rest
        | Some ('.', rest) -> frac true 0 rest
        | Some (c, rest) ->
            (match charToDigit c with
             | None -> None
             | Some d -> int' true d rest)
    let fromString = StringCvt.scanString scan
    let (+) = timeAdd
    let (-) = timeSub
  end ;;
