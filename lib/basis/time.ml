(* Time module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/time.html *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for time operations *)
module type TIME = sig
  (** Abstract type representing time values *)
  type time

  (** Exception raised on invalid time operations *)
  exception Time

  (** The zero time value *)
  val zeroTime : time

  (** Time arithmetic *)
  val (+) : time * time -> time
  val (-) : time * time -> time

  (** Comparisons *)
  val (<) : time * time -> bool
  val (<=) : time * time -> bool
  val (>) : time * time -> bool
  val (>=) : time * time -> bool
  val compare : time * time -> order

  (** Format time with given number of decimal places *)
  val fmt : int -> time -> string

  (** Conversion from large integer representing microseconds *)
  val fromMicroseconds : int64 -> time

  (** Conversion from large integer representing milliseconds *)
  val fromMilliseconds : int64 -> time

  (** Conversion from large integer representing nanoseconds *)
  val fromNanoseconds : int64 -> time

  (** Conversion from real number (seconds) *)
  val fromReal : float -> time

  (** Conversion from large integer representing seconds *)
  val fromSeconds : int64 -> time

  (** Parse time from string *)
  val fromString : string -> time option

  (** Get current time *)
  val now : unit -> time

  (** Convert to microseconds *)
  val toMicroseconds : time -> int64

  (** Convert to milliseconds *)
  val toMilliseconds : time -> int64

  (** Convert to nanoseconds *)
  val toNanoseconds : time -> int64

  (** Convert to real number (seconds) *)
  val toReal : time -> float

  (** Convert to seconds *)
  val toSeconds : time -> int64

  (** Convert to string (default format) *)
  val toString : time -> string
end

module Time : TIME = struct
  (* Time is represented internally as nanoseconds (int64) for precision *)
  type time = int64

  exception Time

  let zeroTime = 0L

  let (+) (t1, t2) = Int64.add t1 t2
  let (-) (t1, t2) = Int64.sub t1 t2

  let int_lt (a : int) (b : int) = a < b
  let int_gt (a : int) (b : int) = a > b

  let (<) (t1, t2) = Int64.compare t1 t2 < 0
  let (<=) (t1, t2) = Int64.compare t1 t2 <= 0
  let (>) (t1, t2) = Int64.compare t1 t2 > 0
  let (>=) (t1, t2) = Int64.compare t1 t2 >= 0

  let compare (t1, t2) =
    let c = Int64.compare t1 t2 in
    if int_lt c 0 then LESS
    else if int_gt c 0 then GREATER
    else EQUAL

  let fromReal r =
    if Float.is_nan r then raise Time
    else Int64.of_float (r *. 1e9)

  let toReal t = Int64.to_float t /. 1e9

  let fromSeconds s = Int64.mul s 1_000_000_000L
  let toSeconds t = Int64.div t 1_000_000_000L

  let fromMilliseconds ms = Int64.mul ms 1_000_000L
  let toMilliseconds t = Int64.div t 1_000_000L

  let fromMicroseconds us = Int64.mul us 1_000L
  let toMicroseconds t = Int64.div t 1_000L

  let fromNanoseconds ns = ns
  let toNanoseconds t = t

  let fmt n t =
    Printf.sprintf "%.*f" n (toReal t)

  let toString t = fmt 3 t

  let now () =
    let t = Unix.gettimeofday () in
    fromReal t

  let fromString s =
    match Float.of_string_opt s with
    | Some f -> Some (fromReal f)
    | None -> None
end
 