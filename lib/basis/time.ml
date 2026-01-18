
(* Time module - compatibility layer for SML Basis Library Time structure *)
(* Author: Port from SML to OCaml *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

module type TIME =
  sig
    (* Time represented as seconds (float) *)
    type time

    (* Exception raised on invalid time operations *)
    exception Time

    (* Zero time value *)
    val zeroTime : time

    (* Time arithmetic *)
    val (+) : time * time -> time
    val (-) : time * time -> time

    (* Comparisons *)
    val (<) : time * time -> bool
    val (<=) : time * time -> bool
    val (>) : time * time -> bool
    val (>=) : time * time -> bool
    val compare : time * time -> order

    (* Conversions *)
    val toString : time -> string
    val fromReal : float -> time
    val toReal : time -> float

    (* Current time *)
    val now : unit -> time
  end

module Time : TIME =
  struct
    (* Time is represented as a float (seconds) *)
    type time = float

    exception Time

    let zeroTime = 0.0

    let (+) (t1, t2) = t1 +. t2
    let (-) (t1, t2) = t1 -. t2

    let (<) (t1, t2) = t1 < t2
    let (<=) (t1, t2) = t1 <= t2
    let (>) (t1, t2) = t1 > t2
    let (>=) (t1, t2) = t1 >= t2

    let compare (t1, t2) =
      if (>) (t1, t2) then LESS
      else if (<) (t1, t2) then GREATER
      else EQUAL

    let toString t =
      Printf.sprintf "%.3f" t

    let fromReal x = x
    let toReal x = x

    let now () = Unix.gettimeofday ()
  end
 