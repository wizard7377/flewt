
(* Ordered Field *)
(* Author: Roberto Virga *)

(* FIELD module type *)
module type FIELD  =
  sig
    (* Name of the set *)
    val name : string
    (* Main type *)
    type nonrec number
    (* Non-invertible element *)
    exception Div
    (* Constants *)
    val zero : number
    val one : number
    (* Operators *)
    val (~-) : number -> number
    val (+) : (number * number) -> number
    val (-) : (number * number) -> number
    val ( * ) : (number * number) -> number
    val inverse : number -> number
    (* raises Div *)
    (* Conversions *)
    val fromInt : int -> number
    val fromString : string -> number option
    val toString : number -> string
  end

module type ORDERED_FIELD  =
  sig
    include FIELD
    (* Sign operations *)
    val sign : number -> int
    val abs : number -> number
    (* Comparisons predicates *)
    val (>) : (number * number) -> bool
    val (<) : (number * number) -> bool
    val (>=) : (number * number) -> bool
    val (<=) : (number * number) -> bool
    val compare : (number * number) -> order
  end;;
