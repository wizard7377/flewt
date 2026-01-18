open Base ;;
module type STRING_CVT =
  sig
    type radix = BIN | OCT | DEC | HEX
    type realfmt
    = SCI of int option
    | FIX of int option
    | GEN of int option
    | EXACT
    type ('a,'b) reader = 'b -> ('a * 'b) option
    val padLeft  : char -> int -> string -> string
    val padRight : char -> int -> string -> string
    val splitl : (char -> bool)
                -> (char, 'a) reader -> 'a -> string * 'a
    val takel : (char -> bool)
                -> (char, 'a) reader -> 'a -> string
    val dropl : (char -> bool) -> (char, 'a) reader -> 'a -> 'a
    val skipWS : (char, 'a) reader -> 'a -> 'a
    type cs
    val scanString : ((char, cs) reader -> ('a, cs) reader)
                    -> string -> 'a option
  end;;

module StringCvt : STRING_CVT =
  struct
    type radix = BIN | OCT | DEC | HEX
    type realfmt = 
      SCI of int option
    | FIX of int option
    | GEN of int option
    | EXACT
    type ('a,'b) reader = 'b -> ('a * 'b) option
    let padLeft c i s = String.pad_left ~char:c s ~len:i
    let padRight c i s = String.pad_right ~char:c s ~len:i
    let splitl p read s = assert false
    let takel p read s = assert false
    let dropl p read s = assert false
    let skipWS read s = assert false
    type cs
    let scanString f s = assert false 
    end;;

