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
val charToDigit : radix -> char -> int option
end 
module StringCvt : STRING_CVT =
  struct
    type radix = BIN | OCT | DEC | HEX
    type realfmt
      = SCI of int option
      | FIX of int option   
      | GEN of int option
      | EXACT
    type ('a,'b) reader = 'b -> ('a * 'b) option
    let rec padLeft padChar totalLen str = assert false 
    let rec padRight padChar totalLen str = assert false
    let rec splitl p reader src = assert false
    let rec takel p reader src = assert false
    let rec dropl p reader src = assert false
    let rec skipWS reader src = assert false
    type cs = CS
    let rec scanString scan reader = assert false
    let charToDigit radix c =
      let code = Char.code c in
      let digit =
        if code >= Char.code '0' && code <= Char.code '9' then
          Some (code - Char.code '0')
        else if code >= Char.code 'a' && code <= Char.code 'f' then
          Some (code - Char.code 'a' + 10)
        else if code >= Char.code 'A' && code <= Char.code 'F' then
          Some (code - Char.code 'A' + 10)
        else
          None
      in
      match digit with
      | None -> None
      | Some d ->
          let max_digit = match radix with
            | BIN -> 1
            | OCT -> 7
            | DEC -> 9
            | HEX -> 15
          in
          if d <= max_digit then Some d else None
  end ;;
