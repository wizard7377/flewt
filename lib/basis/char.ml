(* Char module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/char.html *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for character operations *)
module type CHAR = sig
  type char = Base.Char.t
  type string = Base.String.t

  (** Minimum character value (NUL) *)
  val minChar : char

  (** Maximum character value *)
  val maxChar : char

  (** Maximum ordinal value *)
  val maxOrd : int

  (** Get ordinal value of character *)
  val ord : char -> int

  (** Get character from ordinal value *)
  val chr : int -> char

  (** Successor character *)
  val succ : char -> char

  (** Predecessor character *)
  val pred : char -> char

  (** Comparison *)
  val compare : char * char -> order
  val (< ) : char * char -> bool
  val (<=) : char * char -> bool
  val (> ) : char * char -> bool
  val (>=) : char * char -> bool

  (** Test if string contains character *)
  val contains : string -> char -> bool

  (** Test if string does not contain character *)
  val notContains : string -> char -> bool

  (** Character predicates *)
  val isAscii : char -> bool
  val isAlpha : char -> bool
  val isAlphaNum : char -> bool
  val isCntrl : char -> bool
  val isDigit : char -> bool
  val isGraph : char -> bool
  val isHexDigit : char -> bool
  val isLower : char -> bool
  val isPrint : char -> bool
  val isSpace : char -> bool
  val isPunct : char -> bool
  val isUpper : char -> bool

  (** Case conversion *)
  val toLower : char -> char
  val toUpper : char -> char

  (** String conversions *)
  val toString : char -> string
  val fromString : string -> char option
  val toCString : char -> string
  val fromCString : string -> char option
end

module SmlChar : CHAR = struct
  type char = Base.Char.t
  type string = Base.String.t

  let minChar = Base.Char.min_value
  let maxChar = Base.Char.max_value
  let maxOrd = Base.Char.to_int maxChar

  let ord = Base.Char.to_int

  let chr n =
    if n < 0 || n > maxOrd then
      raise (Invalid_argument "chr")
    else
      Base.Char.of_int_exn n

  let succ c =
    let n = ord c in
    if n >= maxOrd then raise (Invalid_argument "succ")
    else chr (n + 1)

  let pred c =
    let n = ord c in
    if n <= 0 then raise (Invalid_argument "pred")
    else chr (n - 1)

  let compare (c1, c2) =
    let n = Base.Char.compare c1 c2 in
    if Stdlib.( < ) n 0 then LESS
    else if Stdlib.( = ) n 0 then EQUAL
    else GREATER

  let (< ) (c1, c2) = Base.Char.(c1 < c2)
  let (<=) (c1, c2) = Base.Char.(c1 <= c2)
  let (> ) (c1, c2) = Base.Char.(c1 > c2)
  let (>=) (c1, c2) = Base.Char.(c1 >= c2)

  let contains s c = Base.String.contains s c
  let notContains s c = not (Base.String.contains s c)

  let isAscii c = Stdlib.( < ) (ord c) 128
  let toLower = Base.Char.lowercase
  let toUpper = Base.Char.uppercase
  let isAlpha = Base.Char.is_alpha
  let isAlphaNum = Base.Char.is_alphanum
  let isCntrl c = Stdlib.( < ) (ord c) 32 || Stdlib.( = ) (ord c) 127
  let isDigit = Base.Char.is_digit
  let isHexDigit = Base.Char.is_hex_digit
  let isLower = Base.Char.is_lowercase
  let isPrint = Base.Char.is_print
  let isSpace = Base.Char.is_whitespace
  let isUpper = Base.Char.is_uppercase
  let isGraph c = isPrint c && Stdlib.( <> ) c ' '
  let isPunct c = isGraph c && not (isAlphaNum c)

  let toString c = Base.String.make 1 c

  let fromString s =
    if Stdlib.( = ) (Base.String.length s) 1 then Some (Base.String.get s 0)
    else None

  let toCString c =
    (* Simplified - just escape special characters *)
    match c with
    | '\n' -> "\\n"
    | '\t' -> "\\t"
    | '\r' -> "\\r"
    | '\\' -> "\\\\"
    | '"' -> "\\\""
    | c when isCntrl c -> Printf.sprintf "\\%03d" (ord c)
    | c -> toString c

  let fromCString s =
    if Base.String.is_empty s then None
    else if Stdlib.( = ) (Base.String.length s) 1 then Some (Base.String.get s 0)
    else if Stdlib.( >= ) (Base.String.length s) 2 && Stdlib.( = ) (Base.String.get s 0) '\\' then
      match Base.String.get s 1 with
      | 'n' -> Some '\n'
      | 't' -> Some '\t'
      | 'r' -> Some '\r'
      | '\\' -> Some '\\'
      | '"' -> Some '"'
      | _ -> None
    else None
end
