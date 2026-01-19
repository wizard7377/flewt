(* StringCvt module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/string-cvt.html *)

open Base

(** Module type for string conversion utilities *)
module type STRING_CVT = sig
  (** Radix for numeric conversions *)
  type radix = BIN | OCT | DEC | HEX

  (** Format specifications for real number conversions *)
  type realfmt =
    | SCI of int option  (** Scientific notation with optional precision *)
    | FIX of int option  (** Fixed-point notation with optional precision *)
    | GEN of int option  (** General format with optional precision *)
    | EXACT              (** Exact decimal representation *)

  (** A reader is a function that reads a value from a stream *)
  type ('a, 'b) reader = 'b -> ('a * 'b) option

  (** Pad string on left with character to given width *)
  val padLeft : char -> int -> string -> string

  (** Pad string on right with character to given width *)
  val padRight : char -> int -> string -> string

  (** Split stream at first character not satisfying predicate *)
  val splitl : (char -> bool) -> (char, 'a) reader -> 'a -> string * 'a

  (** Take characters while predicate holds *)
  val takel : (char -> bool) -> (char, 'a) reader -> 'a -> string

  (** Drop characters while predicate holds *)
  val dropl : (char -> bool) -> (char, 'a) reader -> 'a -> 'a

  (** Skip whitespace characters *)
  val skipWS : (char, 'a) reader -> 'a -> 'a

  (** Abstract type for string scanning state *)
  type cs

  (** Scan a string using a reader-based scanner *)
  val scanString : ((char, cs) reader -> ('a, cs) reader) -> string -> 'a option
end

module StringCvt : STRING_CVT = struct
  type radix = BIN | OCT | DEC | HEX

  type realfmt =
    | SCI of int option
    | FIX of int option
    | GEN of int option
    | EXACT

  type ('a, 'b) reader = 'b -> ('a * 'b) option

  let padLeft c width s =
    let len = String.length s in
    if len >= width then s
    else String.make (width - len) c ^ s

  let padRight c width s =
    let len = String.length s in
    if len >= width then s
    else s ^ String.make (width - len) c

  let rec splitl p reader src =
    let rec loop acc src =
      match reader src with
      | None -> (String.concat ~sep:"" (List.rev acc), src)
      | Some (c, src') ->
        if p c then loop (String.make 1 c :: acc) src'
        else (String.concat ~sep:"" (List.rev acc), src)
    in
    loop [] src

  let takel p reader src =
    fst (splitl p reader src)

  let dropl p reader src =
    snd (splitl p reader src)

  let isSpace c =
    Char.equal c ' ' || Char.equal c '\t' || Char.equal c '\n' ||
    Char.equal c '\r' || Char.equal c '\012' (* form feed *)

  let skipWS reader src =
    dropl isSpace reader src

  (* Internal state for scanning strings *)
  type cs = int  (* position in string *)

  let scanString scanner s =
    let len = String.length s in
    let reader pos =
      if pos >= len then None
      else Some (String.get s pos, pos + 1)
    in
    match scanner reader 0 with
    | None -> None
    | Some (v, _) -> Some v
end

