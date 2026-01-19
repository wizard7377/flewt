(* String module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/string.html *)

(** Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for string operations *)
module type STRING = sig
  type char = Base.Char.t
  type string = Base.String.t

  (** Concatenate two strings *)
  val (^) : string * string -> string

  (** Concatenate list of strings *)
  val concat : string list -> string

  (** Explode string to character list *)
  val explode : string -> char list

  (** Implode character list to string *)
  val implode : char list -> string

  (** Length of string *)
  val size : string -> int

  (** Create single-character string *)
  val str : char -> string

  (** Extract substring *)
  val substring : string * int * int -> string

  (** Comparisons *)
  val (<) : string * string -> bool
  val (<=) : string * string -> bool
  val (>) : string * string -> bool
  val (>=) : string * string -> bool

  (** Compare with custom character comparator *)
  val collate : (char * char -> order) -> string * string -> order

  (** Compare strings *)
  val compare : string * string -> order

  (** Concatenate with separator *)
  val concatWith : string -> string list -> string

  (** Extract substring with optional length *)
  val extract : string * int * int option -> string

  (** Split on field separators (empty fields kept) *)
  val fields : (char -> bool) -> string -> string list

  (** Parse string from C escape sequences *)
  val fromCString : string -> string option

  (** Parse string from SML escape sequences *)
  val fromString : string -> string option

  (** Test if prefix *)
  val isPrefix : string -> string -> bool

  (** Test if substring *)
  val isSubstring : string -> string -> bool

  (** Test if suffix *)
  val isSuffix : string -> string -> bool

  (** Map function over string *)
  val map : (char -> char) -> string -> string

  (** Maximum string length *)
  val maxSize : int

  (** Get character at index *)
  val sub : string * int -> char

  (** Convert to C escape sequences *)
  val toCString : string -> string

  (** Convert to SML escape sequences *)
  val toString : string -> string

  (** Split on token separators (empty tokens omitted) *)
  val tokens : (char -> bool) -> string -> string list

  (** Translate each character *)
  val translate : (char -> string) -> string -> string
end

module SmlString : STRING = struct
  type char = Base.Char.t
  type string = Base.String.t

  (* Int comparisons using stdlib to avoid shadowing issues *)
  let int_lt (a : int) (b : int) = Stdlib.( < ) a b
  let int_le (a : int) (b : int) = Stdlib.( <= ) a b
  let int_gt (a : int) (b : int) = Stdlib.( > ) a b
  let int_ge (a : int) (b : int) = Stdlib.( >= ) a b
  let int_eq (a : int) (b : int) = Stdlib.( = ) a b

  let (^) (s1, s2) = s1 ^ s2

  let concat = Base.String.concat ~sep:""

  let explode s =
    let rec loop i acc =
      if int_lt i 0 then acc
      else loop (i - 1) (Base.String.get s i :: acc)
    in
    loop (Base.String.length s - 1) []

  let implode chars =
    let len = Base.List.length chars in
    let buf = Bytes.create len in
    let rec fill i = function
      | [] -> ()
      | c :: rest ->
        Bytes.set buf i c;
        fill (i + 1) rest
    in
    fill 0 chars;
    Bytes.to_string buf

  let size = Base.String.length

  let str c = Base.String.make 1 c

  let substring (s, start, len) =
    if int_lt start 0 || int_lt len 0 || int_gt (start + len) (size s) then
      raise (Invalid_argument "String.substring")
    else
      Base.String.sub s ~pos:start ~len

  let extract (s, start, lenOpt) =
    let len = size s in
    if int_lt start 0 || int_gt start len then
      raise (Invalid_argument "String.extract")
    else
      match lenOpt with
      | None -> Base.String.sub s ~pos:start ~len:(len - start)
      | Some n ->
        if int_lt n 0 || int_gt (start + n) len then
          raise (Invalid_argument "String.extract")
        else
          Base.String.sub s ~pos:start ~len:n

  let (<) (s1, s2) = Base.String.(s1 < s2)
  let (<=) (s1, s2) = Base.String.(s1 <= s2)
  let (>) (s1, s2) = Base.String.(s1 > s2)
  let (>=) (s1, s2) = Base.String.(s1 >= s2)

  let compare (s1, s2) =
    let cmp = Base.String.compare s1 s2 in
    if int_lt cmp 0 then LESS
    else if int_eq cmp 0 then EQUAL
    else GREATER

  let collate cmp (s1, s2) =
    let len1 = size s1 in
    let len2 = size s2 in
    let rec loop i =
      if int_ge i len1 && int_ge i len2 then EQUAL
      else if int_ge i len1 then LESS
      else if int_ge i len2 then GREATER
      else
        match cmp (Base.String.get s1 i, Base.String.get s2 i) with
        | EQUAL -> loop (i + 1)
        | result -> result
    in
    loop 0

  let concatWith sep = Base.String.concat ~sep

  let sub (s, i) =
    if int_lt i 0 || int_ge i (size s) then
      raise (Invalid_argument "String.sub")
    else
      Base.String.get s i

  let map f s = Base.String.map ~f s

  let maxSize = Base.String.max_length

  let isPrefix prefix s =
    let plen = size prefix in
    let slen = size s in
    int_le plen slen && Base.String.equal prefix (Base.String.sub s ~pos:0 ~len:plen)

  let isSuffix suffix s =
    let plen = size suffix in
    let slen = size s in
    int_le plen slen && Base.String.equal suffix (Base.String.sub s ~pos:(slen - plen) ~len:plen)

  let isSubstring pattern s =
    let plen = size pattern in
    let slen = size s in
    let rec loop i =
      if int_gt (i + plen) slen then false
      else if Base.String.equal pattern (Base.String.sub s ~pos:i ~len:plen) then true
      else loop (i + 1)
    in
    loop 0

  let translate f s =
    let result = Base.List.map ~f:(fun c -> f c) (explode s) in
    concat result

  let escape_char c =
    match c with
    | '\n' -> "\\n"
    | '\t' -> "\\t"
    | '\r' -> "\\r"
    | '\\' -> "\\\\"
    | '"' -> "\\\""
    | c when int_lt (Base.Char.to_int c) 32 || int_eq (Base.Char.to_int c) 127 -> 
      Printf.sprintf "\\%03d" (Base.Char.to_int c)
    | c -> str c

  let toString s = translate escape_char s

  let toCString s = translate escape_char s

  let fromString s =
    (* Simplified - just return the string *)
    Some s

  let fromCString s =
    (* Simplified - just return the string *)
    Some s

  let tokens p s =
    let len = size s in
    let rec skip_delim i =
      if int_ge i len then i
      else if p (Base.String.get s i) then skip_delim (i + 1)
      else i
    in
    let rec find_delim i =
      if int_ge i len then i
      else if p (Base.String.get s i) then i
      else find_delim (i + 1)
    in
    let rec loop i acc =
      let i = skip_delim i in
      if int_ge i len then Base.List.rev acc
      else
        let j = find_delim i in
        let tok = Base.String.sub s ~pos:i ~len:(j - i) in
        loop j (tok :: acc)
    in
    loop 0 []

  let fields p s =
    let len = size s in
    let rec find_delim i =
      if int_ge i len then i
      else if p (Base.String.get s i) then i
      else find_delim (i + 1)
    in
    let rec loop i acc =
      if int_gt i len then Base.List.rev acc
      else
        let j = find_delim i in
        let field = Base.String.sub s ~pos:i ~len:(j - i) in
        if int_ge j len then Base.List.rev (field :: acc)
        else loop (j + 1) (field :: acc)
    in
    loop 0 []
end
