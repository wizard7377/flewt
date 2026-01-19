(* Substring module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/substring.html *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** A substring is a view into a string (string, start, length) *)
type substring = string * int * int

(** Module type for substring operations *)
module type SUBSTRING = sig
  type substring
  type char = Base.Char.t
  type string = Base.String.t

  (** Create a substring from (string, start, length) *)
  val sub : string * int * int -> substring

  (** Create substring spanning entire string *)
  val full : string -> substring

  (** Extract the string content of a substring *)
  val string : substring -> string

  (** Extract substring with optional length *)
  val extract : string * int * int option -> substring

  (** Get underlying base string, start index, and length *)
  val base : substring -> string * int * int

  (** Test if substring is empty *)
  val isEmpty : substring -> bool

  (** Get first character and remaining substring *)
  val getc : substring -> (char * substring) option

  (** Get first character *)
  val first : substring -> char option

  (** Size of substring *)
  val size : substring -> int

  (** Create sub-substring *)
  val slice : substring * int * int option -> substring

  (** Concatenate list of substrings *)
  val concat : substring list -> string

  (** Concatenate with separator *)
  val concatWith : string -> substring list -> string

  (** Convert substring to character list *)
  val explode : substring -> char list

  (** Test if string is prefix of substring *)
  val isPrefix : string -> substring -> bool

  (** Test if string is contained in substring *)
  val isSubstring : string -> substring -> bool

  (** Test if string is suffix of substring *)
  val isSuffix : string -> substring -> bool

  (** Compare two substrings *)
  val compare : substring * substring -> order

  (** Compare with custom character comparator *)
  val collate : (char * char -> order) -> substring * substring -> order

  (** Split at first character not satisfying predicate (from left) *)
  val splitl : (char -> bool) -> substring -> substring * substring

  (** Split at first character not satisfying predicate (from right) *)
  val splitr : (char -> bool) -> substring -> substring * substring

  (** Split at given position *)
  val splitAt : substring * int -> substring * substring

  (** Drop characters from left while predicate holds *)
  val dropl : (char -> bool) -> substring -> substring

  (** Drop characters from right while predicate holds *)
  val dropr : (char -> bool) -> substring -> substring

  (** Take characters from left while predicate holds *)
  val takel : (char -> bool) -> substring -> substring

  (** Take characters from right while predicate holds *)
  val taker : (char -> bool) -> substring -> substring

  (** Trim n characters from left *)
  val triml : int -> substring -> substring

  (** Trim n characters from right *)
  val trimr : int -> substring -> substring

  (** Find position of pattern in substring *)
  val position : string -> substring -> substring * substring

  (** Span between two substrings (must share base string) *)
  val span : substring * substring -> substring

  (** Get sub-substring given substring and (start, length) *)
  val substring : substring * int * int -> substring

  (** Translate each character using function *)
  val translate : (char -> string) -> substring -> string

  (** Split on delimiter characters (empty strings omitted) *)
  val tokens : (char -> bool) -> substring -> substring list

  (** Split on delimiter characters (empty strings kept) *)
  val fields : (char -> bool) -> substring -> substring list

  (** Apply function to each character *)
  val app : (char -> unit) -> substring -> unit

  (** Left fold over characters *)
  val foldl : (char * 'a -> 'a) -> 'a -> substring -> 'a

  (** Right fold over characters *)
  val foldr : (char * 'a -> 'a) -> 'a -> substring -> 'a
end

module Substring : SUBSTRING = struct
  open Base

  type char = Char.t
  type string = String.t
  type substring = string * int * int

  let sub (s, i, n) =
    if i < 0 || n < 0 || i + n > String.length s then
      raise (Invalid_argument "Substring.sub")
    else
      (s, i, n)

  let full s = (s, 0, String.length s)

  let string (s, i, n) = String.sub s ~pos:i ~len:n

  let extract (s, i, lenOpt) =
    let len = String.length s in
    if i < 0 || i > len then
      raise (Invalid_argument "Substring.extract")
    else
      match lenOpt with
      | None -> (s, i, len - i)
      | Some n ->
        if n < 0 || i + n > len then
          raise (Invalid_argument "Substring.extract")
        else
          (s, i, n)

  let base ss = ss

  let isEmpty (_, _, n) = n = 0

  let getc (s, i, n) =
    if n = 0 then None
    else Some (String.get s i, (s, i + 1, n - 1))

  let first (s, i, n) =
    if n = 0 then None
    else Some (String.get s i)

  let size (_, _, n) = n

  let slice ((s, i, n), i', lenOpt) =
    if i' < 0 || i' > n then
      raise (Invalid_argument "Substring.slice")
    else
      match lenOpt with
      | None -> (s, i + i', n - i')
      | Some n' ->
        if n' < 0 || i' + n' > n then
          raise (Invalid_argument "Substring.slice")
        else
          (s, i + i', n')

  let concat sss = String.concat ~sep:"" (List.map ~f:string sss)

  let concatWith sep sss =
    String.concat ~sep (List.map ~f:string sss)

  let explode (s, i, n) =
    let rec loop j acc =
      if j < i then acc
      else loop (j - 1) (String.get s j :: acc)
    in
    loop (i + n - 1) []

  let isPrefix pat (s, i, n) =
    let plen = String.length pat in
    if plen > n then false
    else String.equal pat (String.sub s ~pos:i ~len:plen)

  let isSubstring pat (s, i, n) =
    let plen = String.length pat in
    let rec loop j =
      if j + plen > i + n then false
      else if String.equal pat (String.sub s ~pos:j ~len:plen) then true
      else loop (j + 1)
    in
    loop i

  let isSuffix pat (s, i, n) =
    let plen = String.length pat in
    if plen > n then false
    else String.equal pat (String.sub s ~pos:(i + n - plen) ~len:plen)

  let compare ((s1, i1, n1), (s2, i2, n2)) =
    match String.compare (String.sub s1 ~pos:i1 ~len:n1)
            (String.sub s2 ~pos:i2 ~len:n2) with
    | n when n < 0 -> LESS
    | 0 -> EQUAL
    | _ -> GREATER

  let collate cmp ((s1, i1, n1), (s2, i2, n2)) =
    let rec loop i =
      if i >= n1 && i >= n2 then EQUAL
      else if i >= n1 then LESS
      else if i >= n2 then GREATER
      else
        match cmp (String.get s1 (i1 + i), String.get s2 (i2 + i)) with
        | EQUAL -> loop (i + 1)
        | result -> result
    in
    loop 0

  let splitl p (s, i, n) =
    let rec loop j =
      if j >= i + n then ((s, i, n), (s, i + n, 0))
      else if not (p (String.get s j)) then ((s, i, j - i), (s, j, i + n - j))
      else loop (j + 1)
    in
    loop i

  let splitr p (s, i, n) =
    let rec loop j =
      if j < i then ((s, i, 0), (s, i, n))
      else if not (p (String.get s j)) then ((s, i, j - i + 1), (s, j + 1, i + n - j - 1))
      else loop (j - 1)
    in
    loop (i + n - 1)

  let splitAt ((s, i, n), k) =
    if k < 0 || k > n then
      raise (Invalid_argument "Substring.splitAt")
    else
      ((s, i, k), (s, i + k, n - k))

  let dropl p ss = Stdlib.snd (splitl p ss)
  let dropr p ss = Stdlib.fst (splitr p ss)
  let takel p ss = Stdlib.fst (splitl p ss)
  let taker p ss = Stdlib.snd (splitr p ss)

  let triml k (s, i, n) =
    if k < 0 then raise (Invalid_argument "Substring.triml")
    else if k >= n then (s, i + n, 0)
    else (s, i + k, n - k)

  let trimr k (s, i, n) =
    if k < 0 then raise (Invalid_argument "Substring.trimr")
    else if k >= n then (s, i, 0)
    else (s, i, n - k)

  let position pat (s, i, n) =
    let plen = String.length pat in
    let rec loop j =
      if j + plen > i + n then ((s, i, n), (s, i + n, 0))
      else if String.equal pat (String.sub s ~pos:j ~len:plen) then
        ((s, i, j - i), (s, j, i + n - j))
      else loop (j + 1)
    in
    loop i

  let span ((s1, i1, n1), (s2, i2, n2)) =
    if not (phys_equal s1 s2) then
      raise (Invalid_argument "Substring.span: different base strings")
    else
      let start = min i1 i2 in
      let finish = max (i1 + n1) (i2 + n2) in
      (s1, start, finish - start)

  let substring ((s, i, n), i', n') =
    if i' < 0 || n' < 0 || i' + n' > n then
      raise (Invalid_argument "Substring.substring")
    else
      (s, i + i', n')

  let translate f (s, i, n) =
    let rec loop j acc =
      if j >= i + n then String.concat ~sep:"" (List.rev acc)
      else loop (j + 1) (f (String.get s j) :: acc)
    in
    loop i []

  let tokens p (s, i, n) =
    let ss = (s, i, n) in
    let rec loop ss acc =
      let ss = dropl p ss in
      if isEmpty ss then List.rev acc
      else
        let (tok, rest) = splitl (fun c -> not (p c)) ss in
        if isEmpty tok then List.rev acc
        else loop rest (tok :: acc)
    in
    loop ss []

  let fields p (s, i, n) =
    let rec loop j acc =
      if j >= i + n then List.rev acc
      else
        let (field, rest) = splitl (fun c -> not (p c)) (s, j, i + n - j) in
        let (_, i', _) = rest in
        if isEmpty rest then List.rev (field :: acc)
        else loop (i' + 1) (field :: acc)
    in
    loop i []

  let app f (s, i, n) =
    for j = i to i + n - 1 do
      f (String.get s j)
    done

  let foldl f init (s, i, n) =
    let rec loop j acc =
      if j >= i + n then acc
      else loop (j + 1) (f (String.get s j, acc))
    in
    loop i init

  let foldr f init (s, i, n) =
    let rec loop j acc =
      if j < i then acc
      else loop (j - 1) (f (String.get s j, acc))
    in
    loop (i + n - 1) init
end
