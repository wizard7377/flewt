(* CharVector module - SML Basis Library compatibility *)
(* In SML, CharVector.vector is equivalent to string *)
(* See https://smlfamily.github.io/Basis/mono-vector.html *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for monomorphic character vectors (strings) *)
module type CHAR_VECTOR = sig
  type vector = string
  type elem = char

  (** Maximum length of a vector *)
  val maxLen : int

  (** Create vector from list of elements *)
  val fromList : elem list -> vector

  (** Create vector by tabulating a function *)
  val tabulate : int * (int -> elem) -> vector

  (** Length of vector *)
  val length : vector -> int

  (** Get element at index *)
  val sub : vector * int -> elem

  (** Functional update - create new vector with one element changed *)
  val update : vector * int * elem -> vector

  (** Concatenate list of vectors *)
  val concat : vector list -> vector

  (** Apply function with index to each element *)
  val appi : (int * elem -> unit) -> vector -> unit

  (** Apply function to each element *)
  val app : (elem -> unit) -> vector -> unit

  (** Map function with index over vector *)
  val mapi : (int * elem -> elem) -> vector -> vector

  (** Map function over vector *)
  val map : (elem -> elem) -> vector -> vector

  (** Left fold with index *)
  val foldli : (int * elem * 'a -> 'a) -> 'a -> vector -> 'a

  (** Right fold with index *)
  val foldri : (int * elem * 'a -> 'a) -> 'a -> vector -> 'a

  (** Left fold *)
  val foldl : (elem * 'a -> 'a) -> 'a -> vector -> 'a

  (** Right fold *)
  val foldr : (elem * 'a -> 'a) -> 'a -> vector -> 'a

  (** Find first element with index satisfying predicate *)
  val findi : (int * elem -> bool) -> vector -> (int * elem) option

  (** Find first element satisfying predicate *)
  val find : (elem -> bool) -> vector -> elem option

  (** Test if any element satisfies predicate *)
  val exists : (elem -> bool) -> vector -> bool

  (** Test if all elements satisfy predicate *)
  val all : (elem -> bool) -> vector -> bool

  (** Lexicographic comparison *)
  val collate : (elem * elem -> order) -> vector * vector -> order
end

module CharVector : CHAR_VECTOR = struct
  open Base

  type vector = string
  type elem = char

  let maxLen = String.max_length

  let fromList chars =
    let len = List.length chars in
    let s = Bytes.create len in
    let rec fill i = function
      | [] -> ()
      | c :: rest ->
        Bytes.set s i c;
        fill (i + 1) rest
    in
    fill 0 chars;
    Bytes.to_string s

  let tabulate (n, f) =
    if n < 0 then raise (Invalid_argument "CharVector.tabulate")
    else String.init n ~f

  let length = String.length

  let sub (v, i) =
    if i < 0 || i >= length v then
      raise (Invalid_argument "CharVector.sub")
    else
      String.get v i

  let update (v, i, c) =
    if i < 0 || i >= length v then
      raise (Invalid_argument "CharVector.update")
    else
      String.mapi ~f:(fun j ch -> if j = i then c else ch) v

  let concat = String.concat ~sep:""

  let appi f v =
    String.iteri ~f:(fun i c -> f (i, c)) v

  let app f v =
    String.iter ~f:f v

  let mapi f v =
    String.mapi ~f:(fun i c -> f (i, c)) v

  let map f v =
    String.map ~f:f v

  let foldli f init v =
    let rec loop i acc =
      if i >= length v then acc
      else loop (i + 1) (f (i, String.get v i, acc))
    in
    loop 0 init

  let foldri f init v =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, String.get v i, acc))
    in
    loop (length v - 1) init

  let foldl f init v =
    let rec loop i acc =
      if i >= length v then acc
      else loop (i + 1) (f (String.get v i, acc))
    in
    loop 0 init

  let foldr f init v =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (String.get v i, acc))
    in
    loop (length v - 1) init

  let findi p v =
    let rec loop i =
      if i >= length v then None
      else
        let c = String.get v i in
        if p (i, c) then Some (i, c)
        else loop (i + 1)
    in
    loop 0

  let find p v =
    let rec loop i =
      if i >= length v then None
      else
        let c = String.get v i in
        if p c then Some c
        else loop (i + 1)
    in
    loop 0

  let exists p v =
    match find p v with
    | Some _ -> true
    | None -> false

  let all p v =
    let rec loop i =
      if i >= length v then true
      else if p (String.get v i) then loop (i + 1)
      else false
    in
    loop 0

  let collate cmp (v1, v2) =
    let len1 = length v1 in
    let len2 = length v2 in
    let rec loop i =
      if i >= len1 && i >= len2 then EQUAL
      else if i >= len1 then LESS
      else if i >= len2 then GREATER
      else
        match cmp (String.get v1 i, String.get v2 i) with
        | EQUAL -> loop (i + 1)
        | result -> result
    in
    loop 0
end
