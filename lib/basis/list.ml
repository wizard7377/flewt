(* List module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/list.html *)

open Base

(** Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for list operations *)
module type LIST = sig
  (** List type *)
  type 'a list = 'a Base.List.t

  (** Exception raised by hd and tl on empty list *)
  exception Empty

  (** Append two lists *)
  val (@) : 'a list * 'a list -> 'a list

  (** Apply function to each element for side effect *)
  val app : ('a -> unit) -> 'a list -> unit

  (** Left fold *)
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b

  (** Right fold *)
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b

  (** Head of list *)
  val hd : 'a list -> 'a

  (** Length of list *)
  val length : 'a list -> int

  (** Map function over list *)
  val map : ('a -> 'b) -> 'a list -> 'b list

  (** Test if list is empty *)
  val null : 'a list -> bool

  (** Reverse list *)
  val rev : 'a list -> 'a list

  (** Tail of list *)
  val tl : 'a list -> 'a list

  (** Test if all elements satisfy predicate *)
  val all : ('a -> bool) -> 'a list -> bool

  (** Compare lists lexicographically *)
  val collate : ('a * 'a -> order) -> 'a list * 'a list -> order

  (** Flatten list of lists *)
  val concat : 'a list list -> 'a list

  (** Drop first n elements *)
  val drop : 'a list * int -> 'a list

  (** Test if any element satisfies predicate *)
  val exists : ('a -> bool) -> 'a list -> bool

  (** Filter elements satisfying predicate *)
  val filter : ('a -> bool) -> 'a list -> 'a list

  (** Find first element satisfying predicate *)
  val find : ('a -> bool) -> 'a list -> 'a option

  (** Decompose list into head and tail *)
  val getItem : 'a list -> ('a * 'a list) option

  (** Last element of list *)
  val last : 'a list -> 'a

  (** Map partial function over list, keeping only Some results *)
  val mapPartial : ('a -> 'b option) -> 'a list -> 'b list

  (** Get nth element (0-indexed) *)
  val nth : 'a list * int -> 'a

  (** Partition list by predicate *)
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list

  (** Reverse and append *)
  val revAppend : 'a list * 'a list -> 'a list

  (** Create list by tabulating function *)
  val tabulate : int * (int -> 'a) -> 'a list

  (** Take first n elements *)
  val take : 'a list * int -> 'a list
end

module SmlList : LIST = struct
  type 'a list = 'a Base.List.t

  exception Empty

  let null = function
    | [] -> true
    | _ -> false

  let hd = function
    | x :: _ -> x
    | [] -> raise Empty

  let tl = function
    | _ :: l -> l
    | [] -> raise Empty

  let rec last = function
    | [] -> raise Empty
    | [x] -> x
    | _ :: l -> last l

  let getItem = function
    | [] -> None
    | x :: r -> Some (x, r)

  let rec foldl f b l =
    match l with
    | [] -> b
    | x :: l -> foldl f (f (x, b)) l

  let length l = foldl (fun (_, n) -> n + 1) 0 l

  let revAppend (l1, l2) =
    foldl (fun (x, acc) -> x :: acc) l2 l1

  let rev l = revAppend (l, [])

  let (@) (l1, l2) =
    match l2 with
    | [] -> l1
    | _ -> revAppend (rev l1, l2)

  let foldr f b l = foldl f b (rev l)

  let concat ls = foldr (fun (l, acc) -> (@) (l, acc)) [] ls

  let app f l = foldl (fun (x, ()) -> f x) () l

  let map f l =
    rev (foldl (fun (x, acc) -> f x :: acc) [] l)

  let mapPartial pred l =
    rev (foldl (fun (x, acc) ->
        match pred x with
        | None -> acc
        | Some y -> y :: acc) [] l)

  let filter pred l =
    mapPartial (fun x -> if pred x then Some x else None) l

  let partition pred l =
    let (pos, neg) =
      foldl (fun (x, (trues, falses)) ->
          if pred x
          then (x :: trues, falses)
          else (trues, x :: falses)) ([], []) l
    in
    (rev pos, rev neg)

  let rec find pred = function
    | [] -> None
    | x :: l -> if pred x then Some x else find pred l

  let exists pred l =
    match find pred l with
    | None -> false
    | Some _ -> true

  let all pred l = not (exists (fun x -> not (pred x)) l)

  let tabulate (n, f) =
    if n < 0 then raise (Invalid_argument "List.tabulate")
    else
      let rec loop i acc =
        if i < n then loop (i + 1) (f i :: acc)
        else rev acc
      in
      loop 0 []

  let nth (l, n) =
    let rec loop l n =
      match l with
      | [] -> raise (Invalid_argument "List.nth")
      | x :: l -> if n = 0 then x else loop l (n - 1)
    in
    if n < 0 then raise (Invalid_argument "List.nth")
    else loop l n

  let take (l, n) =
    let rec loop l n acc =
      if n <= 0 then rev acc
      else
        match l with
        | [] -> raise (Invalid_argument "List.take")
        | x :: l -> loop l (n - 1) (x :: acc)
    in
    if n < 0 then raise (Invalid_argument "List.take")
    else loop l n []

  let drop (l, n) =
    let rec loop l n =
      if n <= 0 then l
      else
        match l with
        | [] -> raise (Invalid_argument "List.drop")
        | _ :: l -> loop l (n - 1)
    in
    if n < 0 then raise (Invalid_argument "List.drop")
    else loop l n

  let rec collate cmp = function
    | ([], []) -> EQUAL
    | ([], _) -> LESS
    | (_, []) -> GREATER
    | (x1 :: l1, x2 :: l2) ->
      match cmp (x1, x2) with
      | EQUAL -> collate cmp (l1, l2)
      | ans -> ans
end
