module type INTSET  =
  sig
    type nonrec intset
    val empty : intset
    val insert : (int * intset) -> intset
    val member : (int * intset) -> bool
    val foldl : ((int * 'b) -> 'b) -> 'b -> intset -> 'b
  end
module IntSet : INTSET =
  struct
    type rbt =
      | Empty 
      | Red of (int * rbt * rbt) 
      | Black of (int * rbt * rbt) 
    let rec lookup dict x =
      let rec lk =
        begin function
        | Empty -> false
        | Red tree -> lk' tree
        | Black tree -> lk' tree end
        and lk' (x1, left, right) =
          begin match Int.compare (x, x1) with
          | EQUAL -> true
          | LESS -> lk left
          | GREATER -> lk right end in
    lk dict
  let rec restore_right =
    begin function
    | Black (e, Red lt, Red ((_, Red _, _) as rt)) ->
        Red (e, (Black lt), (Black rt))
    | Black (e, Red lt, Red ((_, _, Red _) as rt)) ->
        Red (e, (Black lt), (Black rt))
    | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
        Black (rle, (Red (e, l, rll)), (Red (re, rlr, rr)))
    | Black (e, l, Red (re, rl, (Red _ as rr))) ->
        Black (re, (Red (e, l, rl)), rr)
    | dict -> dict end(* l is black, shallow rotate *)
  (* l is black, deep rotate *)(* re-color *)(* re-color *)
let rec restore_left =
  begin function
  | Black (e, Red ((_, Red _, _) as lt), Red rt) ->
      Red (e, (Black lt), (Black rt))
  | Black (e, Red ((_, _, Red _) as lt), Red rt) ->
      Red (e, (Black lt), (Black rt))
  | Black (e, Red (le, (Red _ as ll), lr), r) ->
      Black (le, ll, (Red (e, lr, r)))
  | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
      Black (lre, (Red (le, ll, lrl)), (Red (e, lrr, r)))
  | dict -> dict end(* r is black, deep rotate *)(* r is black, shallow rotate *)
(* re-color *)(* re-color *)
let rec insert (dict, x) =
  let rec ins =
    begin function
    | Empty -> Red (x, Empty, Empty)
    | Red (x1, left, right) ->
        (begin match Int.compare (x, x1) with
         | EQUAL -> Red (x, left, right)
         | LESS -> Red (x1, (ins left), right)
         | GREATER -> Red (x1, left, (ins right)) end)
    | Black (x1, left, right) ->
        (begin match Int.compare (x, x1) with
         | EQUAL -> Black (x, left, right)
         | LESS -> restore_left (Black (x1, (ins left), right))
         | GREATER -> restore_right (Black (x1, left, (ins right))) end) end in
((begin match ins dict with
| Red ((_, Red _, _) as t) -> Black t
| Red ((_, _, Red _) as t) -> Black t
| dict -> dict end)
(* re-color *)(* re-color *)(* val ins : 'a dict -> 'a dict  inserts entry *)
(* ins (Red _) may violate color invariant at root *)
(* ins (Black _) or ins (Empty) will be red/black tree *)
(* ins preserves black height *))
type nonrec intset = rbt
let empty = Empty
let insert = begin function | (x, t) -> insert (t, x) end
let member = begin function | (x, t) -> lookup t x end
let rec foldl f a t =
  let rec fo =
    begin function
    | (Empty, r) -> r
    | (Red (x, left, right), r) -> fo (right, (f (x, (fo (left, r)))))
    | (Black (x, left, right), r) -> fo (right, (f (x, (fo (left, r))))) end in
fo (t, a) end
