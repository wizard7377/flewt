
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
      | Red of
      (((int)(* considered black *)(* Copied from src/table/red-black-tree.fun *)
      (* Author: Frank Pfenning *)(* Specialized for subordination *)
      (* Persistent red/black trees *)) * rbt * rbt) 
      | Black of (int * rbt * rbt) 
    let rec lookup dict x =
      let lk =
        function
        | Empty -> false__
        | Red tree -> lk' tree
        | Black tree -> lk' tree
      and lk' (x1, left, right) =
        match Int.compare (x, x1) with
        | EQUAL -> true__
        | LESS -> lk left
        | GREATER -> lk right in
      lk dict
    let rec restore_right =
      function
      | Black (e, Red lt, Red ((_, Red _, _) as rt)) ->
          Red (e, (Black lt), (Black rt))
      | Black (e, Red lt, Red ((_, _, Red _) as rt)) ->
          Red (e, (Black lt), (Black rt))
      | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
          Black (rle, (Red (e, l, rll)), (Red (re, rlr, rr)))
      | Black (e, l, Red (re, rl, (Red _ as rr))) ->
          Black (re, (Red (e, l, rl)), rr)
      | dict -> dict
    let rec restore_left =
      function
      | Black (e, Red ((_, Red _, _) as lt), Red rt) ->
          Red (e, (Black lt), (Black rt))
      | Black (e, Red ((_, _, Red _) as lt), Red rt) ->
          Red (e, (Black lt), (Black rt))
      | Black (e, Red (le, (Red _ as ll), lr), r) ->
          Black (le, ll, (Red (e, lr, r)))
      | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
          Black (lre, (Red (le, ll, lrl)), (Red (e, lrr, r)))
      | dict -> dict
    let rec insert (dict, x) =
      let ins =
        function
        | Empty -> Red (x, Empty, Empty)
        | Red (x1, left, right) ->
            (match Int.compare (x, x1) with
             | EQUAL -> Red (x, left, right)
             | LESS -> Red (x1, (ins left), right)
             | GREATER -> Red (x1, left, (ins right)))
        | Black (x1, left, right) ->
            (match Int.compare (x, x1) with
             | EQUAL -> Black (x, left, right)
             | LESS -> restore_left (Black (x1, (ins left), right))
             | GREATER -> restore_right (Black (x1, left, (ins right)))) in
      match ins dict with
      | Red ((_, Red _, _) as t) -> Black t
      | Red ((_, _, Red _) as t) -> Black t
      | dict -> dict
    type nonrec intset =
      ((rbt)(* re-color *)(* re-color *)
      (* ins preserves black height *)(* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins (Red _) may violate color invariant at root *)
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* r is black, deep rotate *)(* r is black, shallow rotate *)
      (* re-color *)(* re-color *)(* the color invariant may be violated only at the root of left child *)
      (* restore_left is like restore_right, except *)
      (* l is black, shallow rotate *)(* l is black, deep rotate *)
      (* re-color *)(* re-color *)(*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
      (* val restore_right : 'a dict -> 'a dict *)(*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)
      (* Representation Invariants *))
    let empty = Empty
    let insert = function | (x, t) -> insert (t, x)
    let member = function | (x, t) -> lookup t x
    let rec foldl f a t =
      let fo =
        function
        | (Empty, r) -> r
        | (Red (x, left, right), r) -> fo (right, (f (x, (fo (left, r)))))
        | (Black (x, left, right), r) -> fo (right, (f (x, (fo (left, r))))) in
      fo (t, a)
  end ;;
