
module RedBlackTree(RedBlackTree:sig
                                   type nonrec key'
                                   val compare : (key' * key') -> order
                                 end) : TABLE =
  struct
    type nonrec key = key'
    type nonrec 'a entry = (key * 'a)
    type 'a dict =
      | Empty 
      | Red of ('a entry * 'a dict * 'a dict) 
      | Black of ('a entry * 'a dict * 'a dict) 
    type nonrec 'a __Table = 'a dict ref
    let rec lookup dict key =
      let lk =
        function
        | Empty -> NONE
        | Red tree -> lk' tree
        | Black tree -> lk' tree
      and lk' ((key1, datum1), left, right) =
        match compare (key, key1) with
        | EQUAL -> SOME datum1
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
    let rec insert (dict, ((key, datum) as entry)) =
      let ins =
        function
        | Empty -> Red (entry, Empty, Empty)
        | Red (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> Red (entry, left, right)
             | LESS -> Red (entry1, (ins left), right)
             | GREATER -> Red (entry1, left, (ins right)))
        | Black (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> Black (entry, left, right)
             | LESS -> restore_left (Black (entry1, (ins left), right))
             | GREATER -> restore_right (Black (entry1, left, (ins right)))) in
      match ins dict with
      | Red ((_, Red _, _) as t) -> Black t
      | Red ((_, _, Red _) as t) -> Black t
      | dict -> dict
    let rec insertShadow (dict, ((key, datum) as entry)) =
      let oldEntry = ref NONE in
      let ins =
        function
        | Empty -> Red (entry, Empty, Empty)
        | Red (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> ((:=) oldEntry SOME entry1; Red (entry, left, right))
             | LESS -> Red (entry1, (ins left), right)
             | GREATER -> Red (entry1, left, (ins right)))
        | Black (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL ->
                 ((:=) oldEntry SOME entry1; Black (entry, left, right))
             | LESS -> restore_left (Black (entry1, (ins left), right))
             | GREATER -> restore_right (Black (entry1, left, (ins right)))) in
      oldEntry := NONE;
      (((match ins dict with
         | Red ((_, Red _, _) as t) -> Black t
         | Red ((_, _, Red _) as t) -> Black t
         | dict -> dict)), (!oldEntry))
    let rec app f dict =
      let ap =
        function
        | Empty -> ()
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' (entry1, left, right) = ap left; f entry1; ap right in 
        ap dict
    let rec new__ n = ref Empty
    let insert =
      function
      | table -> (function | entry -> (:=) table insert ((!table), entry))
    let insertShadow =
      function
      | table ->
          (function
           | entry ->
               let (dict, oldEntry) = insertShadow ((!table), entry) in
               (table := dict; oldEntry))
    let lookup = function | table -> (function | key -> lookup (!table) key)
    let clear = function | table -> table := Empty
    let app = function | f -> (function | table -> app f (!table))
  end 
module StringRedBlackTree =
  (Make_RedBlackTree)(struct
                        type nonrec key' =
                          ((string)(* functor RedBlackTree *)(* ignore size hint *)
                          (* re-color *)(* re-color *)
                          (* : 'a entry option ref *)
                          (* use non-imperative version? *)
                          (* re-color *)(* re-color *)
                          (* ins preserves black height *)
                          (* ins (Black _) or ins (Empty) will be red/black tree *)
                          (* ins (Red _) may violate color invariant at root *)
                          (* val ins : 'a dict -> 'a dict  inserts entry *)
                          (* r is black, deep rotate *)
                          (* r is black, shallow rotate *)
                          (* re-color *)(* re-color *)
                          (* the color invariant may be violated only at the root of left child *)
                          (* restore_left is like restore_right, except *)
                          (* l is black, shallow rotate *)
                          (* l is black, deep rotate *)
                          (* re-color *)(* re-color *)
                          (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
                          (* val restore_right : 'a dict -> 'a dict *)
                          (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)
                          (* Representation Invariants *)
                          (* considered black *)(* Author: Frank Pfenning *)
                          (* Red/Black Trees *))
                        let compare = String.compare
                      end)
module IntRedBlackTree =
  (Make_RedBlackTree)(struct
                        type nonrec key' = int
                        let compare = Int.compare
                      end);;
