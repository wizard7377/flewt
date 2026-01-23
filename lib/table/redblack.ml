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
    type nonrec 'a table_ = 'a dict ref
    let rec lookup dict key =
      let rec lk =
        begin function
        | Empty -> None
        | Red tree -> lk' tree
        | Black tree -> lk' tree end
        and lk' ((key1, datum1), left, right) =
          begin match compare (key, key1) with
          | EQUAL -> Some datum1
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
let rec insert (dict, ((key, datum) as entry)) =
  let rec ins =
    begin function
    | Empty -> Red (entry, Empty, Empty)
    | Red (((key1, datum1) as entry1), left, right) ->
        (begin match compare (key, key1) with
         | EQUAL -> Red (entry, left, right)
         | LESS -> Red (entry1, (ins left), right)
         | GREATER -> Red (entry1, left, (ins right)) end)
    | Black (((key1, datum1) as entry1), left, right) ->
        (begin match compare (key, key1) with
         | EQUAL -> Black (entry, left, right)
         | LESS -> restore_left (Black (entry1, (ins left), right))
         | GREATER -> restore_right (Black (entry1, left, (ins right))) end) end in
((begin match ins dict with
| Red ((_, Red _, _) as t) -> Black t
| Red ((_, _, Red _) as t) -> Black t
| dict -> dict end)
(* re-color *)(* re-color *)(* val ins : 'a dict -> 'a dict  inserts entry *)
(* ins (Red _) may violate color invariant at root *)
(* ins (Black _) or ins (Empty) will be red/black tree *)
(* ins preserves black height *))
let rec insertShadow (dict, ((key, datum) as entry)) =
  let oldEntry = ref None in
  let rec ins =
    begin function
    | Empty -> Red (entry, Empty, Empty)
    | Red (((key1, datum1) as entry1), left, right) ->
        (begin match compare (key, key1) with
         | EQUAL ->
             (begin (:=) oldEntry Some entry1; Red (entry, left, right) end)
        | LESS -> Red (entry1, (ins left), right)
        | GREATER -> Red (entry1, left, (ins right)) end)
    | Black (((key1, datum1) as entry1), left, right) ->
        (begin match compare (key, key1) with
         | EQUAL ->
             (begin (:=) oldEntry Some entry1; Black (entry, left, right) end)
        | LESS -> restore_left (Black (entry1, (ins left), right))
        | GREATER -> restore_right (Black (entry1, left, (ins right))) end) end in
((begin oldEntry := None;
((((begin match ins dict with
    | Red ((_, Red _, _) as t) -> Black t
    | Red ((_, _, Red _) as t) -> Black t
    | dict -> dict end))
(* re-color *)(* re-color *)),
!oldEntry) end)
(* : 'a entry option ref *))
let rec app f dict =
  let rec ap =
    begin function
    | Empty -> ()
    | Red tree -> ap' tree
    | Black tree -> ap' tree end
    and ap' (entry1, left, right) = begin ap left; f entry1; ap right end in
ap dict
let rec new_ n = ref Empty
let insert =
  begin function
  | table -> (begin function | entry -> (:=) table insert (!table, entry) end) end
let insertShadow =
  begin function
  | table ->
      (begin function
       | entry ->
           let (dict, oldEntry) = insertShadow (!table, entry) in
           (begin table := dict; oldEntry end) end) end
let lookup =
  begin function | table -> (begin function | key -> lookup !table key end) end
let clear = begin function | table -> table := Empty end
let app = begin function | f -> (begin function | table -> app f !table end) end
end 
module StringRedBlackTree =
  (RedBlackTree)(struct
                        type nonrec key' = string
                        let compare = String.compare
                      end)
module IntRedBlackTree =
  (RedBlackTree)(struct
                        type nonrec key' = int
                        let compare = Int.compare
                      end)