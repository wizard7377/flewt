open Basis 
open Table_sig
module type RBSET  =
  sig
    type nonrec key = int
    type nonrec 'a entry = (key * 'a)
    exception Error of string 
    type nonrec 'a ordSet
    val new_ : unit -> 'a ordSet
    val copy : 'a ordSet -> 'a ordSet
    val insert : 'a ordSet -> 'a entry -> unit
    val insertList : 'a ordSet -> 'a entry list -> unit
    val insertShadow : 'a ordSet -> 'a entry -> unit
    val insertLast : 'a ordSet -> 'a -> unit
    val lookup : 'a ordSet -> key -> 'a option
    val isEmpty : 'a ordSet -> bool
    val last : 'a ordSet -> 'a entry
    val clear : 'a ordSet -> unit
    val app : 'a ordSet -> ('a -> unit) -> unit
    val update : 'a ordSet -> ('a -> 'a) -> 'a ordSet
    val forall : 'a ordSet -> ('a entry -> unit) -> unit
    val exists : 'a ordSet -> ('a entry -> bool) -> bool
    val existsOpt : 'a ordSet -> ('a -> bool) -> int option
    val size : 'a ordSet -> int
    val union : 'a ordSet -> 'a ordSet -> 'a ordSet
    val difference : 'a ordSet -> 'a ordSet -> 'a ordSet
    val difference2 : 'a ordSet -> 'a ordSet -> ('a ordSet * 'a ordSet)
    val differenceModulo :
      'a ordSet -> 'b ordSet -> ('a -> 'b -> unit) -> ('a ordSet * 'b ordSet)
    val splitSets :
      'a ordSet ->
        'a ordSet ->
          ('a -> 'a -> 'a option) -> ('a ordSet * 'a ordSet * 'a ordSet)
    val intersection : 'a ordSet -> 'a ordSet -> 'a ordSet
  end


module RBSet : RBSET =
  struct
    type nonrec key = int
    type nonrec 'a entry = (key * 'a)
    type 'a dict =
      | Empty 
      | Red of ('a entry * 'a dict * 'a dict) 
      | Black of ('a entry * 'a dict * 'a dict) 
    type 'a set =
      | Set of (int * 'a dict) 
    exception Error of string 
    type nonrec 'a ordSet = 'a set ref
    let rec isEmpty =
      begin function | Set (_, Empty) -> true | Set (_, t_) -> false end
    let empty = Set (0, Empty)
    let rec singleton x = Set (1, (Red (x, Empty, Empty)))
    let compare = Int.compare
    let rec lookup (Set (n, dict)) key =
      let rec lk =
        begin function
        | Empty -> None
        | Red tree -> lk' tree
        | Black tree -> lk' tree end
        and lk' ((key1, datum1), left, right) =
          begin match General.int_to_order @@ compare key key1 with
          | EQUAL -> Some datum1
          | LESS -> lk left
          | GREATER -> lk right end in
    lk dict
let rec last (Set (n, dict)) = (n, (Option.get (lookup (Set (n, dict)) n)))
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
let rec insert (Set (n, dict), ((key, datum) as entry)) =
  let nItems = ref n in
  let rec ins =
    begin function
    | Empty -> (begin nItems := (n + 1); Red (entry, Empty, Empty) end)
    | Red (((key1, datum1) as entry1), left, right) ->
        (begin match General.int_to_order @@ compare key key1 with
         | EQUAL -> ((Red (entry1, left, right))
             (*print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n");*))
         | LESS -> Red (entry1, (ins left), right)
         | GREATER -> Red (entry1, left, (ins right)) end)
    | Black (((key1, datum1) as entry1), left, right) ->
        (begin match General.int_to_order @@ compare key key1 with
         | EQUAL -> ((Black (entry1, left, right))
             (* print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n"); *))
         | LESS -> restore_left (Black (entry1, (ins left), right))
         | GREATER -> restore_right (Black (entry1, left, (ins right))) end) end in
let dict' =
((begin match ins dict with
  | Red ((_, Red _, _) as t) -> Black t
  | Red ((_, _, Red _) as t) -> Black t
  | dict -> dict end)
(* re-color *)(* re-color *)) in
((Set (!nItems, dict'))
(* val ins : 'a dict -> 'a dict  inserts entry *)(* ins (Red _) may violate color invariant at root *)
(* ins (Black _) or ins (Empty) will be red/black tree *)
(* ins preserves black height *))
let rec insertList =
  begin function
  | (s_, []) -> s_
  | (s_, e::list) -> insertList ((insert (s_, e)), list) end
let rec insertLast (Set (n, dict), datum) =
  let Set (n', dic') = insert ((Set (n, dict)), ((n + 1), datum)) in
  Set (n', dic')
let rec insertShadow (Set (n, dict), ((key, datum) as entry)) =
  let oldEntry = ref None in
  let rec ins =
    begin function
    | Empty -> Red (entry, Empty, Empty)
    | Red (((key1, datum1) as entry1), left, right) ->
        (begin match General.int_to_order @@ compare key key1 with
         | EQUAL ->
             (begin oldEntry := Some entry1; Red (entry, left, right) end)
        | LESS -> Red (entry1, (ins left), right)
        | GREATER -> Red (entry1, left, (ins right)) end)
    | Black (((key1, datum1) as entry1), left, right) ->
        (begin match General.int_to_order @@ compare key key1 with
         | EQUAL ->
             (begin oldEntry := Some entry1; Black (entry, left, right) end)
        | LESS -> restore_left (Black (entry1, (ins left), right))
        | GREATER -> restore_right (Black (entry1, left, (ins right))) end) end in
let (dict', oldEntry') =
begin oldEntry := None;
((((begin match ins dict with
    | Red ((_, Red _, _) as t) -> Black t
    | Red ((_, _, Red _) as t) -> Black t
    | dict -> dict end))
(* re-color *)(* re-color *)),
!oldEntry) end in ((Set (n, dict'))
(* : 'a entry option ref *))
type color =
  | RedColor 
  | BlackColor 
type 'a zipper =
  | Top 
  | LeftRed of ('a entry * 'a dict * 'a zipper) 
  | LeftBlack of ('a entry * 'a dict * 'a zipper) 
  | RightRed of ('a dict * 'a entry * 'a zipper) 
  | RightBlack of ('a dict * 'a entry * 'a zipper) 
let rec delete (Set (nItems, t), k) =
  let rec zip =
    begin function
    | (Top, t) -> t
    | (LeftRed (x, b, z), a) -> zip (z, (Red (x, a, b)))
    | (LeftBlack (x, b, z), a) -> zip (z, (Black (x, a, b)))
    | (RightRed (a, x, z), b) -> zip (z, (Red (x, a, b)))
    | (RightBlack (a, x, z), b) -> zip (z, (Black (x, a, b))) end in
let rec bbZip =
  begin function
  | (Top, t) -> (true, t)
  | (LeftBlack (x, Red (y, c, d), z), a) ->
      bbZip ((LeftRed (x, c, (LeftBlack (y, d, z)))), a)
  | (LeftRed (x, Red (y, c, d), z), a) ->
      bbZip ((LeftRed (x, c, (LeftBlack (y, d, z)))), a)
  | (LeftBlack (x, Black (w, Red (y, c, d), e), z), a) ->
      bbZip ((LeftBlack (x, (Black (y, c, (Red (w, d, e)))), z)), a)
  | (LeftRed (x, Black (w, Red (y, c, d), e), z), a) ->
      bbZip ((LeftRed (x, (Black (y, c, (Red (w, d, e)))), z)), a)
  | (LeftBlack (x, Black (y, c, Red (w, d, e)), z), a) ->
      (false, (zip (z, (Black (y, (Black (x, a, c)), (Black (w, d, e)))))))
  | (LeftRed (x, Black (y, c, Red (w, d, e)), z), a) ->
      (false, (zip (z, (Red (y, (Black (x, a, c)), (Black (w, d, e)))))))
  | (LeftRed (x, Black (y, c, d), z), a) ->
      (false, (zip (z, (Black (x, a, (Red (y, c, d)))))))
  | (LeftBlack (x, Black (y, c, d), z), a) ->
      bbZip (z, (Black (x, a, (Red (y, c, d)))))
  | (RightBlack (Red (y, c, d), x, z), b) ->
      bbZip ((RightRed (d, x, (RightBlack (c, y, z)))), b)
  | (RightRed (Red (y, c, d), x, z), b) ->
      bbZip ((RightRed (d, x, (RightBlack (c, y, z)))), b)
  | (RightBlack (Black (y, Red (w, c, d), e), x, z), b) ->
      bbZip ((RightBlack ((Black (w, c, (Red (y, d, e)))), x, z)), b)
  | (RightRed (Black (y, Red (w, c, d), e), x, z), b) ->
      bbZip ((RightRed ((Black (w, c, (Red (y, d, e)))), x, z)), b)
  | (RightBlack (Black (y, c, Red (w, d, e)), x, z), b) ->
      (false, (zip (z, (Black (y, c, (Black (x, (Red (w, d, e)), b)))))))
  | (RightRed (Black (y, c, Red (w, d, e)), x, z), b) ->
      (false, (zip (z, (Red (y, c, (Black (x, (Red (w, d, e)), b)))))))
  | (RightRed (Black (y, c, d), x, z), b) ->
      (false, (zip (z, (Black (x, (Red (y, c, d)), b)))))
  | (RightBlack (Black (y, c, d), x, z), b) ->
      bbZip (z, (Black (x, (Red (y, c, d)), b)))
  | (z, t) -> (false, (zip (z, t))) end(* case 2R *)
  (* case 2R *)(* case 4R *)(* case 4R *)
  (* case 3R *)(* case 3R *)(* case 1R *)
  (* case 1R *)(* case 2L *)(* case 2L *)
  (* case 4L *)(* case 4L *)(* case 3L *)
  (* case 3L *)(* case 1L *)(* case 1L *) in
let rec delMin =
  begin function
  | (Red (y, Empty, b), z) -> (y, (false, (zip (z, b))))
  | (Black (y, Empty, b), z) -> (y, (bbZip (z, b)))
  | (Red (y, a, b), z) -> delMin (a, (LeftRed (y, b, z)))
  | (Black (y, a, b), z) -> delMin (a, (LeftBlack (y, b, z))) end in
let rec joinBlack =
  begin function
  | (a, Empty, z) -> Stdlib.snd (bbZip (z, a))
  | (Empty, b, z) -> Stdlib.snd (bbZip (z, b))
  | (a, b, z) ->
      let (x, (needB, b')) = delMin (b, Top) in
      if needB
      then begin Stdlib.snd (bbZip (z, (Black (x, a, b')))) end
        else begin zip (z, (Black (x, a, b'))) end end in
let rec joinRed =
begin function
| (Empty, Empty, z) -> zip (z, Empty)
| (a, b, z) ->
    let (x, (needB, b')) = delMin (b, Top) in
    if needB then begin Stdlib.snd (bbZip (z, (Red (x, a, b')))) end
      else begin zip (z, (Red (x, a, b'))) end end in
let rec del =
begin function
| (Empty, z) -> raise (Error "not found\n")
| (Red (((k', _) as y), a, b), z) ->
    (((begin match General.int_to_order @@ compare k k' with
       | LESS -> del (a, (LeftRed (y, b, z)))
       | EQUAL -> joinRed (a, b, z)
       | GREATER -> del (b, (RightRed (a, y, z))) end))
(* end case *))
| (Black (((k', _) as y), a, b), z) ->
    (((begin match General.int_to_order @@ compare k k' with
       | LESS -> del (a, (LeftBlack (y, b, z)))
       | EQUAL -> joinBlack (a, b, z)
       | GREATER -> del (b, (RightBlack (a, y, z))) end))
(* end case *)) end in ((Set ((nItems - 1), (del (t, Top))))
(* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *))
let rec app f (Set (n, dict)) =
  let rec ap =
    begin function
    | Empty -> ()
    | Red tree -> ap' tree
    | Black tree -> ap' tree end
    and ap' (((_, datum) as entry1), left, right) =
      begin ap left; f datum; ap right end in
ap dict
let rec update f (Set (n, dict)) =
  let rec upd =
    begin function
    | Empty -> Empty
    | Red tree -> Red (upd' tree)
    | Black tree -> Black (upd' tree) end
    and upd' (((k, datum) as entry1), left, right) =
      let left' = upd left in
      let datum' = f datum in
      let right' = upd right in ((k, datum'), left', right') in
Set (n, (upd dict))
let rec forall (Set (n, dict)) f =
  let rec ap =
    begin function
    | Empty -> ()
    | Red tree -> ap' tree
    | Black tree -> ap' tree end
    and ap' (entry, left, right) = begin ap left; f entry; ap right end in
ap dict
let rec existsOpt (Set (n, dict)) f =
  let rec ap =
    begin function
    | Empty -> None
    | Red tree -> ap' tree
    | Black tree -> ap' tree end
    and ap' (((k, d) as entry), left, right) =
      if f d then begin (begin Stdlib.print_string "SUCCESS\n"; Some k end) end
    else begin
      (begin Stdlib.print_string "FAILED\n";
       (begin match ap left with | None -> ap right | Some res -> Some res end) end) end in
ap dict
let rec exists (Set (n, dict)) f =
  let rec ap =
    begin function
    | Empty -> false
    | Red tree -> ap' tree
    | Black tree -> ap' tree end
    and ap' (entry, left, right) = if f entry then begin true end
      else begin if ap left then begin true end else begin ap right end end in
ap dict
let rec setsize (Set (n, _)) = n
let rec left =
  begin function
  | (Empty, rest) -> rest
  | ((Red (_, a, _) as t), rest) -> left (a, (t :: rest))
  | ((Black (_, a, _) as t), rest) -> left (a, (t :: rest)) end
let rec next =
  begin function
  | (Red (_, _, b) as t)::rest -> (t, (left (b, rest)))
  | (Black (_, _, b) as t)::rest -> (t, (left (b, rest)))
  | _ -> (Empty, []) end
let rec start m = left (m, [])
type 'a digit =
  | ZERO 
  | ONE of ('a entry * 'a dict * 'a digit) 
  | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit) 
let rec addItem (a, l) =
  let rec incr =
    begin function
    | (a, t, ZERO) -> ONE (a, t, ZERO)
    | (a1, t1, ONE (a2, t2, r)) -> TWO (a1, t1, a2, t2, r)
    | (a1, t1, TWO (a2, t2, a3, t3, r)) ->
        ONE (a1, t1, (incr (a2, (Black (a3, t3, t2)), r))) end in
incr (a, Empty, l)
let rec linkAll t =
  let rec link =
    begin function
    | (t, ZERO) -> t
    | (t1, ONE (a, t2, r)) -> link ((Black (a, t2, t1)), r)
    | (t, TWO (a1, t1, a2, t2, r)) ->
        link ((Black (a1, (Red (a2, t2, t1)), t)), r) end in
link (Empty, t)
let rec getEntry =
  begin function | Red (x, _, _) -> x | Black (x, _, _) -> x end
let rec union (Set (n1, s1), Set (n2, s2)) =
  let rec ins =
    begin function
    | ((Empty, _), n, result) -> (n, result)
    | ((Red (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result)))
    | ((Black (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result))) end in
let rec union' (t1, t2, n, result) =
  begin match ((next t1), (next t2)) with
  | ((Empty, _), (Empty, _)) -> (n, result)
  | ((Empty, _), t2) -> ins (t2, n, result)
  | (t1, (Empty, _)) -> ins (t1, n, result)
  | ((tree1, r1), (tree2, r2)) ->
      let (x, d1) as e1 = getEntry tree1 in
      let (y, d2) as e2 = getEntry tree2 in
      (begin match General.int_to_order @@ compare x y with
       | LESS -> union' (r1, t2, (n + 1), (addItem (e1, result)))
       | EQUAL -> union' (r1, r2, (n + 1), (addItem (e1, result)))
       | GREATER -> union' (t1, r2, (n + 1), (addItem (e2, result))) end) end in
begin match s1 with
| Empty -> Set (n2, s2)
| _ ->
    (begin match s2 with
     | Empty -> Set (n1, s1)
     | _ ->
         let (n, result) = union' ((start s1), (start s2), 0, ZERO) in
         Set (n, (linkAll result)) end) end
let rec intersection (Set (_, s1), Set (_, s2)) =
  let rec intersect (t1, t2, n, result) =
    begin match ((next t1), (next t2)) with
    | ((Empty, r), (tree, r')) -> (n, result)
    | ((tree, r), (Empty, r')) -> (n, result)
    | ((tree1, r1), (tree2, r2)) ->
        let (x, d1) as e1 = getEntry tree1 in
        let (y, d2) as e2 = getEntry tree2 in
        (begin match General.int_to_order @@ compare x y with
         | LESS -> intersect (r1, t2, n, result)
         | EQUAL -> intersect (r1, r2, (n + 1), (addItem (e1, result)))
         | GREATER -> intersect (t1, r2, n, result) end) end in
let (n, result) = intersect ((start s1), (start s2), 0, ZERO) in
Set (n, (linkAll result))
let rec difference (Set (_, s1), Set (_, s2)) =
  let rec ins =
    begin function
    | ((Empty, _), n, result) -> (n, result)
    | ((Red (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result)))
    | ((Black (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result))) end in
let rec diff (t1, t2, n, result) =
  begin match ((next t1), (next t2)) with
  | ((Empty, _), _) -> (n, result)
  | (t1, (Empty, _)) -> ins (t1, n, result)
  | ((tree1, r1), (tree2, r2)) ->
      let (x, d1) as e1 = getEntry tree1 in
      let (y, d2) as e2 = getEntry tree2 in
      (begin match General.int_to_order @@ compare x y with
       | LESS -> diff (r1, t2, (n + 1), (addItem (e1, result)))
       | EQUAL -> diff (r1, r2, n, result)
       | GREATER -> diff (t1, r2, n, result) end) end in
let (n, result) = diff ((start s1), (start s2), 0, ZERO) in
Set (n, (linkAll result))
let rec difference2 (Set (_, s1), Set (_, s2)) =
  let rec ins =
    begin function
    | ((Empty, _), n, result) -> (n, result)
    | ((Red (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result)))
    | ((Black (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result))) end in
let rec diff (t1, t2, (n1, result1), (n2, result2)) =
  begin match ((next t1), (next t2)) with
  | ((Empty, _), t2) -> ((n1, result1), (ins (t2, n2, result2)))
  | (t1, (Empty, _)) -> ((ins (t1, n1, result1)), (n2, result2))
  | ((tree1, r1), (tree2, r2)) ->
      let (x, d1) as e1 = getEntry tree1 in
      let (y, d2) as e2 = getEntry tree2 in
      (begin match General.int_to_order @@ compare x y with
       | LESS ->
           diff (r1, t2, ((n1 + 1), (addItem (e1, result1))), (n2, result2))
       | EQUAL -> diff (r1, r2, (n1, result1), (n2, result2))
       | GREATER ->
           diff (t1, r2, (n1, result1), ((n2 + 1), (addItem (e2, result2)))) end) end in
let ((n1, result1), (n2, result2)) =
  diff ((start s1), (start s2), (0, ZERO), (0, ZERO)) in
((Set (n1, (linkAll result1))), (Set (n2, (linkAll result2))))
let rec diffMod (f_) (Set (_, s1), Set (_, s2)) =
  let rec ins =
    begin function
    | ((Empty, _), n, result) -> (n, result)
    | ((Red (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result)))
    | ((Black (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result))) end in
let rec diff (t1, t2, (n1, result1), (n2, result2)) =
  begin match ((next t1), (next t2)) with
  | ((Empty, _), t2) -> ((n1, result1), (ins (t2, n2, result2)))
  | (t1, (Empty, _)) -> ((ins (t1, n1, result1)), (n2, result2))
  | ((tree1, r1), (tree2, r2)) ->
      let (x, d1) as e1 = getEntry tree1 in
      let (y, d2) as e2 = getEntry tree2 in
      (begin match General.int_to_order @@ compare x y with
       | LESS ->
           diff (r1, t2, ((n1 + 1), (addItem (e1, result1))), (n2, result2))
       | EQUAL ->
           (begin f_ d1 d2; diff (r1, r2, (n1, result1), (n2, result2)) end)
        | GREATER ->
            diff (t1, r2, (n1, result1), ((n2 + 1), (addItem (e2, result2)))) end) end in
let ((n1, result1), (n2, result2)) =
diff ((start s1), (start s2), (0, ZERO), (0, ZERO)) in
((Set (n1, (linkAll result1))), (Set (n2, (linkAll result2))))
let rec splitSets (f_) (Set (_, s1), Set (_, s2)) =
  let rec ins =
    begin function
    | ((Empty, _), n, result) -> (n, result)
    | ((Red (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result)))
    | ((Black (x, _, _), r), n, result) ->
        ins ((next r), (n + 1), (addItem (x, result))) end in
let rec split
  (t1, t2, ((n, result) as nr), ((n1, result1) as nr1),
   ((n2, result2) as nr2))
  =
  begin match ((next t1), (next t2)) with
  | ((Empty, _), t2) -> (nr, nr1, (ins (t2, n2, result2)))
  | (t1, (Empty, _)) -> (nr, (ins (t1, n1, result1)), nr2)
  | ((tree1, r1), (tree2, r2)) ->
      let (x, d1) as e1 = getEntry tree1 in
      let (y, d2) as e2 = getEntry tree2 in
      (begin match General.int_to_order @@ compare x y with
       | LESS -> split (r1, t2, nr, ((n1 + 1), (addItem (e1, result1))), nr2)
       | EQUAL ->
           (begin match f_ d1 d2 with
            | None ->
                split
                  (r1, r2, nr, ((n1 + 1), (addItem (e1, result1))),
                    ((n2 + 1), (addItem (e2, result2))))
            | Some d ->
                split
                  (r1, r2, ((n + 1), (addItem ((x, d), result))), nr1, nr2) end)
        | GREATER ->
            split (t1, r2, nr, nr1, ((n2 + 1), (addItem (e2, result2)))) end) end in
let ((n, r), (n1, r1), (n2, r2)) =
split ((start s1), (start s2), (0, ZERO), (0, ZERO), (0, ZERO)) in
((Set (n, (linkAll r))), (Set (n1, (linkAll r1))), (Set (n2, (linkAll r2))))
let rec new_ () = ref empty
let rec copy (s_) = let s'_ = new_ () in begin s'_ := !s_; s'_ end
let insert =
  begin function
  | set -> (begin function | entry -> set := insert (!set, entry) end) end
let insertLast =
  begin function
  | set -> (begin function | datum -> set := insertLast (!set, datum) end) end
let insertList =
  begin function
  | set -> (begin function | list -> set := insertList (!set, list) end) end
let insertShadow =
  begin function
  | set -> (begin function | entry -> set := insertShadow (!set, entry) end) end
let isEmpty = begin function | ordSet -> isEmpty !ordSet end
let last = begin function | ordSet -> last !ordSet end
let lookup =
  begin function | ordSet -> (begin function | key -> lookup !ordSet key end) end
let clear = begin function | ordSet -> ordSet := empty end
let app =
  begin function | ordSet -> (begin function | f -> app f !ordSet end) end
let update =
  begin function
  | ordSet ->
      (begin function | f -> (begin ordSet := (update f !ordSet); ordSet end) end) end
let forall =
  begin function | ordSet -> (begin function | f -> forall !ordSet f end) end
let exists =
  begin function | ordSet -> (begin function | f -> exists !ordSet f end) end
let existsOpt =
  begin function | ordSet -> (begin function | f -> existsOpt !ordSet f end) end
let rec size (s_) = setsize !s_
let difference =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           let set = new_ () in
           (begin set := (difference (!set1, !set2)); set end) end) end
let difference2 =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           let r1 = new_ () in
           let r2 = new_ () in
           let (rset1, rset2) = difference2 (!set1, !set2) in
           (begin r1 := rset1; r2 := rset2; (r1, r2) end) end) end
let differenceModulo =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           (begin function
            | f_ ->
                let r1 = new_ () in
                let r2 = new_ () in
                let (rset1, rset2) = diffMod f_ (!set1, !set2) in
                (begin r1 := rset1; r2 := rset2; (r1, r2) end) end) end) end
let splitSets =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           (begin function
            | f_ ->
                let r1 = new_ () in
                let r2 = new_ () in
                let r = new_ () in
                let (rset, rset1, rset2) = splitSets f_ (!set1, !set2) in
                (begin r := rset; r1 := rset1; r2 := rset2; (r, r1, r2) end) end) end) end
let intersection =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           let set = new_ () in
           (begin set := (intersection (!set1, !set2)); set end) end) end
let union =
  begin function
  | set1 ->
      (begin function
       | set2 ->
           let set = new_ () in (begin set := (union (!set1, !set2)); set end) end) end
end
