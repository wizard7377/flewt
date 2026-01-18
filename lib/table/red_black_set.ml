
(* Sets *)
(* Author: Brigitte Pientka *)
(* This provides a common interface to ordered sets *)
(* based on red/black trees *)
module type RBSET  =
  sig
    type nonrec key = int
    (* parameter *)
    type nonrec 'a entry = (key * 'a)
    exception Error of string 
    type nonrec 'a ordSet
    val new__ : unit -> 'a ordSet
    val copy : 'a ordSet -> 'a ordSet
    val insert : 'a ordSet -> 'a entry -> unit
    val insertList : 'a ordSet -> 'a entry list -> unit
    val insertShadow : 'a ordSet -> 'a entry -> unit
    val insertLast : 'a ordSet -> 'a -> unit
    (*  val delete : 'a ordSet -> key -> unit*)
    val lookup : 'a ordSet -> key -> 'a option
    val isEmpty : 'a ordSet -> bool
    val last : 'a ordSet -> 'a entry
    val clear : 'a ordSet -> unit
    (* Applies f:'a -> unit to all entries in the set
     pre-order traversal *)
    val app : 'a ordSet -> ('a -> unit) -> unit
    val update : 'a ordSet -> ('a -> 'a) -> 'a ordSet
    (* Applies f:'a entry -> unit to all entries in the set
     pre-order traversal *)
    val forall : 'a ordSet -> ('a entry -> unit) -> unit
    (*  val exists : 'a ordSet -> ('a entry -> 'b option) -> ('a entry  key * 'a *)
    val exists : 'a ordSet -> ('a entry -> bool) -> bool
    val existsOpt : 'a ordSet -> ('a -> bool) -> int option
    val size : 'a ordSet -> int
    val union : 'a ordSet -> 'a ordSet -> 'a ordSet
    val difference : 'a ordSet -> 'a ordSet -> 'a ordSet
    val difference2 : 'a ordSet -> 'a ordSet -> ('a ordSet * 'a ordSet)
    val differenceModulo :
      'a ordSet -> 'b ordSet -> ('a -> 'b -> unit) -> ('a ordSet * 'b ordSet)
    (* splits two sets into S1, S2, S3 *)
    val splitSets :
      'a ordSet ->
        'a ordSet ->
          ('a -> 'a -> 'a option) -> ('a ordSet * 'a ordSet * 'a ordSet)
    val intersection : 'a ordSet -> 'a ordSet -> 'a ordSet
  end;;




(* redblack-set.sml
 *
 * This code is based on Chris Okasaki's implementation of
 * red-black trees.  The linear-time tree construction code is
 * based on the paper "Constructing red-black trees" by Hinze,
 * and the delete function is based on the description in Cormen,
 * Leiserson, and Rivest.
 *
 * A red-black tree should satisfy the following two invariants:
 *
 *   Red Invariant: each red node has a black parent.
 *
 *   Black Condition: each path from the root to an empty node has the
 *     same number of black nodes (the tree's black height).
 *
 * The Red condition implies that the root is always black and the Black
 * condition implies that any node with only one child will be black and
 * its child will be a red leaf.
 *)
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
      function | Set (_, Empty) -> true__ | Set (_, T) -> false__
    let empty = Set (0, Empty)
    let rec singleton x = Set (1, (Red (x, Empty, Empty)))
    let compare = Int.compare
    (* Representation Invariants *)
    (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)
    let rec lookup (Set (n, dict)) key =
      let rec lk =
        function
        | Empty -> None
        | Red tree -> lk' tree
        | Black tree -> lk' tree
      and lk' ((key1, datum1), left, right) =
        match compare (key, key1) with
        | EQUAL -> Some datum1
        | LESS -> lk left
        | GREATER -> lk right in
      lk dict
    let rec last (Set (n, dict)) = (n, (valOf (lookup (Set (n, dict)) n)))
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
    let rec insert (Set (n, dict), ((key, datum) as entry)) =
      let nItems = ref n in
      let rec ins =
        function
        | Empty -> ((nItems := n) + 1; Red (entry, Empty, Empty))
        | Red (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> Red (entry1, left, right)
             | LESS -> Red (entry1, (ins left), right)
             | GREATER -> Red (entry1, left, (ins right)))
        | Black (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> Black (entry1, left, right)
             | LESS -> restore_left (Black (entry1, (ins left), right))
             | GREATER -> restore_right (Black (entry1, left, (ins right)))) in
      let dict' =
        match ins dict with
        | Red ((_, Red _, _) as t) -> Black t
        | Red ((_, _, Red _) as t) -> Black t
        | dict -> dict in
      Set ((!nItems), dict')
    let rec insertList =
      function
      | (S, nil) -> S
      | (S, e::list) -> insertList ((insert (S, e)), list)
    let rec insertLast (Set (n, dict), datum) =
      let Set (n', dic') = insert ((Set (n, dict)), ((n + 1), datum)) in
      Set (n', dic')
    let rec insertShadow (Set (n, dict), ((key, datum) as entry)) =
      let oldEntry = ref None in
      let rec ins =
        function
        | Empty -> Red (entry, Empty, Empty)
        | Red (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> ((:=) oldEntry Some entry1; Red (entry, left, right))
             | LESS -> Red (entry1, (ins left), right)
             | GREATER -> Red (entry1, left, (ins right)))
        | Black (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL ->
                 ((:=) oldEntry Some entry1; Black (entry, left, right))
             | LESS -> restore_left (Black (entry1, (ins left), right))
             | GREATER -> restore_right (Black (entry1, left, (ins right)))) in
      let (dict', oldEntry') =
        oldEntry := None;
        (((match ins dict with
           | Red ((_, Red _, _) as t) -> Black t
           | Red ((_, _, Red _) as t) -> Black t
           | dict -> dict)), (!oldEntry)) in
      Set (n, dict')
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
        function
        | (Top, t) -> t
        | (LeftRed (x, b, z), a) -> zip (z, (Red (x, a, b)))
        | (LeftBlack (x, b, z), a) -> zip (z, (Black (x, a, b)))
        | (RightRed (a, x, z), b) -> zip (z, (Red (x, a, b)))
        | (RightBlack (a, x, z), b) -> zip (z, (Black (x, a, b))) in
      let rec bbZip =
        function
        | (Top, t) -> (true__, t)
        | (LeftBlack (x, Red (y, c, d), z), a) ->
            bbZip ((LeftRed (x, c, (LeftBlack (y, d, z)))), a)
        | (LeftRed (x, Red (y, c, d), z), a) ->
            bbZip ((LeftRed (x, c, (LeftBlack (y, d, z)))), a)
        | (LeftBlack (x, Black (w, Red (y, c, d), e), z), a) ->
            bbZip ((LeftBlack (x, (Black (y, c, (Red (w, d, e)))), z)), a)
        | (LeftRed (x, Black (w, Red (y, c, d), e), z), a) ->
            bbZip ((LeftRed (x, (Black (y, c, (Red (w, d, e)))), z)), a)
        | (LeftBlack (x, Black (y, c, Red (w, d, e)), z), a) ->
            (false__,
              (zip (z, (Black (y, (Black (x, a, c)), (Black (w, d, e)))))))
        | (LeftRed (x, Black (y, c, Red (w, d, e)), z), a) ->
            (false__,
              (zip (z, (Red (y, (Black (x, a, c)), (Black (w, d, e)))))))
        | (LeftRed (x, Black (y, c, d), z), a) ->
            (false__, (zip (z, (Black (x, a, (Red (y, c, d)))))))
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
            (false__,
              (zip (z, (Black (y, c, (Black (x, (Red (w, d, e)), b)))))))
        | (RightRed (Black (y, c, Red (w, d, e)), x, z), b) ->
            (false__,
              (zip (z, (Red (y, c, (Black (x, (Red (w, d, e)), b)))))))
        | (RightRed (Black (y, c, d), x, z), b) ->
            (false__, (zip (z, (Black (x, (Red (y, c, d)), b)))))
        | (RightBlack (Black (y, c, d), x, z), b) ->
            bbZip (z, (Black (x, (Red (y, c, d)), b)))
        | (z, t) -> (false__, (zip (z, t))) in
      let rec delMin =
        function
        | (Red (y, Empty, b), z) -> (y, (false__, (zip (z, b))))
        | (Black (y, Empty, b), z) -> (y, (bbZip (z, b)))
        | (Red (y, a, b), z) -> delMin (a, (LeftRed (y, b, z)))
        | (Black (y, a, b), z) -> delMin (a, (LeftBlack (y, b, z))) in
      let rec joinBlack =
        function
        | (a, Empty, z) -> ((fun (_, r) -> r)) (bbZip (z, a))
        | (Empty, b, z) -> ((fun (_, r) -> r)) (bbZip (z, b))
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, Top) in
            if needB
            then ((fun (_, r) -> r)) (bbZip (z, (Black (x, a, b'))))
            else zip (z, (Black (x, a, b'))) in
      let rec joinRed =
        function
        | (Empty, Empty, z) -> zip (z, Empty)
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, Top) in
            if needB
            then ((fun (_, r) -> r)) (bbZip (z, (Red (x, a, b'))))
            else zip (z, (Red (x, a, b'))) in
      let rec del =
        function
        | (Empty, z) -> raise (Error "not found\n")
        | (Red (((k', _) as y), a, b), z) ->
            (match compare (k, k') with
             | LESS -> del (a, (LeftRed (y, b, z)))
             | EQUAL -> joinRed (a, b, z)
             | GREATER -> del (b, (RightRed (a, y, z))))
        | (Black (((k', _) as y), a, b), z) ->
            (match compare (k, k') with
             | LESS -> del (a, (LeftBlack (y, b, z)))
             | EQUAL -> joinBlack (a, b, z)
             | GREATER -> del (b, (RightBlack (a, y, z)))) in
      Set ((nItems - 1), (del (t, Top)))
    let rec app f (Set (n, dict)) =
      let rec ap =
        function
        | Empty -> ()
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' (((_, datum) as entry1), left, right) =
        ap left; f datum; ap right in
      ap dict
    let rec update f (Set (n, dict)) =
      let rec upd =
        function
        | Empty -> Empty
        | Red tree -> Red (upd' tree)
        | Black tree -> Black (upd' tree)
      and upd' (((k, datum) as entry1), left, right) =
        let left' = upd left in
        let datum' = f datum in
        let right' = upd right in ((k, datum'), left', right') in
      Set (n, (upd dict))
    let rec forall (Set (n, dict)) f =
      let rec ap =
        function
        | Empty -> ()
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' (entry, left, right) = ap left; f entry; ap right in ap dict
    let rec existsOpt (Set (n, dict)) f =
      let rec ap =
        function
        | Empty -> None
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' (((k, d) as entry), left, right) =
        if f d
        then (print "SUCCESS\n"; Some k)
        else
          (print "FAILED\n";
           (match ap left with | None -> ap right | Some res -> Some res)) in
      ap dict
    let rec exists (Set (n, dict)) f =
      let rec ap =
        function
        | Empty -> false__
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' (entry, left, right) =
        if f entry then true__ else if ap left then true__ else ap right in
      ap dict
    let rec setsize (Set (n, _)) = n
    let rec next =
      function
      | (Red (_, _, b) as t)::rest -> (t, (left (b, rest)))
      | (Black (_, _, b) as t)::rest -> (t, (left (b, rest)))
      | _ -> (Empty, [])
    let rec left =
      function
      | (Empty, rest) -> rest
      | ((Red (_, a, _) as t), rest) -> left (a, (t :: rest))
      | ((Black (_, a, _) as t), rest) -> left (a, (t :: rest))
    let rec start m = left (m, [])
    type 'a digit =
      | ZERO 
      | ONE of ('a entry * 'a dict * 'a digit) 
      | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit) 
    let rec addItem (a, l) =
      let rec incr =
        function
        | (a, t, ZERO) -> ONE (a, t, ZERO)
        | (a1, t1, ONE (a2, t2, r)) -> TWO (a1, t1, a2, t2, r)
        | (a1, t1, TWO (a2, t2, a3, t3, r)) ->
            ONE (a1, t1, (incr (a2, (Black (a3, t3, t2)), r))) in
      incr (a, Empty, l)
    let rec linkAll t =
      let rec link =
        function
        | (t, ZERO) -> t
        | (t1, ONE (a, t2, r)) -> link ((Black (a, t2, t1)), r)
        | (t, TWO (a1, t1, a2, t2, r)) ->
            link ((Black (a1, (Red (a2, t2, t1)), t)), r) in
      link (Empty, t)
    let rec getEntry = function | Red (x, _, _) -> x | Black (x, _, _) -> x
    let rec union (Set (n1, s1), Set (n2, s2)) =
      let rec ins =
        function
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec union' (t1, t2, n, result) =
        match ((next t1), (next t2)) with
        | ((Empty, _), (Empty, _)) -> (n, result)
        | ((Empty, _), t2) -> ins (t2, n, result)
        | (t1, (Empty, _)) -> ins (t1, n, result)
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS -> union' (r1, t2, (n + 1), (addItem (e1, result)))
             | EQUAL -> union' (r1, r2, (n + 1), (addItem (e1, result)))
             | GREATER -> union' (t1, r2, (n + 1), (addItem (e2, result)))) in
      match s1 with
      | Empty -> Set (n2, s2)
      | _ ->
          (match s2 with
           | Empty -> Set (n1, s1)
           | _ ->
               let (n, result) = union' ((start s1), (start s2), 0, ZERO) in
               Set (n, (linkAll result)))
    let rec intersection (Set (_, s1), Set (_, s2)) =
      let rec intersect (t1, t2, n, result) =
        match ((next t1), (next t2)) with
        | ((Empty, r), (tree, r')) -> (n, result)
        | ((tree, r), (Empty, r')) -> (n, result)
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS -> intersect (r1, t2, n, result)
             | EQUAL -> intersect (r1, r2, (n + 1), (addItem (e1, result)))
             | GREATER -> intersect (t1, r2, n, result)) in
      let (n, result) = intersect ((start s1), (start s2), 0, ZERO) in
      Set (n, (linkAll result))
    let rec difference (Set (_, s1), Set (_, s2)) =
      let rec ins =
        function
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff (t1, t2, n, result) =
        match ((next t1), (next t2)) with
        | ((Empty, _), _) -> (n, result)
        | (t1, (Empty, _)) -> ins (t1, n, result)
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS -> diff (r1, t2, (n + 1), (addItem (e1, result)))
             | EQUAL -> diff (r1, r2, n, result)
             | GREATER -> diff (t1, r2, n, result)) in
      let (n, result) = diff ((start s1), (start s2), 0, ZERO) in
      Set (n, (linkAll result))
    let rec difference2 (Set (_, s1), Set (_, s2)) =
      let rec ins =
        function
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff (t1, t2, (n1, result1), (n2, result2)) =
        match ((next t1), (next t2)) with
        | ((Empty, _), t2) -> ((n1, result1), (ins (t2, n2, result2)))
        | (t1, (Empty, _)) -> ((ins (t1, n1, result1)), (n2, result2))
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS ->
                 diff
                   (r1, t2, ((n1 + 1), (addItem (e1, result1))),
                     (n2, result2))
             | EQUAL -> diff (r1, r2, (n1, result1), (n2, result2))
             | GREATER ->
                 diff
                   (t1, r2, (n1, result1),
                     ((n2 + 1), (addItem (e2, result2))))) in
      let ((n1, result1), (n2, result2)) =
        diff ((start s1), (start s2), (0, ZERO), (0, ZERO)) in
      ((Set (n1, (linkAll result1))), (Set (n2, (linkAll result2))))
    let rec diffMod (F) (Set (_, s1), Set (_, s2)) =
      let rec ins =
        function
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff (t1, t2, (n1, result1), (n2, result2)) =
        match ((next t1), (next t2)) with
        | ((Empty, _), t2) -> ((n1, result1), (ins (t2, n2, result2)))
        | (t1, (Empty, _)) -> ((ins (t1, n1, result1)), (n2, result2))
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS ->
                 diff
                   (r1, t2, ((n1 + 1), (addItem (e1, result1))),
                     (n2, result2))
             | EQUAL ->
                 (F d1 d2; diff (r1, r2, (n1, result1), (n2, result2)))
             | GREATER ->
                 diff
                   (t1, r2, (n1, result1),
                     ((n2 + 1), (addItem (e2, result2))))) in
      let ((n1, result1), (n2, result2)) =
        diff ((start s1), (start s2), (0, ZERO), (0, ZERO)) in
      ((Set (n1, (linkAll result1))), (Set (n2, (linkAll result2))))
    let rec splitSets (F) (Set (_, s1), Set (_, s2)) =
      let rec ins =
        function
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec split
        (t1, t2, ((n, result) as nr), ((n1, result1) as nr1),
         ((n2, result2) as nr2))
        =
        match ((next t1), (next t2)) with
        | ((Empty, _), t2) -> (nr, nr1, (ins (t2, n2, result2)))
        | (t1, (Empty, _)) -> (nr, (ins (t1, n1, result1)), nr2)
        | ((tree1, r1), (tree2, r2)) ->
            let (x, d1) as e1 = getEntry tree1 in
            let (y, d2) as e2 = getEntry tree2 in
            (match compare (x, y) with
             | LESS ->
                 split (r1, t2, nr, ((n1 + 1), (addItem (e1, result1))), nr2)
             | EQUAL ->
                 (match F d1 d2 with
                  | None ->
                      split
                        (r1, r2, nr, ((n1 + 1), (addItem (e1, result1))),
                          ((n2 + 1), (addItem (e2, result2))))
                  | Some d ->
                      split
                        (r1, r2, ((n + 1), (addItem ((x, d), result))), nr1,
                          nr2))
             | GREATER ->
                 split (t1, r2, nr, nr1, ((n2 + 1), (addItem (e2, result2))))) in
      let ((n, r), (n1, r1), (n2, r2)) =
        split ((start s1), (start s2), (0, ZERO), (0, ZERO), (0, ZERO)) in
      ((Set (n, (linkAll r))), (Set (n1, (linkAll r1))),
        (Set (n2, (linkAll r2))))
    (* val restore_right : 'a dict -> 'a dict *)
    (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
    (* re-color *)
    (* re-color *)
    (* l is black, deep rotate *)
    (* l is black, shallow rotate *)
    (* restore_left is like restore_right, except *)
    (* the color invariant may be violated only at the root of left child *)
    (* re-color *)
    (* re-color *)
    (* r is black, shallow rotate *)
    (* r is black, deep rotate *)
    (* val ins : 'a dict -> 'a dict  inserts entry *)
    (* ins (Red _) may violate color invariant at root *)
    (* ins (Black _) or ins (Empty) will be red/black tree *)
    (* ins preserves black height *)
    (*print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n");*)
    (* print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n"); *)
    (* re-color *)
    (* re-color *)
    (* input: set sc
     output set s' *)
    (* : 'a entry option ref *)
    (* re-color *)
    (* re-color *)
    (* Remove an item.  Raises LibBase.NotFound if not found. *)
    (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *)
    (* case 1L *)
    (* case 1L *)
    (* case 3L *)
    (* case 3L *)
    (* case 4L *)
    (* case 4L *)
    (* case 2L *)
    (* case 2L *)
    (* case 1R *)
    (* case 1R *)
    (* case 3R *)
    (* case 3R *)
    (* case 4R *)
    (* case 4R *)
    (* case 2R *)
    (* case 2R *)
    (* end case *)
    (* end case *)
    (* local *)
    (* does not apply f to all elements of S in order! *)
    (* support for constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)
    (* functions for walking the tree while keeping a stack of parents
   * to be visited.
   *)
    (* add an item that is guaranteed to be larger than any in l *)
    (* link the digits into a tree *)
    (* return the union of the two sets *)
    (* return the intersection of the two sets *)
    (* return the set difference  S1 - S2 
     if there are elements in S2 which do not appear in S1
     they are ignored !*)
    (* returns difference (d1, d2) where d1 
     contains all elements occurring in S1 but not in S2
     and d2 contains all elements occurring in S2 but not in S1
       *)
    (* S1 - S2 = R1 
      S2 - S1 = R2
      intersection (S1, S2) requires 
      for all (x, d1) in S1 
        and (x, d2) in S2, d1 ~ d2
    *)
    let rec new__ () = ref empty
    (* ignore size hint *)
    let rec copy (S) = let S' = new__ () in S' := (!S); S'
    let insert =
      function | set -> (function | entry -> (:=) set insert ((!set), entry))
    let insertLast =
      function
      | set -> (function | datum -> (:=) set insertLast ((!set), datum))
    let insertList =
      function
      | set -> (function | list -> (:=) set insertList ((!set), list))
    let insertShadow =
      function
      | set -> (function | entry -> (:=) set insertShadow ((!set), entry))
    let isEmpty = function | ordSet -> isEmpty (!ordSet)
    let last = function | ordSet -> last (!ordSet)
    let lookup =
      function | ordSet -> (function | key -> lookup (!ordSet) key)
    let clear = function | ordSet -> ordSet := empty
    let app = function | ordSet -> (function | f -> app f (!ordSet))
    let update =
      function
      | ordSet -> (function | f -> (ordSet := (update f (!ordSet)); ordSet))
    let forall = function | ordSet -> (function | f -> forall (!ordSet) f)
    let exists = function | ordSet -> (function | f -> exists (!ordSet) f)
    let existsOpt =
      function | ordSet -> (function | f -> existsOpt (!ordSet) f)
    let rec size (S) = setsize (!S)
    let difference =
      function
      | set1 ->
          (function
           | set2 ->
               let set = new__ () in
               ((:=) set difference ((!set1), (!set2)); set))
    let difference2 =
      function
      | set1 ->
          (function
           | set2 ->
               let r1 = new__ () in
               let r2 = new__ () in
               let (rset1, rset2) = difference2 ((!set1), (!set2)) in
               (r1 := rset1; r2 := rset2; (r1, r2)))
    let differenceModulo =
      function
      | set1 ->
          (function
           | set2 ->
               (function
                | F ->
                    let r1 = new__ () in
                    let r2 = new__ () in
                    let (rset1, rset2) = diffMod F ((!set1), (!set2)) in
                    (r1 := rset1; r2 := rset2; (r1, r2))))
    let splitSets =
      function
      | set1 ->
          (function
           | set2 ->
               (function
                | F ->
                    let r1 = new__ () in
                    let r2 = new__ () in
                    let r = new__ () in
                    let (rset, rset1, rset2) = splitSets F ((!set1), (!set2)) in
                    (r := rset; r1 := rset1; r2 := rset2; (r, r1, r2))))
    let intersection =
      function
      | set1 ->
          (function
           | set2 ->
               let set = new__ () in
               ((:=) set intersection ((!set1), (!set2)); set))
    let union =
      function
      | set1 ->
          (function
           | set2 ->
               let set = new__ () in ((:=) set union ((!set1), (!set2)); set))
  end ;;
