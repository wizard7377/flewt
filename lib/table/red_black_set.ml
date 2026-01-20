
module type RBSET  =
  sig
    type nonrec key = int
    type nonrec 'a entry = (key * 'a)
    exception Error of string 
    type nonrec 'a ordSet
    val new__ : unit -> 'a ordSet
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
  end;;




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
      function | Set (_, Empty) -> true | Set (_, __T) -> false
    let empty = Set (0, Empty)
    let rec singleton x = Set (1, (Red (x, Empty, Empty)))
    let compare = Int.compare
    let rec lookup (Set (n, dict)) key =
      let rec lk =
        function
        | Empty -> None
        | Red tree -> lk' tree
        | Black tree -> lk' tree
      and lk' (key1, datum1) left right =
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
      | dict -> dict(* l is black, shallow rotate *)
      (* l is black, deep rotate *)(* re-color *)
      (* re-color *)
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
      | dict -> dict(* r is black, deep rotate *)(* r is black, shallow rotate *)
      (* re-color *)(* re-color *)
    let rec insert (Set (n, dict)) ((key, datum) as entry) =
      let nItems = ref n in
      let rec ins =
        function
        | Empty -> ((nItems := n) + 1; Red (entry, Empty, Empty))
        | Red (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> ((Red (entry1, left, right))
                 (*print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n");*))
             | LESS -> Red (entry1, (ins left), right)
             | GREATER -> Red (entry1, left, (ins right)))
        | Black (((key1, datum1) as entry1), left, right) ->
            (match compare (key, key1) with
             | EQUAL -> ((Black (entry1, left, right))
                 (* print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n"); *))
             | LESS -> restore_left (Black (entry1, (ins left), right))
             | GREATER -> restore_right (Black (entry1, left, (ins right)))) in
      let dict' =
        ((match ins dict with
          | Red ((_, Red _, _) as t) -> Black t
          | Red ((_, _, Red _) as t) -> Black t
          | dict -> dict)
        (* re-color *)(* re-color *)) in
      ((Set ((!nItems), dict'))
        (* val ins : 'a dict -> 'a dict  inserts entry *)
        (* ins (Red _) may violate color invariant at root *)(* ins (Black _) or ins (Empty) will be red/black tree *)
        (* ins preserves black height *))
    let rec insertList __0__ __1__ =
      match (__0__, __1__) with
      | (__S, nil) -> __S
      | (__S, e::list) -> insertList ((insert (__S, e)), list)
    let rec insertLast (Set (n, dict)) datum =
      let Set (n', dic') = insert ((Set (n, dict)), ((n + 1), datum)) in
      Set (n', dic')
    let rec insertShadow (Set (n, dict)) ((key, datum) as entry) =
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
        ((((match ins dict with
            | Red ((_, Red _, _) as t) -> Black t
            | Red ((_, _, Red _) as t) -> Black t
            | dict -> dict))
          (* re-color *)(* re-color *)),
          (!oldEntry)) in
      ((Set (n, dict'))(* : 'a entry option ref *))
    type color =
      | RedColor 
      | BlackColor 
    type 'a zipper =
      | Top 
      | LeftRed of ('a entry * 'a dict * 'a zipper) 
      | LeftBlack of ('a entry * 'a dict * 'a zipper) 
      | RightRed of ('a dict * 'a entry * 'a zipper) 
      | RightBlack of ('a dict * 'a entry * 'a zipper) 
    let rec delete (Set (nItems, t)) k =
      let rec zip __2__ __3__ =
        match (__2__, __3__) with
        | (Top, t) -> t
        | (LeftRed (x, b, z), a) -> zip (z, (Red (x, a, b)))
        | (LeftBlack (x, b, z), a) -> zip (z, (Black (x, a, b)))
        | (RightRed (a, x, z), b) -> zip (z, (Red (x, a, b)))
        | (RightBlack (a, x, z), b) -> zip (z, (Black (x, a, b))) in
      let rec bbZip __4__ __5__ =
        match (__4__, __5__) with
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
            (false,
              (zip (z, (Black (y, (Black (x, a, c)), (Black (w, d, e)))))))
        | (LeftRed (x, Black (y, c, Red (w, d, e)), z), a) ->
            (false,
              (zip (z, (Red (y, (Black (x, a, c)), (Black (w, d, e)))))))
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
            (false,
              (zip (z, (Black (y, c, (Black (x, (Red (w, d, e)), b)))))))
        | (RightRed (Black (y, c, Red (w, d, e)), x, z), b) ->
            (false,
              (zip (z, (Red (y, c, (Black (x, (Red (w, d, e)), b)))))))
        | (RightRed (Black (y, c, d), x, z), b) ->
            (false, (zip (z, (Black (x, (Red (y, c, d)), b)))))
        | (RightBlack (Black (y, c, d), x, z), b) ->
            bbZip (z, (Black (x, (Red (y, c, d)), b)))
        | (z, t) -> (false, (zip (z, t)))(* case 2R *)
        (* case 2R *)(* case 4R *)
        (* case 4R *)(* case 3R *)
        (* case 3R *)(* case 1R *)
        (* case 1R *)(* case 2L *)
        (* case 2L *)(* case 4L *)
        (* case 4L *)(* case 3L *)
        (* case 3L *)(* case 1L *)
        (* case 1L *) in
      let rec delMin __6__ __7__ =
        match (__6__, __7__) with
        | (Red (y, Empty, b), z) -> (y, (false, (zip (z, b))))
        | (Black (y, Empty, b), z) -> (y, (bbZip (z, b)))
        | (Red (y, a, b), z) -> delMin (a, (LeftRed (y, b, z)))
        | (Black (y, a, b), z) -> delMin (a, (LeftBlack (y, b, z))) in
      let rec joinBlack __8__ __9__ __10__ =
        match (__8__, __9__, __10__) with
        | (a, Empty, z) -> ((fun r -> r.2)) (bbZip (z, a))
        | (Empty, b, z) -> ((fun r -> r.2)) (bbZip (z, b))
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, Top) in
            if needB
            then ((fun r -> r.2)) (bbZip (z, (Black (x, a, b'))))
            else zip (z, (Black (x, a, b'))) in
      let rec joinRed __11__ __12__ __13__ =
        match (__11__, __12__, __13__) with
        | (Empty, Empty, z) -> zip (z, Empty)
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, Top) in
            if needB
            then ((fun r -> r.2)) (bbZip (z, (Red (x, a, b'))))
            else zip (z, (Red (x, a, b'))) in
      let rec del __14__ __15__ =
        match (__14__, __15__) with
        | (Empty, z) -> raise (Error "not found\n")
        | (Red (((k', _) as y), a, b), z) ->
            (((match compare (k, k') with
               | LESS -> del (a, (LeftRed (y, b, z)))
               | EQUAL -> joinRed (a, b, z)
               | GREATER -> del (b, (RightRed (a, y, z)))))
            (* end case *))
        | (Black (((k', _) as y), a, b), z) ->
            (((match compare (k, k') with
               | LESS -> del (a, (LeftBlack (y, b, z)))
               | EQUAL -> joinBlack (a, b, z)
               | GREATER -> del (b, (RightBlack (a, y, z)))))
            (* end case *)) in
      ((Set ((nItems - 1), (del (t, Top))))
        (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *))
    let rec app f (Set (n, dict)) =
      let rec ap =
        function
        | Empty -> ()
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' ((_, datum) as entry1) left right = ap left; f datum; ap right in
      ap dict
    let rec update f (Set (n, dict)) =
      let rec upd =
        function
        | Empty -> Empty
        | Red tree -> Red (upd' tree)
        | Black tree -> Black (upd' tree)
      and upd' ((k, datum) as entry1) left right =
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
      and ap' entry left right = ap left; f entry; ap right in ap dict
    let rec existsOpt (Set (n, dict)) f =
      let rec ap =
        function
        | Empty -> None
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' ((k, d) as entry) left right =
        if f d
        then (print "SUCCESS\n"; Some k)
        else
          (print "FAILED\n";
           (match ap left with | None -> ap right | Some res -> Some res)) in
      ap dict
    let rec exists (Set (n, dict)) f =
      let rec ap =
        function
        | Empty -> false
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' entry left right =
        if f entry then true else if ap left then true else ap right in
      ap dict
    let rec setsize (Set (n, _)) = n
    let rec next =
      function
      | (Red (_, _, b) as t)::rest -> (t, (left (b, rest)))
      | (Black (_, _, b) as t)::rest -> (t, (left (b, rest)))
      | _ -> (Empty, [])
    let rec left __16__ __17__ =
      match (__16__, __17__) with
      | (Empty, rest) -> rest
      | ((Red (_, a, _) as t), rest) -> left (a, (t :: rest))
      | ((Black (_, a, _) as t), rest) -> left (a, (t :: rest))
    let rec start m = left (m, [])
    type 'a digit =
      | ZERO 
      | ONE of ('a entry * 'a dict * 'a digit) 
      | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit) 
    let rec addItem a l =
      let rec incr __18__ __19__ __20__ =
        match (__18__, __19__, __20__) with
        | (a, t, ZERO) -> ONE (a, t, ZERO)
        | (a1, t1, ONE (a2, t2, r)) -> TWO (a1, t1, a2, t2, r)
        | (a1, t1, TWO (a2, t2, a3, t3, r)) ->
            ONE (a1, t1, (incr (a2, (Black (a3, t3, t2)), r))) in
      incr (a, Empty, l)
    let rec linkAll t =
      let rec link __21__ __22__ =
        match (__21__, __22__) with
        | (t, ZERO) -> t
        | (t1, ONE (a, t2, r)) -> link ((Black (a, t2, t1)), r)
        | (t, TWO (a1, t1, a2, t2, r)) ->
            link ((Black (a1, (Red (a2, t2, t1)), t)), r) in
      link (Empty, t)
    let rec getEntry = function | Red (x, _, _) -> x | Black (x, _, _) -> x
    let rec union (Set (n1, s1)) (Set (n2, s2)) =
      let rec ins __23__ __24__ __25__ =
        match (__23__, __24__, __25__) with
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec union' t1 t2 n result =
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
    let rec intersection (Set (_, s1)) (Set (_, s2)) =
      let rec intersect t1 t2 n result =
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
    let rec difference (Set (_, s1)) (Set (_, s2)) =
      let rec ins __26__ __27__ __28__ =
        match (__26__, __27__, __28__) with
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff t1 t2 n result =
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
    let rec difference2 (Set (_, s1)) (Set (_, s2)) =
      let rec ins __29__ __30__ __31__ =
        match (__29__, __30__, __31__) with
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff t1 t2 (n1, result1) (n2, result2) =
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
    let rec diffMod (__F) (Set (_, s1)) (Set (_, s2)) =
      let rec ins __32__ __33__ __34__ =
        match (__32__, __33__, __34__) with
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec diff t1 t2 (n1, result1) (n2, result2) =
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
                 (__F d1 d2; diff (r1, r2, (n1, result1), (n2, result2)))
             | GREATER ->
                 diff
                   (t1, r2, (n1, result1),
                     ((n2 + 1), (addItem (e2, result2))))) in
      let ((n1, result1), (n2, result2)) =
        diff ((start s1), (start s2), (0, ZERO), (0, ZERO)) in
      ((Set (n1, (linkAll result1))), (Set (n2, (linkAll result2))))
    let rec splitSets (__F) (Set (_, s1)) (Set (_, s2)) =
      let rec ins __35__ __36__ __37__ =
        match (__35__, __36__, __37__) with
        | ((Empty, _), n, result) -> (n, result)
        | ((Red (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result)))
        | ((Black (x, _, _), r), n, result) ->
            ins ((next r), (n + 1), (addItem (x, result))) in
      let rec split t1 t2 ((n, result) as nr) ((n1, result1) as nr1)
        ((n2, result2) as nr2) =
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
                 (match __F d1 d2 with
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
    let rec new__ () = ref empty
    let rec copy (__S) = let __S' = new__ () in __S' := (!__S); __S'
    let insert set entry = (:=) set insert ((!set), entry)
    let insertLast set datum = (:=) set insertLast ((!set), datum)
    let insertList set list = (:=) set insertList ((!set), list)
    let insertShadow set entry = (:=) set insertShadow ((!set), entry)
    let isEmpty ordSet = isEmpty (!ordSet)
    let last ordSet = last (!ordSet)
    let lookup ordSet key = lookup (!ordSet) key
    let clear ordSet = ordSet := empty
    let app ordSet f = app f (!ordSet)
    let update ordSet f = ordSet := (update f (!ordSet)); ordSet
    let forall ordSet f = forall (!ordSet) f
    let exists ordSet f = exists (!ordSet) f
    let existsOpt ordSet f = existsOpt (!ordSet) f
    let rec size (__S) = setsize (!__S)
    let difference set1 set2 =
      let set = new__ () in (:=) set difference ((!set1), (!set2)); set
    let difference2 set1 set2 =
      let r1 = new__ () in
      let r2 = new__ () in
      let (rset1, rset2) = difference2 ((!set1), (!set2)) in
      r1 := rset1; r2 := rset2; (r1, r2)
    let differenceModulo set1 set2 (__F) =
      let r1 = new__ () in
      let r2 = new__ () in
      let (rset1, rset2) = diffMod __F ((!set1), (!set2)) in
      r1 := rset1; r2 := rset2; (r1, r2)
    let splitSets set1 set2 (__F) =
      let r1 = new__ () in
      let r2 = new__ () in
      let r = new__ () in
      let (rset, rset1, rset2) = splitSets __F ((!set1), (!set2)) in
      r := rset; r1 := rset1; r2 := rset2; (r, r1, r2)
    let intersection set1 set2 =
      let set = new__ () in (:=) set intersection ((!set1), (!set2)); set
    let union set1 set2 =
      let set = new__ () in (:=) set union ((!set1), (!set2)); set
  end ;;
