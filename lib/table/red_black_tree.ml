
module RedBlackTree(RedBlackTree:sig
                                   type nonrec key'
                                   val compare : key' -> key' -> order
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
    let rec insert dict ((key, datum) as entry) =
      let rec ins =
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
      ((match ins dict with
        | Red ((_, Red _, _) as t) -> Black t
        | Red ((_, _, Red _) as t) -> Black t
        | dict -> dict)
        (* re-color *)(* re-color *)
        (* val ins : 'a dict -> 'a dict  inserts entry *)
        (* ins (Red _) may violate color invariant at root *)(* ins (Black _) or ins (Empty) will be red/black tree *)
        (* ins preserves black height *))
    exception NotFound 
    type 'a zipper =
      | TOP 
      | LEFTB of ('a entry * 'a dict * 'a zipper) 
      | LEFTR of ('a entry * 'a dict * 'a zipper) 
      | RIGHTB of ('a dict * 'a entry * 'a zipper) 
      | RIGHTR of ('a dict * 'a entry * 'a zipper) 
    let rec delete t key =
      let rec zip __0__ __1__ =
        match (__0__, __1__) with
        | (TOP, t) -> t
        | (LEFTB (x, b, z), a) -> zip (z, (Black (x, a, b)))
        | (LEFTR (x, b, z), a) -> zip (z, (Red (x, a, b)))
        | (RIGHTB (a, x, z), b) -> zip (z, (Black (x, a, b)))
        | (RIGHTR (a, x, z), b) -> zip (z, (Red (x, a, b))) in
      let rec bbZip __2__ __3__ =
        match (__2__, __3__) with
        | (TOP, t) -> (true, t)
        | (LEFTB (x, Red (y, c, d), z), a) ->
            bbZip ((LEFTR (x, c, (LEFTB (y, d, z)))), a)
        | (LEFTB (x, Black (w, Red (y, c, d), e), z), a) ->
            bbZip ((LEFTB (x, (Black (y, c, (Red (w, d, e)))), z)), a)
        | (LEFTR (x, Black (w, Red (y, c, d), e), z), a) ->
            bbZip ((LEFTR (x, (Black (y, c, (Red (w, d, e)))), z)), a)
        | (LEFTB (x, Black (y, c, Red (w, d, e)), z), a) ->
            (false,
              (zip (z, (Black (y, (Black (x, a, c)), (Black (w, d, e)))))))
        | (LEFTR (x, Black (y, c, Red (w, d, e)), z), a) ->
            (false,
              (zip (z, (Red (y, (Black (x, a, c)), (Black (w, d, e)))))))
        | (LEFTR (x, Black (y, c, d), z), a) ->
            (false, (zip (z, (Black (x, a, (Red (y, c, d)))))))
        | (LEFTB (x, Black (y, c, d), z), a) ->
            bbZip (z, (Black (x, a, (Red (y, c, d)))))
        | (RIGHTB (Red (y, c, d), x, z), b) ->
            bbZip ((RIGHTR (d, x, (RIGHTB (c, y, z)))), b)
        | (RIGHTR (Red (y, c, d), x, z), b) ->
            bbZip ((RIGHTR (d, x, (RIGHTB (c, y, z)))), b)
        | (RIGHTB (Black (y, Red (w, c, d), e), x, z), b) ->
            bbZip ((RIGHTB ((Black (w, c, (Red (y, d, e)))), x, z)), b)
        | (RIGHTR (Black (y, Red (w, c, d), e), x, z), b) ->
            bbZip ((RIGHTR ((Black (w, c, (Red (y, d, e)))), x, z)), b)
        | (RIGHTB (Black (y, c, Red (w, d, e)), x, z), b) ->
            (false,
              (zip (z, (Black (y, c, (Black (x, (Red (w, d, e)), b)))))))
        | (RIGHTR (Black (y, c, Red (w, d, e)), x, z), b) ->
            (false,
              (zip (z, (Red (y, c, (Black (w, (Red (w, d, e)), b)))))))
        | (RIGHTR (Black (y, c, d), x, z), b) ->
            (false, (zip (z, (Black (x, (Red (y, c, d)), b)))))
        | (RIGHTB (Black (y, c, d), x, z), b) ->
            bbZip (z, (Black (x, (Red (y, c, d)), b)))
        | (z, t) -> (false, (zip (z, t)))(* case 2R *)
        (* case 2R *)(* case 4R *)
        (* case 4R *)(* case 3R *)
        (* case 3R *)(* case 1R *)
        (* case 1R *)(* case 2L *)
        (* case 2L *)(* case 4L *)
        (* case 4L *)(* case 3L *)
        (* case 3L *)(* case 1L *) in
      let rec delMin __4__ __5__ =
        match (__4__, __5__) with
        | (Red (y, Empty, b), z) -> (y, (false, (zip (z, b))))
        | (Black (y, Empty, b), z) -> (y, (bbZip (z, b)))
        | (Black (y, a, b), z) -> delMin (a, (LEFTB (y, b, z)))
        | (Red (y, a, b), z) -> delMin (a, (LEFTR (y, b, z)))
        | (Empty, _) -> raise Match in
      let rec joinRed __6__ __7__ __8__ =
        match (__6__, __7__, __8__) with
        | (Empty, Empty, z) -> zip (z, Empty)
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, TOP) in
            if needB
            then ((fun r -> r.2)) (bbZip (z, (Red (x, a, b'))))
            else zip (z, (Red (x, a, b'))) in
      let rec joinBlack __9__ __10__ __11__ =
        match (__9__, __10__, __11__) with
        | (a, Empty, z) -> ((fun r -> r.2)) (bbZip (z, a))
        | (Empty, b, z) -> ((fun r -> r.2)) (bbZip (z, b))
        | (a, b, z) ->
            let (x, (needB, b')) = delMin (b, TOP) in
            if needB
            then ((fun r -> r.2)) (bbZip (z, (Black (x, a, b'))))
            else zip (z, (Black (x, a, b'))) in
      let rec del __12__ __13__ =
        match (__12__, __13__) with
        | (Empty, z) -> raise NotFound
        | (Black (((key1, datum1) as entry1), a, b), z) ->
            (match compare (key, key1) with
             | EQUAL -> joinBlack (a, b, z)
             | LESS -> del (a, (LEFTB (entry1, b, z)))
             | GREATER -> del (b, (RIGHTB (a, entry1, z))))
        | (Red (((key1, datum1) as entry1), a, b), z) ->
            (match compare (key, key1) with
             | EQUAL -> joinRed (a, b, z)
             | LESS -> del (a, (LEFTR (entry1, b, z)))
             | GREATER -> del (b, (RIGHTR (a, entry1, z)))) in
      ((try del (t, TOP); true with | NotFound -> false)
        (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *))
    let rec insertShadow dict ((key, datum) as entry) =
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
      ((oldEntry := None;
        ((((match ins dict with
            | Red ((_, Red _, _) as t) -> Black t
            | Red ((_, _, Red _) as t) -> Black t
            | dict -> dict))
          (* re-color *)(* re-color *)),
          (!oldEntry)))
        (* : 'a entry option ref *))
    let rec app f dict =
      let rec ap =
        function
        | Empty -> ()
        | Red tree -> ap' tree
        | Black tree -> ap' tree
      and ap' entry1 left right = ap left; f entry1; ap right in ap dict
    let rec new__ n = ref Empty
    let insert table entry = (:=) table insert ((!table), entry)
    let insertShadow table entry =
      let (dict, oldEntry) = insertShadow ((!table), entry) in
      table := dict; oldEntry
    let lookup table key = lookup (!table) key
    let delete table key = delete (!table) key; ()
    let clear table = table := Empty
    let app f table = app f (!table)
  end ;;
