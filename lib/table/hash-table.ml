
module HashTable(HashTable:sig
                             type nonrec key'
                             val hash : key' -> int
                             val eq :
                               (key' * key') ->
                                 ((bool)(* Modified: Roberto Virga *)
                                 (* Author: Frank Pfenning *)(* Hash Table *))
                           end) : TABLE =
  struct
    type nonrec key = key'
    type nonrec 'a entry = (key * 'a)
    type 'a bucket =
      | Nil 
      | Cons of
      ((('a)(* A hashtable is an array of buckets containing entries paired with hash values *)
      (* A hashtable bucket is a linked list of mutable elements *))
      ref * 'a bucket ref) 
    type nonrec 'a __Table = ((int * 'a entry) bucket array * int)
    let rec new__ n = ((Array.array (n, Nil)), n)
    let rec insertShadow (a, n) ((key, datum) as e) =
      let hashVal = hash key in
      let index = hashVal mod__ n in
      let bucket = Array.sub (a, index) in
      let insertB (Cons ((ref (hash', ((key', datum') as e')) as r'), br')) =
        if (hashVal = hash') && (eq (key, key'))
        then (r' := (hashVal, e); SOME e')
        else insertBR br'
      and insertBR =
        function
        | ref (Nil) as br ->
            ((:=) br Cons ((ref (hashVal, e)), (ref Nil)); NONE)
        | br -> insertB (!br) in
      let insertA =
        function
        | Nil ->
            (Array.update (a, index, (Cons ((ref (hashVal, e)), (ref Nil))));
             NONE)
        | bucket -> insertB bucket in
      insertA bucket
    let rec insert h e = insertShadow h e; ()
    let rec lookup (a, n) key =
      let hashVal = hash key in
      let lookup' =
        function
        | Cons (ref (hash1, (key1, datum1)), br) ->
            if (hashVal = hash1) && (eq (key, key1))
            then SOME datum1
            else lookup' (!br)
        | Nil -> NONE in
      let bucket = Array.sub (a, (hashVal mod__ n)) in lookup' bucket
    let rec delete (a, n) key =
      let hashVal = hash key in
      let index = hashVal mod__ n in
      let bucket = Array.sub (a, index) in
      let deleteBR =
        function
        | ref (Cons (ref (hash1, (key1, _)), br1)) as br ->
            if (hashVal = hash1) && (eq (key, key1))
            then (!) ((:=) br) br1
            else deleteBR br1
        | br -> () in
      let deleteA =
        function
        | Nil -> ()
        | Cons (ref (hash1, (key1, _)), br1) ->
            if (hashVal = hash1) && (eq (key, key1))
            then Array.update (a, index, (!br1))
            else deleteBR br1 in
      deleteA bucket
    let rec clear (a, n) = Array.modify (function | _ -> Nil) a
    let rec appBucket arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, Nil) -> ()
      | (f, Cons (ref (_, e), br)) -> (f e; appBucket f (!br))
    let rec app f (a, n) = Array.app (appBucket f) a
  end ;;
