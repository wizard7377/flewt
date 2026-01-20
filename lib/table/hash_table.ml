
module HashTable(HashTable:sig
                             type nonrec key'
                             val hash : key' -> int
                             val eq : key' -> key' -> bool
                           end) : TABLE =
  struct
    type nonrec key = key'
    type nonrec 'a entry = (key * 'a)
    type 'a bucket =
      | Nil 
      | Cons of ('a ref * 'a bucket ref) 
    type nonrec 'a __Table = ((int * 'a entry) bucket array * int)
    let rec new__ n = ((Array.array (n, Nil)), n)
    let rec insertShadow a n ((key, datum) as e) =
      let hashVal = hash key in
      let index = hashVal mod__ n in
      let bucket = Array.sub (a, index) in
      let rec insertB (Cons
        (({ contents = (hash', ((key', datum') as e')) } as r'), br')) =
        if (hashVal = hash') && (eq (key, key'))
        then (r' := (hashVal, e); Some e')
        else insertBR br'
      and insertBR =
        function
        | { contents = Nil } as br ->
            ((:=) br Cons ((ref (hashVal, e)), (ref Nil)); NONE)
        | br -> insertB (!br) in
      let rec insertA =
        function
        | Nil ->
            (Array.update (a, index, (Cons ((ref (hashVal, e)), (ref Nil))));
             NONE)
        | bucket -> insertB bucket in
      insertA bucket
    let rec insert h e = insertShadow h e; ()
    let rec lookup a n key =
      let hashVal = hash key in
      let rec lookup' =
        function
        | Cons ({ contents = (hash1, (key1, datum1)) }, br) ->
            if (hashVal = hash1) && (eq (key, key1))
            then Some datum1
            else lookup' (!br)
        | Nil -> NONE in
      let bucket = Array.sub (a, (hashVal mod__ n)) in lookup' bucket
    let rec delete a n key =
      let hashVal = hash key in
      let index = hashVal mod__ n in
      let bucket = Array.sub (a, index) in
      let rec deleteBR =
        function
        | { contents = Cons ({ contents = (hash1, (key1, _)) }, br1) } as br
            ->
            if (hashVal = hash1) && (eq (key, key1))
            then (!) ((:=) br) br1
            else deleteBR br1
        | br -> () in
      let rec deleteA =
        function
        | Nil -> ()
        | Cons ({ contents = (hash1, (key1, _)) }, br1) ->
            if (hashVal = hash1) && (eq (key, key1))
            then Array.update (a, index, (!br1))
            else deleteBR br1 in
      deleteA bucket
    let rec clear a n = Array.modify (fun _ -> Nil) a
    let rec appBucket __0__ __1__ =
      match (__0__, __1__) with
      | (f, Nil) -> ()
      | (f, Cons ({ contents = (_, e) }, br)) -> (f e; appBucket f (!br))
    let rec app f a n = Array.app (appBucket f) a
  end ;;
