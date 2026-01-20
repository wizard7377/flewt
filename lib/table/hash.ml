
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
            ((:=) br Cons ((ref (hashVal, e)), (ref Nil)); None)
        | br -> insertB (!br) in
      let rec insertA =
        function
        | Nil ->
            (Array.update (a, index, (Cons ((ref (hashVal, e)), (ref Nil))));
             None)
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
        | Nil -> None in
      let bucket = Array.sub (a, (hashVal mod__ n)) in lookup' bucket
    let rec clear a n = Array.modify (fun _ -> Nil) a
    let rec appBucket __0__ __1__ =
      match (__0__, __1__) with
      | (f, Nil) -> ()
      | (f, Cons ({ contents = (_, e) }, br)) -> (f e; appBucket f (!br))
    let rec app f a n = Array.app (appBucket f) a
  end  module type STRING_HASH  = sig val stringHash : string -> int end
module StringHash : STRING_HASH =
  struct
    let rec stringHash s =
      let rec num i = Char.ord (String.sub (s, i)) mod__ 128 in
      let n = String.size s in
      if n = 0
      then 0
      else
        (let a = n - 1 in
         let b = n div 2 in
         let c = b div 2 in
         let d = b + c in
         ((num a) + 128) * (((num b) + 128) * (( * ) ((num c) + 128) num d)))
      (* sample 4 characters from string *)
  end 
module StringHashTable : TABLE =
  (Make_HashTable)(struct
                     type nonrec key' = string
                     let hash = StringHash.stringHash
                     let eq = (=)
                   end) ;;
