open Table_sig
module HashTable(HashTable:sig
                             type nonrec key'
                             val hash : key' -> int
                             val eq : (key' * key') -> bool
                           end) : (TABLE with type key = HashTable.key') =
  struct
    type nonrec key = HashTable.key'
    type nonrec 'a entry = (key * 'a)
    type 'a bucket =
      | Nil 
      | Cons of ('a ref * 'a bucket ref) 
    type nonrec 'a table_ = ((int * 'a entry) bucket array * int)
    let rec new_ n = ((Array.make n Nil), n)
    let rec insertShadow (a, n) ((key, datum) as e) =
      let hashVal = HashTable.hash key in
      let index = hashVal mod n in
      let bucket = a.(index) in
      let rec insertB (Cons
        (({ contents = (hash', ((key', datum') as e')) } as r'), br')) =
        if (hashVal = hash') && (HashTable.eq (key, key'))
        then begin (begin r' := (hashVal, e); Some e' end) end
      else begin insertBR br' end
        and insertBR =
          begin function
          | { contents = Nil } as br ->
              (begin br := Cons ((ref (hashVal, e)), (ref Nil)); None end)
          | br -> insertB !br end in
    let rec insertA =
      begin function
      | Nil ->
          (begin Array.set  
                   a index (Cons ((ref (hashVal, e)), (ref Nil)));
           None end)
      | bucket -> insertB bucket end in
  insertA bucket
let rec insert h e = begin ignore @@ insertShadow h e; () end
let rec lookup (a, n) key =
  let hashVal = HashTable.hash key in
  let rec lookup' =
    begin function
    | Cons ({ contents = (hash1, (key1, datum1)) }, br) ->
        if (hashVal = hash1) && (HashTable.eq (key, key1)) then begin Some datum1 end
        else begin lookup' !br end
    | Nil -> None end in
let bucket = a.(hashVal mod n) in lookup' bucket
let rec delete (a, n) key =
  let hashVal = HashTable.hash key in
  let index = hashVal mod n in
  let bucket = a.(index) in
  let rec deleteBR =
    begin function
    | { contents = Cons ({ contents = (hash1, (key1, _)) }, br1) } as br ->
        if (hashVal = hash1) && (HashTable.eq (key, key1))
        then begin br := !br1 end else begin deleteBR br1 end
    | br -> () end in
  let rec deleteA =
    begin function
    | Nil -> ()
    | Cons ({ contents = (hash1, (key1, _)) }, br1) ->
        if (hashVal = hash1) && (HashTable.eq (key, key1))
        then begin Array.set a index !br1 end
        else begin deleteBR br1 end end in
deleteA bucket
let rec clear (a, n) = Array.iter (begin function | _ -> () end) a
let rec appBucket arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, Nil) -> ()
  | (f, Cons ({ contents = (_, e) }, br)) -> (begin f e; appBucket f !br end) end
let rec app f (a, n) = Array.iter (appBucket f) a end
