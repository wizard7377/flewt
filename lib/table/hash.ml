module HashTable(HashTable:sig
                             type nonrec key'
                             val hash : key' -> int
                             val eq : (key' * key') -> bool
                           end) : TABLE =
  struct
    type nonrec key = key'
    type nonrec 'a entry = (key * 'a)
    type 'a bucket =
      | Nil 
      | Cons of ('a ref * 'a bucket ref) 
    type nonrec 'a table_ = ((int * 'a entry) bucket array * int)
    let rec new_ n = ((Array.array (n, Nil)), n)
    let rec insertShadow (a, n) ((key, datum) as e) =
      let hashVal = hash key in
      let index = hashVal mod_ n in
      let bucket = Array.sub (a, index) in
      let rec insertB (Cons
        (({ contents = (hash', ((key', datum') as e')) } as r'), br')) =
        if (hashVal = hash') && (eq (key, key'))
        then begin (begin r' := (hashVal, e); Some e' end) end
      else begin insertBR br' end
        and insertBR =
          begin function
          | { contents = Nil } as br ->
              (begin (:=) br Cons ((ref (hashVal, e)), (ref Nil)); None end)
          | br -> insertB !br end in
    let rec insertA =
      begin function
      | Nil ->
          (begin Array.update
                   (a, index, (Cons ((ref (hashVal, e)), (ref Nil))));
           None end)
      | bucket -> insertB bucket end in
  insertA bucket
let rec insert h e = begin insertShadow h e; () end
let rec lookup (a, n) key =
  let hashVal = hash key in
  let rec lookup' =
    begin function
    | Cons ({ contents = (hash1, (key1, datum1)) }, br) ->
        if (hashVal = hash1) && (eq (key, key1)) then begin Some datum1 end
        else begin lookup' !br end
    | Nil -> None end in
let bucket = Array.sub (a, (hashVal mod_ n)) in lookup' bucket
let rec clear (a, n) = Array.modify (begin function | _ -> Nil end) a
let rec appBucket arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, Nil) -> ()
  | (f, Cons ({ contents = (_, e) }, br)) -> (begin f e; appBucket f !br end) end
let rec app f (a, n) = Array.app (appBucket f) a end 
module type STRING_HASH  = sig val stringHash : string -> int end
module StringHash : STRING_HASH =
  struct
    let rec stringHash s =
      let rec num i = Char.ord (String.sub (s, i)) mod_ 128 in
      let n = String.size s in if n = 0 then begin 0 end
        else begin
          (let a = n - 1 in
           let b = n div 2 in
           let c = b div 2 in
           let d = b + c in
           ((num a) + 128) *
             (((num b) + 128) * (( * ) ((num c) + 128) num d))) end(* sample 4 characters from string *)
end 
module StringHashTable : TABLE =
  (HashTable)(struct
                     type nonrec key' = string
                     let hash = StringHash.stringHash
                     let eq = (=)
                   end) 