
module type TABLE  =
  sig
    type nonrec key
    type nonrec 'a entry = (key * 'a)
    type nonrec 'a __Table
    val new__ : int -> 'a __Table
    val insert : 'a __Table -> 'a entry -> unit
    val insertShadow : 'a __Table -> 'a entry -> 'a entry option
    val lookup : 'a __Table -> key -> 'a option
    val delete : 'a __Table -> key -> unit
    val clear : 'a __Table -> unit
    val app : ('a entry -> unit) -> 'a __Table -> unit
  end;;




module StringHashTable =
  (Make_HashTable)(struct
                     type nonrec key' = string
                     let hash = StringHash.stringHash
                     let eq = (=)
                   end)
module IntHashTable =
  (Make_HashTable)(struct
                     type nonrec key' = int
                     let hash n = n
                     let eq = (=)
                   end)
module StringRedBlackTree =
  (Make_RedBlackTree)(struct
                        type nonrec key' = string
                        let compare = String.compare
                      end)
module IntRedBlackTree =
  (Make_RedBlackTree)(struct
                        type nonrec key' = int
                        let compare = Int.compare
                      end)
module SparseArray =
  (Make_SparseArray)(struct module IntTable = IntHashTable end)
module SparseArray2 =
  (Make_SparseArray2)(struct module IntTable = IntHashTable end);;
