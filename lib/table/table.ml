open Table_sig
open Hash_table

module StringHashTable =
  (HashTable)(struct
                     type nonrec key' = string
                     let hash = String_hash.StringHash.stringHash
                     let eq (x,y) = (x = y)
                   end)
module IntHashTable : (TABLE with type key = int) =
  (HashTable)(struct
                     type nonrec key' = int
                     let hash = begin function | n -> n end
                     let eq (x,y) = (x = y) end)
module StringRedBlackTree =
  (Red_black_tree.RedBlackTree)(struct
                                  type nonrec key' = string
                                  let compare (x,y) = Basis.General.int_to_order (String.compare x y)
                                end)
module IntRedBlackTree =
  (Red_black_tree.RedBlackTree)(struct
                                  type nonrec key' = int
                                  let compare (x,y) = Basis.General.int_to_order (Int.compare x y)
                                end)
module SparseArray =
  (Sparse_array.SparseArray)(struct module IntTable = IntHashTable end)
module SparseArray2 =
  (Sparse_array2.SparseArray2)(struct module IntTable = IntHashTable end) 