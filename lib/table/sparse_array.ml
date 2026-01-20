
module type SPARSE_ARRAY  =
  sig
    type nonrec 'a array
    val array : 'a -> 'a array
    val sub : 'a array -> int -> 'a
    val update : 'a array -> int -> 'a -> unit
    val extract : 'a array -> int -> int -> 'a Vector.vector
    val copyVec :
      <
        src: 'a Vector.vector  ;si: int  ;len: int option  ;dst: 'a array  ;
        di: int   >  -> unit
    val app : (int -> 'a -> unit) -> 'a array -> int -> int -> unit
    val foldl : (int -> 'a -> 'b -> 'b) -> 'b -> 'a array -> int -> int -> 'b
    val foldr : (int -> 'a -> 'b -> 'b) -> 'b -> 'a array -> int -> int -> 'b
    val modify : (int -> 'a -> 'a) -> 'a array -> int -> int -> unit
  end;;




module SparseArray(SparseArray:sig module IntTable : TABLE end) :
  SPARSE_ARRAY =
  struct
    type nonrec 'a array = < default: 'a  ;table: 'a IntTable.__Table   > 
    let size = 29
    let rec unsafeSub { table; default; default } i =
      match IntTable.lookup table i with | NONE -> default | Some v -> v
    let rec unsafeUpdate { table; default; default } i v =
      IntTable.insert table (i, v)
    let rec array default = { default; table = (IntTable.new__ size) }
    let rec sub array i =
      if i >= 0 then unsafeSub (array, i) else raise General.Subscript
    let rec update array i v =
      if i >= 0 then unsafeUpdate (array, i, v) else raise General.Subscript
    let rec extract array i len =
      if (i >= 0) && (len >= 0)
      then Vector.tabulate (len, (fun off -> unsafeSub (array, (i + off))))
      else raise General.Subscript
    let rec copyVec
      { src; si; len; dst; di; si; len; dst; di; len; dst; di; dst; di; di }
      =
      if di >= 0
      then
        VectorSlice.appi (fun i -> fun v -> unsafeUpdate (dst, i, v))
          (VectorSlice.slice (src, si, len))
      else raise General.Subscript
    let rec app f array i len =
      if (i >= 0) && (len >= 0)
      then
        let imax = i + len in
        let rec app' i' =
          if i' < imax
          then (f (i', (unsafeSub (array, i'))); app' (i' + 1))
          else () in
        app' i
      else raise General.Subscript
    let rec foldl f init array i len =
      if (i >= 0) && (len >= 0)
      then
        let rec foldl' i' =
          if i' >= i
          then f (i', (unsafeSub (array, i')), (foldl' (i' - 1)))
          else init in
        foldl' ((i + len) - 1)
      else raise General.Subscript
    let rec foldr f init array i len =
      if (i >= 0) && (len >= 0)
      then
        let imax = i + len in
        let rec foldr' i' =
          if i' < imax
          then f (i', (unsafeSub (array, i')), (foldr' (i' + 1)))
          else init in
        foldr' i
      else raise General.Subscript
    let rec modify f array i len =
      if (i >= 0) && (len >= 0)
      then
        let imax = i + len in
        let rec modify' i' =
          if i' < imax
          then
            (unsafeUpdate (array, i', (f (i', (unsafeSub (array, i')))));
             modify' (i' + 1))
          else () in
        modify' i
      else raise General.Subscript
  end ;;
