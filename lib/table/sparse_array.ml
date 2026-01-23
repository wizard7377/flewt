open Table_sig
open Basis
module type SPARSE_ARRAY  =
  sig
    type nonrec 'a array
    val array : 'a -> 'a array
    val sub : ('a array * int) -> 'a
    val update : ('a array * int * 'a) -> unit
    val extract : ('a array * int * int) -> 'a Array.t
    val copyVec :
      <
        src: 'a Array.t  ;si: int  ;len: int option  ;dst: 'a array  ;
        di: int   >  -> unit
    val app : ((int * 'a) -> unit) -> ('a array * int * int) -> unit
    val foldl : ((int * 'a * 'b) -> 'b) -> 'b -> ('a array * int * int) -> 'b
    val foldr : ((int * 'a * 'b) -> 'b) -> 'b -> ('a array * int * int) -> 'b
    val modify : ((int * 'a) -> 'a) -> ('a array * int * int) -> unit
  end


module SparseArray(SparseArray:sig module IntTable : TABLE with type key = int end) :
  SPARSE_ARRAY =
  struct
    type nonrec 'a array = { default: 'a  ;table: 'a SparseArray.IntTable.table_   } 
    let size = 29
    let rec unsafeSub ({ table; default }, i) =
      begin match SparseArray.IntTable.lookup table i with
      | None -> default
      | Some v -> v end
    let rec unsafeUpdate ({ table; default }, i, v) =
      SparseArray.IntTable.insert table (i, v)
    let rec array default = { default; table = (SparseArray.IntTable.new_ size) }
    let rec sub (array, i) = if i >= 0 then begin unsafeSub (array, i) end
      else begin raise Basis.General.Subscript end
let rec update (array, i, v) =
  if i >= 0 then begin unsafeUpdate (array, i, v) end
  else begin raise General.Subscript end
  
let rec extract (array, i, len) =
  if (i >= 0) && (len >= 0)
  then
    begin Array.init len
            (begin function | off -> unsafeSub (array, (i + off)) end) end
  else begin raise Basis.General.Subscript end
let rec copyVec arg =
  let len = match arg#len with | None -> Array.length arg#src - arg#si | Some l -> l in
  if arg#di >= 0 && arg#si >= 0 && len >= 0 &&
     arg#si + len <= Array.length arg#src
  then
    begin for i = 0 to len - 1 do
            unsafeUpdate (arg#dst, arg#di + i, arg#src.(arg#si + i))
          done
    end
  else begin raise Basis.General.Subscript end
let rec app f (array, i, len) =
  if (i >= 0) && (len >= 0)
  then
    begin let imax = i + len in
          let rec app' i' =
            if i' < imax
            then
              begin (begin f (i', (unsafeSub (array, i'))); app' (i' + 1) end) end
            else begin () end in
app' i end
else begin raise General.Subscript end
let rec foldl f init (array, i, len) =
  if (i >= 0) && (len >= 0)
  then
    begin let rec foldl' i' =
            if i' >= i
            then begin f (i', (unsafeSub (array, i')), (foldl' (i' - 1))) end
            else begin init end in
foldl' ((i + len) - 1) end
else begin raise General.Subscript end
let rec foldr f init (array, i, len) =
  if (i >= 0) && (len >= 0)
  then
    begin let imax = i + len in
          let rec foldr' i' =
            if i' < imax
            then begin f (i', (unsafeSub (array, i')), (foldr' (i' + 1))) end
            else begin init end in
  foldr' i end
else begin raise General.Subscript end
let rec modify f (array, i, len) =
  if (i >= 0) && (len >= 0)
  then
    begin let imax = i + len in
          let rec modify' i' =
            if i' < imax
            then
              begin (begin unsafeUpdate
                             (array, i', (f (i', (unsafeSub (array, i')))));
                     modify' (i' + 1) end) end
            else begin () end in
modify' i end else begin raise General.Subscript end end
