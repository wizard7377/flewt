open Table_sig
open Basis.General
module type SPARSE_ARRAY2  =
  sig
    type nonrec 'a array
    type nonrec 'a region =
      { base: 'a array  ;row: int  ;col: int  ;nrows: int  ;ncols: int   }
    type traversal =
      | RowMajor
      | ColMajor 
    val array : 'a -> 'a array
    val sub : ('a array * int * int) -> 'a
    val update : ('a array * int * int * 'a) -> unit 
    val row : ('a array * int * (int * int)) -> 'a Array.t
    val column : ('a array * int * (int * int)) -> 'a Array.t
    val app : traversal -> ((int * int * 'a) -> unit) -> 'a region -> unit
    val fold :
      traversal -> ((int * int * 'a * 'b) -> 'b) -> 'b -> 'a region -> 'b
    val modify : traversal -> ((int * int * 'a) -> 'a) -> 'a region -> unit
  end


module SparseArray2(SparseArray2:sig module IntTable : TABLE with type key = int end) :
  SPARSE_ARRAY2 =
  struct
    type nonrec 'a array = { default: 'a  ;table: 'a SparseArray2.IntTable.table_   }
    type nonrec 'a region =
      { base: 'a array  ;row: int  ;col: int  ;nrows: int  ;ncols: int   }
    type traversal =
      | RowMajor 
      | ColMajor 
    let size = 29
    let rec fromInt code =
      let rec fromInt' r =
        let code' = ( * ) (r + 1) (r + 2) / 2 in
        if code < code'
        then begin let diff = (code' - code) - 1 in (diff, (r - diff)) end
          else begin fromInt' (r + 1) end in
    fromInt' 0
  let rec toInt (m, n) = let sum = m + n in (( * ) sum (sum + 1) / 2) + n
  let rec unsafeSub ({ table; default }, i, j) =
    begin match SparseArray2.IntTable.lookup table (toInt (i, j)) with
    | None -> default
    | Some v -> v end
let rec unsafeUpdate ({ table; default }, i, j, v) =
  SparseArray2.IntTable.insert table ((toInt (i, j)), v)
let rec checkRegion { base; row; col; nrows; ncols } =
  (row >= 0) && ((col >= 0) && ((nrows >= 0) && (ncols >= 0)))
let rec array default = { default; table = (SparseArray2.IntTable.new_ size) }
let rec sub (array, i, j) =
  if (i >= 0) && (j >= 0) then begin unsafeSub (array, i, j) end
  else begin raise Basis.General.Subscript end
let rec update (array, i, j, v) =
  if (i >= 0) && (j >= 0) then begin unsafeUpdate (array, i, j, v) end
  else begin raise Basis.General.Subscript end
let rec row (array, i, (j, len)) =
  if (i >= 0) && ((j >= 0) && (len >= 0))
  then
    begin Array.init len
            (begin function | off -> unsafeSub (array, i, (j + off)) end) end
  else begin raise Basis.General.Subscript end
let rec column (array, j, (i, len)) =
  if (j >= 0) && ((i >= 0) && (len >= 0))
  then
    begin Array.init len
            (begin function | off -> unsafeSub (array, (i + off), j) end) end
  else begin raise Basis.General.Subscript end
let rec app traversal f ({ base; row; col; nrows; ncols } as region) =
  if checkRegion region
  then
    begin let rmax = row + nrows in
          let cmax = col + ncols in
          let rec appR (row', col') =
            if row' < rmax
            then
              begin (if col' < cmax
                     then
                       begin (begin f
                                      (row', col',
                                        (unsafeSub (base, row', col')));
                              appR (row', (col' + 1)) end) end
            else begin appR ((row' + 1), col) end) end else begin () end in
let rec appC (row', col') =
  if col' < cmax
  then
    begin (if row' < rmax
           then
             begin (begin f (row', col', (unsafeSub (base, row', col')));
                    appC ((row' + 1), col') end) end
  else begin appC (row, (col' + 1)) end) end else begin () end in
begin match traversal with
| RowMajor -> appR (row, col)
| ColMajor -> appC (row, col) end end
else begin raise Basis.General.Subscript end
let rec fold traversal f init ({ base; row; col; nrows; ncols } as region) =
  if checkRegion region
  then
    begin let rmax = row + nrows in
          let cmax = col + ncols in
          let rec foldR (row', col') =
            if row' < rmax
            then
              begin (if col' < cmax
                     then
                       begin f
                               (row', col', (unsafeSub (base, row', col')),
                                 (foldR (row', (col' + 1)))) end
              else begin foldR ((row' + 1), col) end) end
            else begin init end in
let rec foldC (row', col') =
  if col' < cmax
  then
    begin (if row' < rmax
           then
             begin f
                     (row', col', (unsafeSub (base, row', col')),
                       (foldC ((row' + 1), col'))) end
    else begin foldC (row, (col' + 1)) end) end
  else begin init end in
begin match traversal with
| RowMajor -> foldR (row, col)
| ColMajor -> foldC (row, col) end end
else begin raise Basis.General.Subscript end
let rec modify traversal f ({ base; row; col; nrows; ncols } as region) =
  if checkRegion region
  then
    begin let rmax = row + nrows in
          let cmax = col + ncols in
          let rec modifyR (row', col') =
            if row' < rmax
            then
              begin (if col' < cmax
                     then
                       begin (begin unsafeUpdate
                                      (base, row', col',
                                        (f
                                           (row', col',
                                             (unsafeSub (base, row', col')))));
                              modifyR (row', (col' + 1)) end) end
            else begin modifyR ((row' + 1), col) end) end else begin () end in
let rec modifyC (row', col') =
  if col' < cmax
  then
    begin (if row' < rmax
           then
             begin (begin unsafeUpdate
                            (base, row', col',
                              (f (row', col', (unsafeSub (base, row', col')))));
                    modifyC ((row' + 1), col') end) end
  else begin modifyC (row, (col' + 1)) end) end else begin () end in
begin match traversal with
| RowMajor -> modifyR (row, col)
| ColMajor -> modifyC (row, col) end end else begin raise Basis.General.Subscript end
end
