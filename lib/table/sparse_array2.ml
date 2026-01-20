
module type SPARSE_ARRAY2  =
  sig
    type nonrec 'a array
    type nonrec 'a region =
      < base: 'a array  ;row: int  ;col: int  ;nrows: int  ;ncols: int   > 
    type traversal =
      | RowMajor 
      | ColMajor 
    val array : 'a -> 'a array
    val sub : 'a array -> int -> int -> 'a
    val update : 'a array -> int -> int -> 'a -> unit
    val row : 'a array -> int -> (int * int) -> 'a Vector.vector
    val column : 'a array -> int -> (int * int) -> 'a Vector.vector
    val app : traversal -> (int -> int -> 'a -> unit) -> 'a region -> unit
    val fold :
      traversal -> (int -> int -> 'a -> 'b -> 'b) -> 'b -> 'a region -> 'b
    val modify : traversal -> (int -> int -> 'a -> 'a) -> 'a region -> unit
  end;;




module SparseArray2(SparseArray2:sig module IntTable : TABLE end) :
  SPARSE_ARRAY2 =
  struct
    type nonrec 'a array = < default: 'a  ;table: 'a IntTable.__Table   > 
    type nonrec 'a region =
      < base: 'a array  ;row: int  ;col: int  ;nrows: int  ;ncols: int   > 
    type traversal =
      | RowMajor 
      | ColMajor 
    let size = 29
    let rec fromInt code =
      let rec fromInt' r =
        let code' = ( * ) (r + 1) (r + 2) div 2 in
        if code < code'
        then let diff = (code' - code) - 1 in (diff, (r - diff))
        else fromInt' (r + 1) in
      fromInt' 0
    let rec toInt m n = let sum = m + n in (( * ) sum (sum + 1) div 2) + n
    let rec unsafeSub { table; default; default } i j =
      match IntTable.lookup table (toInt (i, j)) with
      | NONE -> default
      | Some v -> v
    let rec unsafeUpdate { table; default; default } i j v =
      IntTable.insert table ((toInt (i, j)), v)
    let rec checkRegion
      { base; row; col; nrows; ncols; row; col; nrows; ncols; col; nrows;
        ncols; nrows; ncols; ncols }
      = (row >= 0) && ((col >= 0) && ((nrows >= 0) && (ncols >= 0)))
    let rec array default = { default; table = (IntTable.new__ size) }
    let rec sub array i j =
      if (i >= 0) && (j >= 0)
      then unsafeSub (array, i, j)
      else raise General.Subscript
    let rec update array i j v =
      if (i >= 0) && (j >= 0)
      then unsafeUpdate (array, i, j, v)
      else raise General.Subscript
    let rec row array i (j, len) =
      if (i >= 0) && ((j >= 0) && (len >= 0))
      then
        Vector.tabulate (len, (fun off -> unsafeSub (array, i, (j + off))))
      else raise General.Subscript
    let rec column array j (i, len) =
      if (j >= 0) && ((i >= 0) && (len >= 0))
      then
        Vector.tabulate (len, (fun off -> unsafeSub (array, (i + off), j)))
      else raise General.Subscript
    let rec app traversal f
      ({ base; row; col; nrows; ncols; row; col; nrows; ncols; col; nrows;
         ncols; nrows; ncols; ncols } as region)
      =
      if checkRegion region
      then
        let rmax = row + nrows in
        let cmax = col + ncols in
        let rec appR row' col' =
          if row' < rmax
          then
            (if col' < cmax
             then
               (f (row', col', (unsafeSub (base, row', col')));
                appR (row', (col' + 1)))
             else appR ((row' + 1), col))
          else () in
        let rec appC row' col' =
          if col' < cmax
          then
            (if row' < rmax
             then
               (f (row', col', (unsafeSub (base, row', col')));
                appC ((row' + 1), col'))
             else appC (row, (col' + 1)))
          else () in
        match traversal with
        | RowMajor -> appR (row, col)
        | ColMajor -> appC (row, col)
      else raise General.Subscript
    let rec fold traversal f init
      ({ base; row; col; nrows; ncols; row; col; nrows; ncols; col; nrows;
         ncols; nrows; ncols; ncols } as region)
      =
      if checkRegion region
      then
        let rmax = row + nrows in
        let cmax = col + ncols in
        let rec foldR row' col' =
          if row' < rmax
          then
            (if col' < cmax
             then
               f
                 (row', col', (unsafeSub (base, row', col')),
                   (foldR (row', (col' + 1))))
             else foldR ((row' + 1), col))
          else init in
        let rec foldC row' col' =
          if col' < cmax
          then
            (if row' < rmax
             then
               f
                 (row', col', (unsafeSub (base, row', col')),
                   (foldC ((row' + 1), col')))
             else foldC (row, (col' + 1)))
          else init in
        match traversal with
        | RowMajor -> foldR (row, col)
        | ColMajor -> foldC (row, col)
      else raise General.Subscript
    let rec modify traversal f
      ({ base; row; col; nrows; ncols; row; col; nrows; ncols; col; nrows;
         ncols; nrows; ncols; ncols } as region)
      =
      if checkRegion region
      then
        let rmax = row + nrows in
        let cmax = col + ncols in
        let rec modifyR row' col' =
          if row' < rmax
          then
            (if col' < cmax
             then
               (unsafeUpdate
                  (base, row', col',
                    (f (row', col', (unsafeSub (base, row', col')))));
                modifyR (row', (col' + 1)))
             else modifyR ((row' + 1), col))
          else () in
        let rec modifyC row' col' =
          if col' < cmax
          then
            (if row' < rmax
             then
               (unsafeUpdate
                  (base, row', col',
                    (f (row', col', (unsafeSub (base, row', col')))));
                modifyC ((row' + 1), col'))
             else modifyC (row, (col' + 1)))
          else () in
        match traversal with
        | RowMajor -> modifyR (row, col)
        | ColMajor -> modifyC (row, col)
      else raise General.Subscript
  end ;;
