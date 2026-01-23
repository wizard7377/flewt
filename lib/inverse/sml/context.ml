module type CONTEXT  =
  sig
    type nonrec 'a ctx
    exception Context of string 
    val empty : 'a ctx
    val lookup : ('a ctx * int) -> 'a option
    val push : ('a ctx * 'a) -> 'a ctx
    val list : 'a ctx -> 'a list
  end


module Context : CONTEXT =
  struct
    module L = Lib
    type nonrec 'a ctx = 'a list
    exception Context of string 
    let empty = []
    let rec lookup (l, n) =
      begin try Some (L.ith n l) with | Fail _ -> None end
    let rec push (ctx, p) = p :: ctx
    let rec list l = l end 