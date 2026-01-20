
module type TABLE  =
  sig
    type nonrec key
    type nonrec 'a table
    val table : int -> 'a table
    val insert : 'a table -> key -> 'a -> 'a table
    val lookup : 'a table -> key -> 'a
    val size : 'a table -> int
    val app : ('a -> unit) -> 'a table -> unit
    val appi : (int -> 'a -> unit) -> 'a table -> unit
    val clear : 'a table -> unit
  end;;




module ArrayTable : TABLE =
  struct
    module L = Lib
    module A = Array
    type nonrec key = int
    type nonrec 'a table = < arr: 'a option array  ;used: int ref   > 
    let rec table n = { arr = (A.array (n, NONE)); used = (ref 0) }
    let rec clear { arr; used; used } =
      used := 0; A.modify (fun _ -> NONE) arr
    let rec insert ({ arr; used; used } as t) n v =
      if (n < 0) || ((>) n A.length arr)
      then raise Subscript
      else
        (match A.sub (arr, n) with
         | NONE ->
             (A.update (arr, n, (Some v));
              if (!) ((>) n) used then used := n else ();
              t)
         | Some _ -> raise (Fail "insert: key already present"))
    let rec lookup { arr } n =
      if (n < 0) || ((>) n A.length arr)
      then raise Subscript
      else
        (match A.sub (arr, n) with | NONE -> raise Subscript | Some v -> v)
    let rec size { arr } = A.length arr
    exception Done 
    let rec app f { arr; used; used } =
      let used' = !used in
      let rec f' i x =
        if i >= used'
        then raise Done
        else (match x with | Some n -> f n | NONE -> ()) in
      try A.appi f' arr with | Done -> ()
    let rec appi f { arr; used; used } =
      let used' = !used in
      let rec f' i x =
        if i >= used'
        then raise Done
        else (match x with | Some n -> f (i, n) | NONE -> ()) in
      try A.appi f' arr with | Done -> ()
  end  module Table = ArrayTable;;
