
(** 
 A tabular data structure.
 *)
module type TABLE  =
  sig
    type nonrec key
    type nonrec 'a table
    (** Give the expected size of the eventual table. 
      Some implementations may grow outside that initial
      bound if necessary.  Others may raise an exception.
   *)
    val table : int -> 'a table
    (** Insert a key/value pair into the table.  
      Raise Fail if key is already present. *)
    val insert : 'a table -> (key * 'a) -> 'a table
    (** Lookup a key in the table. Raise Fail if key not present *)
    val lookup : 'a table -> key -> 'a
    (** number of key/value pairs *)
    val size : 'a table -> int
    (** Iterate a procedure over the table. *)
    val app : ('a -> unit) -> 'a table -> unit
    (** Iterate a procedure over the table. *)
    val appi : ((int * 'a) -> unit) -> 'a table -> unit
    (** Clear the table. *)
    val clear : 'a table -> unit
  end;;




(* structure GrowarrayTable : TABLE where type key = int = *)
(* struct *) (*   structure L = Lib *)
(*   structure A = GrowArray *)
(*   type key = int  *)
(*   type 'a table = 'a A.growarray *)
(*   fun empty _ = A.empty() *)
(*   fun size t = A.length t *)
(*   fun insert t (n,v) = *)
(*       if A.length t > n then raise Fail "insert: signat contains key" *)
(*       else (A.update t n v;t) *)
(*   fun lookup t n = A.sub t n *)
(*   fun iter f : ('a -> unit) -> 'a table -> unit *)
(*   val foldl : ('a * 'b -> 'b) -> 'b -> 'a table -> b *)
(*   val foldr : ('a * 'b -> 'b) -> 'b -> 'a table -> b *)
(* end *)
module ArrayTable : TABLE =
  struct
    module L = Lib
    module A = Array
    type nonrec key = int
    type nonrec 'a table = < arr: 'a option array  ;used: int ref   > 
    let rec table n = { arr = (A.array (n, NONE)); used = (ref 0) }
    let rec clear { arr; used; used } =
      used := 0; A.modify (function | _ -> NONE) arr
    let rec insert ({ arr; used; used } as t) (n, v) =
      if (n < 0) || ((>) n A.length arr)
      then raise Subscript
      else
        (match A.sub (arr, n) with
         | NONE ->
             (A.update (arr, n, (SOME v));
              if (!) ((>) n) used then used := n else ();
              t)
         | SOME _ -> raise (Fail "insert: key already present"))
    let rec lookup ({ arr } : 'a table) n =
      if (n < 0) || ((>) n A.length arr)
      then raise Subscript
      else
        (match A.sub (arr, n) with | NONE -> raise Subscript | SOME v -> v)
    let rec size ({ arr } : 'a table) = A.length arr
    exception Done 
    let rec app f { arr; used; used } =
      let used' = !used in
      let rec f' (i, x) =
        if i >= used'
        then raise Done
        else (match x with | SOME n -> f n | NONE -> ()) in
      try A.appi f' arr with | Done -> ()
    let rec appi f { arr; used; used } =
      let used' = !used in
      let rec f' (i, x) =
        if i >= used'
        then raise Done
        else (match x with | SOME n -> f (i, n) | NONE -> ()) in
      try A.appi f' arr with | Done -> ()
  end  module Table = ArrayTable;;
