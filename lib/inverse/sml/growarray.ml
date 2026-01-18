
(** Imperative arrays that automatically grow to
    accomodate new data. The array can have 'holes'
    where no data are stored, though these are not
    treated efficiently. *)
module type GROWARRAY  =
  sig
    type nonrec 'a growarray
    val growarray : int -> 'a -> 'a growarray
    val empty : unit -> 'a growarray
    (** return actual length *)
    val length : 'a growarray -> int
    (** can raise Subscript when out of bounds *)
    val sub : 'a growarray -> int -> 'a
    (** only raises subscript if index is negative. *)
    val update : 'a growarray -> int -> 'a -> unit
    (** stick an element at the end *)
    val append : 'a growarray -> 'a -> unit
    (** true if a position has been set *)
    val used : 'a growarray -> int -> bool
    (** 
     after calling this, don't use the growarray
     any longer, since it may share data with the returned
     array. 

     @exception Subscript if the array has holes.
*)
    val finalize : 'a growarray -> 'a Array.array
  end;;




module GrowArray : GROWARRAY =
  struct
    module A = Array
    type nonrec 'a growarray = (int * 'a option A.array) ref
    (* start with 16 cells, why not? *)
    let rec empty () = ref (0, (A.array (16, NONE)))
    let rec growarray n i = ref (n, (A.array (n, (SOME i))))
    let rec sub (ref (used, a)) n =
      if (n < used) && (n >= 0)
      then match A.sub (a, n) with | NONE -> raise Subscript | SOME z -> z
      else raise Subscript
    let rec length (ref (l, _)) = l
    (* grow to accomodate at least n elements *)
    let rec accomodate (ref (l, a) as r) n =
      if (A.length a) >= (n + 1)
      then ()
      else
        (let rec nextpower x = if x >= (n + 1) then x else nextpower (x * 2) in
         let ns = nextpower (A.length a) in
         let na =
           A.tabulate
             (ns, (function | i -> if i < l then A.sub (a, i) else NONE)) in
         r := (l, na))
    let rec update r n x =
      if n < 0
      then raise Subscript
      else
        (let _ = accomodate r n in
         let (l, a) = !r in
         ((A.update (a, n, (SOME x));
           if n >= l then r := ((n + 1), a) else ())
           (* also update 'used' *)))
    let rec append (ref (n, _) as r) x =
      let _ = accomodate r (n + 1) in
      let (_, a) = !r in A.update (a, n, (SOME x)); r := ((n + 1), a)
    let rec used arr n =
      try ignore (sub arr n); true__ with | Subscript -> false__
    let rec finalize (ref (n, a)) =
      A.tabulate
        (n,
          (function
           | x ->
               (match A.sub (a, x) with
                | NONE -> raise Subscript
                | SOME z -> z)))
  end ;;
