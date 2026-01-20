
module type GROWARRAY  =
  sig
    type nonrec 'a growarray
    val growarray : int -> 'a -> 'a growarray
    val empty : unit -> 'a growarray
    val length : 'a growarray -> int
    val sub : 'a growarray -> int -> 'a
    val update : 'a growarray -> int -> 'a -> unit
    val append : 'a growarray -> 'a -> unit
    val used : 'a growarray -> int -> bool
    val finalize : 'a growarray -> 'a Array.array
  end;;




module GrowArray : GROWARRAY =
  struct
    module A = Array
    type nonrec 'a growarray = (int * 'a option A.array) ref
    let rec empty () = ref (0, (A.array (16, None)))
    let rec growarray n i = ref (n, (A.array (n, (Some i))))
    let rec sub { contents = (used, a) } n =
      if (n < used) && (n >= 0)
      then match A.sub (a, n) with | None -> raise Subscript | Some z -> z
      else raise Subscript
    let rec length { contents = (l, _) } = l
    let rec accomodate ({ contents = (l, a) } as r) n =
      if (A.length a) >= (n + 1)
      then ()
      else
        (let rec nextpower x = if x >= (n + 1) then x else nextpower (x * 2) in
         let ns = nextpower (A.length a) in
         let na =
           A.tabulate (ns, (fun i -> if i < l then A.sub (a, i) else None)) in
         r := (l, na))
    let rec update r n x =
      if n < 0
      then raise Subscript
      else
        (let _ = accomodate r n in
         let (l, a) = !r in
         ((A.update (a, n, (Some x));
           if n >= l then r := ((n + 1), a) else ())
           (* also update 'used' *)))
    let rec append ({ contents = (n, _) } as r) x =
      let _ = accomodate r (n + 1) in
      let (_, a) = !r in A.update (a, n, (Some x)); r := ((n + 1), a)
    let rec used arr n =
      try ignore (sub arr n); true with | Subscript -> false
    let rec finalize { contents = (n, a) } =
      A.tabulate
        (n,
          (fun x ->
             match A.sub (a, x) with | None -> raise Subscript | Some z -> z))
  end ;;
