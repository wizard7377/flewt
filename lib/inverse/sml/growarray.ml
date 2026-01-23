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
  end


module GrowArray : GROWARRAY =
  struct
    module A = Array
    type nonrec 'a growarray = (int * 'a option A.array) ref
    let rec empty () = ref (0, (A.array (16, None)))
    let rec growarray n i = ref (n, (A.array (n, (Some i))))
    let rec sub { contents = (used, a) } n =
      if (n < used) && (n >= 0)
      then
        begin begin match A.sub (a, n) with
              | None -> raise Subscript
              | Some z -> z end end
      else begin raise Subscript end
let rec length { contents = (l, _) } = l
let rec accomodate ({ contents = (l, a) } as r) n =
  if (A.length a) >= (n + 1) then begin () end
  else begin
    (let rec nextpower x = if x >= (n + 1) then begin x end
       else begin nextpower (x * 2) end in
let ns = nextpower (A.length a) in
let na =
  A.tabulate
    (ns,
      (begin function
       | i -> if i < l then begin A.sub (a, i) end else begin None end end)) in
r := (l, na)) end
let rec update r n x = if n < 0 then begin raise Subscript end
  else begin
    (let _ = accomodate r n in
     let (l, a) = !r in
     ((begin A.update (a, n, (Some x));
       if n >= l then begin r := ((n + 1), a) end
       else begin () end end)
  (* also update 'used' *))) end
let rec append ({ contents = (n, _) } as r) x =
  let _ = accomodate r (n + 1) in
  let (_, a) = !r in begin A.update (a, n, (Some x)); r := ((n + 1), a) end
let rec used arr n = begin try begin ignore (sub arr n); true end
  with | Subscript -> false end
let rec finalize { contents = (n, a) } =
  A.tabulate
    (n,
      (begin function
       | x ->
           (begin match A.sub (a, x) with
            | None -> raise Subscript
            | Some z -> z end) end)) end
