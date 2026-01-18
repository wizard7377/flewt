
(**
 A library of useful functions for everyday programming.
*)
module type LIB  =
  sig
    (** Nice for postponing an implementation. *)
    exception Not_implemented 
    (* -------------------------------------------------------------------------- *)
    (*  Booleans                                                                  *)
    (* -------------------------------------------------------------------------- *)
    (** Curried <code> andalso </code> *)
    val andalso' : bool -> bool -> bool
    (** Curried <code> orelse </code> *)
    val orelse' : bool -> bool -> bool
    (* -------------------------------------------------------------------------- *)
    (*  Pairs                                                                     *)
    (* -------------------------------------------------------------------------- *)
    (** First element of a pair. *)
    val fst : ('a * 'b) -> 'a
    (** Second element of a pair. *)
    val snd : ('a * 'b) -> 'b
    (* -------------------------------------------------------------------------- *)
    (*  Options                                                                   *)
    (* -------------------------------------------------------------------------- *)
    val is_none : 'a option -> bool
    val is_some : 'a option -> bool
    (** Get the content of an option type. 
      @exception Fail
   *)
    val the : 'a option -> 'a
    (* ------------------------------------------------------------------------- *)
    (*  Refs                                                                     *)
    (* ------------------------------------------------------------------------- *)
    (** Increment an <code> int ref <\code> *)
    val incr : int ref -> unit
    (** Increment an <code> int ref <\code> *)
    val (+=) : (int ref * int) -> unit
    (** Decrement an <code> int ref <\code> *)
    val (-=) : (int ref * int) -> unit
    (** Decrement an <code> int ref <\code> *)
    val decr : int ref -> unit
    (** Prepend an element to a <code> list </code> *)
    val ::= : ('a list ref * 'a) -> unit
    (** Append a list at the back of a <code> list </code> *)
    val (@=) : ('a list ref * 'a list) -> unit
    (* -------------------------------------------------------------------------- *)
    (*  Streams                                                                   *)
    (* -------------------------------------------------------------------------- *)
    (** Infinite streams. *)
    type nonrec 'a stream
    (** Prefix of a stream, as a list *)
    val listof_s : int -> 'a stream -> 'a list
    (** 
     Select an element from a stream
     @exception Fail if there are not enough elements in the stream.
   *)
    val nth_s : int -> 'a stream -> 'a
    (* ---------------------------------------------------------------------- *)
    (*  Functions                                                             *)
    (* ---------------------------------------------------------------------- *)
    (** Curry a function. *)
    val curry : (('a * 'b) -> 'c) -> 'a -> 'b -> 'c
    (** Uncurry a function. *)
    val uncurry : ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
    (** Curry a 3 argument function.  Occasionally useful. *)
    val curry3 : (('a * 'b * 'c) -> 'd) -> 'a -> 'b -> 'c -> 'd
    (** Identity combinator *)
    val id : 'a -> 'a
    (** Returns true iff a function application returns a value. *)
    val can : ('a -> 'b) -> 'a -> bool
    (** Returns true iff a function application raises an exception. *)
    val cant : ('a -> 'b) -> 'a -> bool
    (** Returns true iff a (2 argument) function application returns a value. *)
    val can2 : ('a -> 'b -> 'c) -> 'a -> 'b -> bool
    (** Curried equality *)
    val ceq : 'a -> 'a -> bool
    (** Swap the arguments of a function. *)
    val swap : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
    (** Explicit application. *)
    val apply : (('a -> 'b) * 'a) -> 'b
    (** Apply a function a given number of times. *)
    val repeat : ('a -> 'a) -> int -> 'a -> 'a
    (* -------------------------------------------------------------------------- *)
    (*  Ints                                                                      *)
    (* -------------------------------------------------------------------------- *)
    (** Add up a list of ints *)
    val sum : int list -> int
    (** max of a list of ints *)
    val max : int list -> int
    (** upto 3 5 ~~> [3,4,5] *)
    val upto : (int * int) -> int list
    (** @see upto *)
    val (--) : (int * int) -> int list
    (** 3 --< 5 ~~> [3,4] *)
    val (--<) : (int * int) -> int list
    (* -------------------------------------------------------------------------- *)
    (*  Reals                                                                     *)
    (* -------------------------------------------------------------------------- *)
    (** max of a list of reals *)
    val real_max : real list -> real
    (** sum of a list of reals *)
    val real_sum : real list -> real
    (* ------------------------------------------------------------------------- *)
    (*  Order                                                                    *)
    (* ------------------------------------------------------------------------- *)
    val string_ord : (string * string) -> order
    val int_ord : (int * int) -> order
    val lex_ord :
      (('a * 'b) -> order) ->
        (('c * 'd) -> order) -> (('a * 'c) * ('b * 'd)) -> order
    val eq_ord : ('a * 'a) -> order
    (* ---------------------------------------------------------------------- *)
    (*  Debug                                                                 *)
    (* ---------------------------------------------------------------------- *)
    val assert__ : bool -> string -> unit
    (** !warn = true iff <code> warning s</code> will print 
      <code> s</code> to stdout. *)
    val warn : bool ref
    (** Print a warning message to stdout.  
   @see warn
   *)
    val warning : string -> unit
    (* ---------------------------------------------------------------------- *)
    (*  Lists                                                                 *)
    (* ---------------------------------------------------------------------- *)
    (** Cons. *)
    val cons : 'a -> 'a list -> 'a list
    (** Singleton list. *)
    val list : 'a -> 'a list
    val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val citlist : (('a * 'b) -> 'b) -> 'a list -> 'b -> 'b
    val ith : int -> 'a list -> 'a
    val map2 : (('a * 'b) -> 'c) -> 'a list -> 'b list -> 'c list
    val map3 :
      (('a * 'b * 'c) -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
    val zip : 'a list -> 'b list -> ('a * 'b) list
    val zip3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
    val zip4 :
      'a list -> 'b list -> 'c list -> 'd list -> ('a * 'b * 'c * 'd) list
    val zip5 :
      'a list ->
        'b list ->
          'c list -> 'd list -> 'e list -> ('a * 'b * 'c * 'd * 'e) list
    val unzip : ('a * 'b) list -> ('a list * 'b list)
    val unzip3 : ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
    val unzip4 :
      ('a * 'b * 'c * 'd) list -> ('a list * 'b list * 'c list * 'd list)
    val (~~) : ('a list * 'b list) -> ('a * 'b) list
    val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
    val end_citlist : (('a * 'a) -> 'a) -> 'a list -> 'a
    val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
    val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val rev_end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
    val replicate : 'a -> int -> 'a list
    val exists : ('a -> bool) -> 'a list -> bool
    val forall : ('a -> bool) -> 'a list -> bool
    val last : 'a list -> 'a
    val butlast : 'a list -> 'a list
    val gen_list_eq : (('a * 'b) -> order) -> 'a list -> 'b list -> bool
    val list_eq : 'a list -> 'a list -> bool
    val partition : ('a -> bool) -> 'a list -> ('a list * 'a list)
    val filter : ('a -> bool) -> 'a list -> 'a list
    val sort : (('a * 'a) -> order) -> 'a list -> 'a list
    val uniq : (('a * 'a) -> order) -> 'a list -> 'a list
    val uniq_list : (('a * 'a) -> order) -> 'a list -> bool
    val split_at : int -> 'a list -> ('a list * 'a list)
    val list_prefix : int -> 'a list -> 'a list
    val list_slice : int -> int -> 'a list -> 'a list
    val shuffle : 'a list -> 'a list -> 'a list
    val find_index : ('a -> bool) -> 'a list -> int option
    val index : 'a -> 'a list -> int option
    val find_last_index : ('a -> bool) -> 'a list -> int option
    val last_index : 'a -> 'a list -> int option
    val flatten : 'a list list -> 'a list
    val chop_list : int -> 'a list -> ('a list * 'a list)
    val list_to_string : ('a -> string) -> 'a list -> string
    val remove : ('a -> bool) -> 'a list -> ('a * 'a list)
    val do_list : ('a -> 'b) -> 'a list -> unit
    val exn_index : ('a -> 'b) -> 'a list -> int option
    (* ------------------------------------------------------------------------- *)
    (*  Lists as Sets                                                            *)
    (* ------------------------------------------------------------------------- *)
    val gen_setify : (('a * 'a) -> order) -> 'a list -> 'a list
    val setify : 'a list -> 'a list
    val gen_mem : (('a * 'b) -> order) -> 'a -> 'b list -> bool
    val mem : 'a -> 'a list -> bool
    val insert : 'a -> 'a list -> 'a list
    val gen_disjoint : (('a * 'b) -> order) -> 'a list -> 'b list -> bool
    val disjoint : 'a list -> 'a list -> bool
    val gen_pairwise_disjoint : (('a * 'a) -> order) -> 'a list list -> bool
    val pairwise_disjoint : 'a list list -> bool
    val gen_set_eq : (('a * 'a) -> order) -> 'a list -> 'a list -> bool
    val diff : 'a list -> 'a list -> 'a list
    val union : 'a list -> 'a list -> 'a list
    val unions : 'a list list -> 'a list
    val intersect : 'a list -> 'a list -> 'a list
    val subtract : 'a list -> 'a list -> 'a list
    val subset : 'a list -> 'a list -> bool
    val set_eq : 'a list -> 'a list -> bool
    (* ------------------------------------------------------------------------- *)
    (*  Assoc lists                                                              *)
    (* ------------------------------------------------------------------------- *)
    val find : ('a -> bool) -> 'a list -> 'a option
    val assoc : 'a -> ('a * 'b) list -> 'b option
    val rev_assoc : 'a -> ('b * 'a) list -> 'b option
    (* -------------------------------------------------------------------------- *)
    (*  Printing                                                                  *)
    (* -------------------------------------------------------------------------- *)
    val printl : string -> unit
  end;;




module Lib : LIB =
  struct
    exception Not_implemented 
    (* ------------------------------------------------------------------------- *)
    (*  Booleans                                                                 *)
    (* ------------------------------------------------------------------------- *)
    let rec andalso' x y = x && y
    let rec orelse' x y = x || y
    (* ---------------------------------------------------------------------- *)
    (*  Pairs                                                                 *)
    (* ---------------------------------------------------------------------- *)
    let rec fst (x, y) = x
    let rec snd (x, y) = y
    (* -------------------------------------------------------------------------- *)
    (*  Options                                                                   *)
    (* -------------------------------------------------------------------------- *)
    let rec is_none = function | None -> true__ | Some _ -> false__
    let rec is_some = function | None -> false__ | Some _ -> true__
    let rec the = function | None -> raise (Fail "the") | Some x -> x
    (* ------------------------------------------------------------------------- *)
    (*  Refs                                                                     *)
    (* ------------------------------------------------------------------------- *)
    let rec x ((+=)) n = (x := (!x)) + n
    let rec x ((-=)) n = (x := (!x)) - n
    let rec incr x = x += 1
    let rec decr x = x -= 1
    let rec l (::=) v = (l := v) :: (!l)
    let rec l ((@=)) l' = (l := (!l)) @ l'
    (* -------------------------------------------------------------------------- *)
    (*  Streams                                                                   *)
    (* -------------------------------------------------------------------------- *)
    type 'a stream =
      | SNil 
      | SCons of (unit -> ('a * 'a stream)) 
    let rec constant_s x = SCons (function | () -> (x, (constant_s x)))
    let rec ones_f n = SCons (function | () -> (n, (ones_f (n + 1))))
    let nat_s = ones_f 0
    let rec nth_s arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, SNil) -> raise (Fail "s_nth")
      | (0, SCons f) -> fst (f ())
      | (n, SCons f) -> let (_, s') = f () in nth_s (n - 1) s'
    let rec listof_s arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (0, _) -> []
      | (n, SNil) -> raise (Fail "listof_s")
      | (n, SCons f) -> let (v, s) = f () in (::) v listof_s (n - 1) s
    (* ---------------------------------------------------------------------- *)
    (*  Functions                                                             *)
    (* ---------------------------------------------------------------------- *)
    let rec curry f x y = f (x, y)
    let rec uncurry f (x, y) = f x y
    let rec curry3 f x y z = f (x, y, z)
    let rec id x = x
    let rec can f x = try f x; true__ with | _ -> false__
    let rec cant f x = try f x; false__ with | _ -> true__
    let rec can2 f x y = try f x y; true__ with | _ -> false__
    let rec ceq x y = x = y
    let rec oo f g x y = f (g x y)
    let rec ooo f g x y z = f (g x y z)
    let rec oooo f g x y z w = f (g x y z w)
    let rec swap f x y = f y x
    let rec apply (f, x) = f x
    let rec repeat f n x = if n = 0 then x else repeat f (n - 1) (f x)
    (* -------------------------------------------------------------------------- *)
    (*  Ints                                                                      *)
    (* -------------------------------------------------------------------------- *)
    let rec max xs = foldr Int.max 0 xs
    let rec sum ns = foldr (+) 0 ns
    let rec uptoby k m n = if m > n then [] else m :: (uptoby k (m + k) n)
    let upto = uncurry (uptoby 1)
    let (--) = upto
    let rec x ((--<)) y = x -- (y - 1)
    let rec pow x n =
      match n with
      | 0 -> 1
      | n ->
          if (Int.mod__ (n, 2)) = 0
          then let n' = pow x (Int.div (n, 2)) in n' * n'
          else ( * ) x pow x (n - 1)
    let rec log n =
      let rec log n even =
        match n with
        | 1 -> (0, even)
        | n ->
            let (ln, even') = log (Int.div (n, 2)) even in
            let even'' = even' && ((Int.mod__ (n, 2)) = 0) in
            ((1 + ln), even'') in
      log n true__
    (* -------------------------------------------------------------------------- *)
    (*  Reals                                                                     *)
    (* -------------------------------------------------------------------------- *)
    let rec real_max xs = foldr Real.max 0.0 xs
    let rec real_sum rs = foldr (+) 0.0 rs
    (* ------------------------------------------------------------------------- *)
    (*  Order                                                                    *)
    (* ------------------------------------------------------------------------- *)
    let rec string_ord ((s1 : string), s2) =
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER
    let rec int_ord ((s1 : int), s2) =
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER
    let rec lex_ord o1 o2 ((x1, y1), (x2, y2)) =
      match o1 (x1, x2) with | EQUAL -> o2 (y1, y2) | x -> x
    let rec eq_ord (x, y) = if x = y then EQUAL else LESS
    (* ---------------------------------------------------------------------- *)
    (*  Debug                                                                 *)
    (* ---------------------------------------------------------------------- *)
    let rec assert__ b s =
      if b then () else raise (Fail ("Assertion Failure: " ^ s))
    let warn = ref true__
    let rec warning s =
      if !warn then TextIO.print (("Warning: " ^ s) ^ "\n") else ()
    (* ---------------------------------------------------------------------- *)
    (*  Lists                                                                 *)
    (* ---------------------------------------------------------------------- *)
    let rec list x = [x]
    let rec cons x xs = x :: xs
    (* same as foldr *)
    let rec itlist arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (f, [], b) -> b
      | (f, h::t, b) -> f h (itlist f t b)
    let rec citlist f l b = itlist (curry f) l b
    let rec ith arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (i, []) -> raise (Fail "ith: empty")
      | (0, h::t) -> h
      | (n, h::t) -> ith (n - 1) t
    let rec map2 arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (f, [], []) -> []
      | (f, h1::t1, h2::t2) -> (::) (f (h1, h2)) map2 f t1 t2
      | (f, _, _) -> raise (Fail "map2: length mismatch")
    let rec map3 arg__0 arg__1 arg__2 arg__3 =
      match (arg__0, arg__1, arg__2, arg__3) with
      | (f, [], [], []) -> []
      | (f, h1::t1, h2::t2, h3::t3) -> (::) (f (h1, h2, h3)) map3 f t1 t2 t3
      | (f, _, _, _) -> raise (Fail "map3: unequal lengths")
    let rec map4 arg__0 arg__1 arg__2 arg__3 arg__4 =
      match (arg__0, arg__1, arg__2, arg__3, arg__4) with
      | (f, [], [], [], []) -> []
      | (f, h1::t1, h2::t2, h3::t3, h4::t4) ->
          (::) (f (h1, h2, h3, h4)) map4 f t1 t2 t3 t4
      | (f, _, _, _, _) -> raise (Fail "map4: unequal lengths")
    let rec map5 arg__0 arg__1 arg__2 arg__3 arg__4 arg__5 =
      match (arg__0, arg__1, arg__2, arg__3, arg__4, arg__5) with
      | (f, [], [], [], [], []) -> []
      | (f, h1::t1, h2::t2, h3::t3, h4::t4, h5::t5) ->
          (::) (f (h1, h2, h3, h4, h5)) map5 f t1 t2 t3 t4 t5
      | (f, _, _, _, _, _) -> raise (Fail "map5: unequal lengths")
    let rec zip l1 l2 = map2 id l1 l2
    let rec zip3 l1 l2 l3 = map3 id l1 l2 l3
    let rec zip4 l1 l2 l3 l4 = map4 id l1 l2 l3 l4
    let rec zip5 l1 l2 l3 l4 l5 = map5 id l1 l2 l3 l4 l5
    let rec unzip l =
      itlist
        (function
         | (h1, h2) -> (function | (t1, t2) -> ((h1 :: t1), (h2 :: t2)))) l
        ([], [])
    let rec unzip3 l =
      itlist
        (function
         | (h1, h2, h3) ->
             (function | (t1, t2, t3) -> ((h1 :: t1), (h2 :: t2), (h3 :: t3))))
        l ([], [], [])
    let rec unzip4 l =
      itlist
        (function
         | (h1, h2, h3, h4) ->
             (function
              | (t1, t2, t3, t4) ->
                  ((h1 :: t1), (h2 :: t2), (h3 :: t3), (h4 :: t4)))) l
        ([], [], [], [])
    let rec x ((~~)) y = zip x y
    let rec end_itlist arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, []) -> raise (Fail "end_itlist")
      | (f, x::[]) -> x
      | (f, h::t) -> f h (end_itlist f t)
    let rec end_citlist f l = end_itlist (curry f) l
    let rec itlist2 arg__0 arg__1 arg__2 arg__3 =
      match (arg__0, arg__1, arg__2, arg__3) with
      | (f, [], [], b) -> b
      | (f, h1::t1, h2::t2, b) -> f h1 h2 (itlist2 f t1 t2 b)
      | (_, _, _, _) -> raise (Fail "itlist2")
    (* same as foldl *)
    let rec rev_itlist arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (f, [], b) -> b
      | (f, h::t, b) -> rev_itlist f t (f h b)
    let rec rev_end_itlist arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, []) -> raise (Fail "rev_end_itlist")
      | (f, x::[]) -> x
      | (f, h::t) -> f (rev_end_itlist f t) h
    let rec replicate arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (x, 0) -> []
      | (x, n) -> if n > 0 then (::) x replicate x (n - 1) else []
    let rec exists arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, []) -> false__
      | (f, h::t) -> (f h) || (exists f t)
    let rec forall arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, []) -> true__
      | (f, h::t) -> (f h) && (forall f t)
    let rec last =
      function | [] -> raise (Fail "Last") | h::[] -> h | h::t -> last t
    let rec butlast =
      function
      | [] -> raise (Fail "Butlast")
      | h::[] -> []
      | h::t -> (::) h butlast t
    let rec gen_list_eq ord l1 l2 =
      itlist2
        (function
         | x ->
             (function | y -> (function | z -> ((ord (x, y)) = EQUAL) && z)))
        l1 l2 true__
    let rec list_eq l1 l2 = gen_list_eq eq_ord l1 l2
    let rec partition arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, []) -> ([], [])
      | (p, h::t) ->
          let (l, r) = partition p t in
          if p h then ((h :: l), r) else (l, (h :: r))
    let rec filter p l = fst (partition p l)
    let rec sort arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (ord, []) -> []
      | (ord, piv::rest) ->
          let (l, r) = partition (function | x -> (ord (x, piv)) = LESS) rest in
          (sort ord l) @ (piv :: (sort ord r))
    let rec uniq arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (ord, x::(y::_ as t)) ->
          let t' = uniq ord t in if (ord (x, y)) = EQUAL then t' else x :: t'
      | (_, l) -> l
    let rec uniq_list comp l = (=) (length (uniq comp l)) length l
    let rec split_at arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (_, []) -> raise (Fail "split_at: splitting empty")
      | (0, l) -> ([], l)
      | (n, (x::ys as xs)) ->
          if n < 0
          then raise (Fail "split_at: arg out of range")
          else (let (ps, qs) = split_at (n - 1) ys in ((x :: ps), qs))
    let rec list_prefix n l =
      try fst (split_at n l) with | Fail _ -> raise (Fail "list_prefix")
    let rec list_slice n m l =
      let (_, r) = split_at n l in let (l', _) = split_at m r in l'
    let rec shuffle arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ([], l2) -> l2
      | (l1, []) -> l1
      | (h1::t1, h2::t2) -> (::) (h1 :: h2) shuffle t1 t2
    let rec find_index p =
      let rec ind arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (n, []) -> None
        | (n, h::t) -> if p h then Some n else ind (n + 1) t in
      ind 0
    let rec index x l = find_index (ceq x) l
    let rec find_last_index p l =
      let n = length l in
      let l' = rev l in
      match find_index p l' with
      | Some n' -> Some ((n - n') - 1)
      | None -> None
    let rec last_index x l = find_last_index (ceq x) l
    let rec flatten l = itlist (curry (@)) l []
    let rec chop_list arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (0, l) -> ([], l)
      | (n, l) ->
          (try
             let (l1, l2) = chop_list (n - 1) (tl l) in (((hd l) :: l1), l2)
           with | _ -> raise (Fail "chop_list"))
    let rec list_to_string f l =
      let l' = map f l in
      itlist (function | x -> (function | y -> (x ^ ",") ^ y))
        (("[" :: l') @ ["]"]) ""
    let rec remove arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, []) -> raise (Fail "remove")
      | (p, h::t) ->
          if p h then (h, t) else (let (y, n) = remove p t in (y, (h :: n)))
    let rec do_list arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, []) -> ()
      | (f, h::t) -> (f h; do_list f t)
    let rec exn_index f l =
      let rec exn_index arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | (f, [], n) -> None
        | (f, h::t, n) -> if can f h then exn_index f t (n + 1) else Some n in
      exn_index f l 0
    (* ------------------------------------------------------------------------- *)
    (*  Lists as Sets                                                            *)
    (* ------------------------------------------------------------------------- *)
    let rec gen_setify ord s = uniq ord (sort ord s)
    let rec setify s = gen_setify eq_ord s
    let rec gen_mem arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (ord, x, []) -> false__
      | (ord, x, h::t) ->
          if (ord (x, h)) = EQUAL then true__ else gen_mem ord x t
    let rec mem x l = gen_mem eq_ord x l
    let rec insert x l = if mem x l then l else x :: l
    let rec gen_disjoint ord l1 l2 =
      forall (function | x -> not (gen_mem ord x l2)) l1
    let rec disjoint l = gen_disjoint eq_ord l
    let rec gen_pairwise_disjoint arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, []) -> true__
      | (p, h::t) ->
          (forall (gen_disjoint p h) t) && (gen_pairwise_disjoint p t)
    let rec pairwise_disjoint t = gen_pairwise_disjoint eq_ord t
    let rec gen_set_eq ord l1 l2 =
      gen_list_eq ord (gen_setify ord l1) (gen_setify ord l2)
    let rec diff arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ([], l) -> []
      | (h::t, l) -> if mem h l then diff t l else (::) h diff t l
    let rec union l1 l2 = itlist insert l1 l2
    let rec unions l = itlist union l []
    let rec intersect l1 l2 = filter (function | x -> mem x l2) l1
    let rec subtract l1 l2 = filter (function | x -> not (mem x l2)) l1
    let rec subset l1 l2 = forall (function | t -> mem t l2) l1
    let rec set_eq l1 l2 = (subset l1 l2) && (subset l2 l1)
    (* ------------------------------------------------------------------------- *)
    (*  Assoc lists                                                              *)
    (* ------------------------------------------------------------------------- *)
    let rec find arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, []) -> None
      | (p, h::t) -> if p h then Some h else find p t
    let rec assoc x l =
      match find (function | p -> (fst p) = x) l with
      | Some (x, y) -> Some y
      | None -> None
    let rec rev_assoc x l =
      match find (function | p -> (snd p) = x) l with
      | Some (x, y) -> Some x
      | None -> None
    (* ------------------------------------------------------------------------- *)
    (*  Strings                                                                  *)
    (* ------------------------------------------------------------------------- *)
    let rec char_max c1 c2 = if (<) (Char.ord c1) Char.ord c2 then c1 else c2
    let rec string_lt (x : string) y = x < y
    let rec collect l = itlist (curry (^)) l ""
    let rec commas n = replicate "," n
    let rec shuffle_commas l = shuffle l (commas ((length l) - 1))
    let rec semis n = replicate ";" n
    let rec parenify x = collect ["("; x; ")"]
    let rec postfix n s = substring (s, ((size s) - n), n)
    let numeric_chars = "0123456789"
    let lowercase_chars = "abcdefghijklmnopqrstuvwxyz"
    let uppercase_chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    let alpha_chars = lowercase_chars ^ uppercase_chars
    let alphanum_chars = alpha_chars ^ numeric_chars
    let word_sym_chars = "_'"
    let word_chars = alphanum_chars ^ word_sym_chars
    let explode = String.explode
    let rec is_legal u s =
      forall (function | x -> mem x (explode u)) (explode s)
    let is_numeric = is_legal numeric_chars
    let is_lower = is_legal lowercase_chars
    let is_upper = is_legal uppercase_chars
    let is_alpha = is_legal alpha_chars
    let is_alnum = is_legal alphanum_chars
    let is_word_sym = is_legal word_sym_chars
    let is_word = is_legal word_chars
    let to_lower = String.translate (Char.toString o Char.toLower)
    let to_upper = String.translate (Char.toString o Char.toUpper)
    let rec capitalize s =
      match map Char.toString (explode s) with
      | [] -> ""
      | h::t -> concat ([to_upper h] @ (map to_lower t))
    let newline = Char.toString '\n'
    let rec ends_with s e =
      try (substring (s, ((-) (size s) size e), (size e))) = e
      with | _ -> false__
    let rec starts_with s e =
      try (substring (s, 0, (size e))) = e with | _ -> false__
    (* abc.def.ghi -> (abc,def.ghi) *)
    let rec strip_path c s =
      let n =
        match index c (String.explode s) with
        | Some x -> x
        | None -> raise (Fail "strip_path") in
      let m = substring (s, 0, n) in
      let m' = substring (s, (n + 1), (((size s) - n) - 1)) in (m, m')
    (* abc.def.ghi -> (abc.def,ghi) *)
    let rec rev_strip_path c s =
      let no = last_index c (String.explode s) in
      let n =
        match no with | Some x -> x | None -> raise (Fail "rev_strip_path") in
      let m = substring (s, 0, n) in
      let m' = substring (s, (n + 1), (((size s) - n) - 1)) in (m, m')
    (* ------------------------------------------------------------------------- *)
    (*  Options                                                                  *)
    (* ------------------------------------------------------------------------- *)
    let rec the = function | Some x -> x | _ -> raise (Fail "the")
    let rec is_some = function | Some _ -> true__ | _ -> false__
    let rec is_none = function | None -> true__ | _ -> false__
    let rec list_of_opt_list =
      function
      | [] -> []
      | (None)::t -> list_of_opt_list t
      | (Some x)::t -> (::) x list_of_opt_list t
    let rec get_opt arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Some x, _) -> x
      | (None, err) -> raise (Fail err)
    let rec get_list = function | Some l -> l | None -> []
    let rec conv_opt arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, Some l) -> Some (f l)
      | (f, None) -> None
    (* ------------------------------------------------------------------------- *)
    (*  Timing                                                                   *)
    (* ------------------------------------------------------------------------- *)
    let rec time f x =
      let timer = Timer.startCPUTimer () in
      try
        let res = f x in
        let time = Timer.checkCPUTimer timer in
        let _ =
          print
            ((^) "CPU time (user): " Time.toString ((fun r -> r.usr) time)) in
        res
      with
      | e ->
          let time = Timer.checkCPUTimer timer in
          (print
             ((^) "Failed after (user) CUP time of " Time.toString
                ((fun r -> r.usr) time));
           raise e)
    (* ------------------------------------------------------------------------- *)
    (*  IO                                                                       *)
    (* ------------------------------------------------------------------------- *)
    let rec printl s = print (s ^ "\n")
    let rec read_file file =
      let f = TextIO.openIn file in
      let s = TextIO.inputAll f in let _ = TextIO.closeIn f in s
    let rec write_file file s =
      let f = TextIO.openOut file in
      let _ = TextIO.output (f, s) in let _ = TextIO.closeOut f in ()
    let rec write_file_append file s =
      let f = TextIO.openAppend file in
      let _ = TextIO.output (f, s) in let _ = TextIO.closeOut f in ()
    let rec all_dir_files dir =
      let str = OS.FileSys.openDir dir in
      let fs = ref [] in
      let f = ref (OS.FileSys.readDir str) in
      while (!f) <> None do (::= fs the (!f); (:=) f OS.FileSys.readDir str)
        done;
      !fs
  end ;;
