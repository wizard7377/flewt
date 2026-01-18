
module type BASIC_STREAM  =
  sig
    type nonrec 'a stream
    type 'a front =
      | Empty 
      | Cons of ('a * 'a stream) 
    val delay : (unit -> 'a front) -> 'a stream
    val expose : 'a stream -> 'a front
    val empty : 'a stream
    val cons : ('a * 'a stream) -> 'a stream
  end
module BasicStream : BASIC_STREAM =
  struct
    type 'a stream =
      | Stream of (unit -> 'a front) 
    and 'a front =
      | Empty 
      | Cons of ('a * 'a stream) 
    let rec delay d = Stream d
    let rec expose (Stream d) = d ()
    let empty = Stream (function | () -> Empty)
    let rec cons (x, s) = Stream (function | () -> Cons (x, s))
  end 
module BasicMemoStream : BASIC_STREAM =
  struct
    type 'a stream =
      | Stream of (unit -> 'a front) 
    and 'a front =
      | Empty 
      | Cons of ('a * 'a stream) 
    exception Uninitialized 
    let rec expose (Stream d) = d ()
    let rec delay d =
      let memo = ref (function | () -> raise Uninitialized) in
      let rec memoFun () =
        try let r = d () in memo := ((function | () -> r)); r
        with | exn -> (memo := ((function | () -> raise exn)); raise exn) in
      memo := memoFun; Stream (function | () -> (!) memo ())
    let empty = Stream (function | () -> Empty)
    let rec cons (x, s) = Stream (function | () -> Cons (x, s))
  end 
module type STREAM  =
  sig
    include BASIC_STREAM
    exception EmptyStream 
    val null : 'a stream -> bool
    val hd : 'a stream -> 'a
    val tl : 'a stream -> 'a stream
    val map : ('a -> 'b) -> 'a stream -> 'b stream
    val filter : ('a -> bool) -> 'a stream -> 'a stream
    val exists : ('a -> bool) -> 'a stream -> bool
    val take : ('a stream * int) -> 'a list
    val drop : ('a stream * int) -> 'a stream
    val fromList : 'a list -> 'a stream
    val toList : 'a stream -> 'a list
    val tabulate : (int -> 'a) -> 'a stream
  end
module Stream(Stream:sig module BasicStream : BASIC_STREAM end) : STREAM =
  struct
    open BasicStream
    exception EmptyStream 
    let rec null s = null' (expose s)
    let rec null' = function | Empty -> true__ | Cons _ -> false__
    let rec hd s = hd' (expose s)
    let rec hd' = function | Empty -> raise EmptyStream | Cons (x, s) -> x
    let rec tl s = tl' (expose s)
    let rec tl' = function | Empty -> raise EmptyStream | Cons (x, s) -> s
    let rec map f s = delay (function | () -> map' f (expose s))
    let rec map' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, Empty) -> Empty
      | (f, Cons (x, s)) -> Cons ((f x), (map f s))
    let rec filter p s = delay (function | () -> filter' p (expose s))
    let rec filter' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, Empty) -> Empty
      | (p, Cons (x, s)) ->
          if p x then Cons (x, (filter p s)) else filter' p (expose s)
    let rec exists p s = exists' p (expose s)
    let rec exists' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (p, Empty) -> false__
      | (p, Cons (x, s)) -> (p x) || (exists p s)
    let rec takePos =
      function | (s, 0) -> nil | (s, n) -> take' ((expose s), n)
    let rec take' =
      function
      | (Empty, _) -> nil
      | (Cons (x, s), n) -> (::) x takePos (s, (n - 1))
    let rec take (s, n) = if n < 0 then raise Subscript else takePos (s, n)
    let rec fromList =
      function | nil -> empty | x::l -> cons (x, (fromList l))
    let rec toList s = toList' (expose s)
    let rec toList' =
      function | Empty -> nil | Cons (x, s) -> (::) x toList s
    let rec dropPos =
      function | (s, 0) -> s | (s, n) -> drop' ((expose s), n)
    let rec drop' =
      function
      | (Empty, _) -> empty
      | (Cons (x, s), n) -> dropPos (s, (n - 1))
    let rec drop (s, n) = if n < 0 then raise Subscript else dropPos (s, n)
    let rec tabulate f = delay (function | () -> tabulate' f)
    let rec tabulate' f =
      Cons ((f 0), (tabulate (function | i -> f (i + 1))))
  end  (* Stream Library *)
(* Author: Frank Pfenning *)
(* BASIC_STREAM defines the visible "core" of streams *)
(* Lazy stream construction and exposure *)
(* Eager stream construction *)
(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
(* STREAM extends BASIC_STREAMS by operations *)
(* definable without reference to the implementation *)
(* functions null, hd, tl, map, filter, exists, take, drop *)
(* parallel the functions in the List structure *)
(* structure Stream :> STREAM --- non-memoizing *)
module Stream : STREAM =
  (Make_Stream)(struct module BasicStream = BasicStream end) 
(* structure MStream :> STREAM --- memoizing *)
module MStream : STREAM =
  (Make_Stream)(struct module BasicStream = BasicMemoStream end) ;;
