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
    let empty = Stream (begin function | () -> Empty end)
    let rec cons (x, s) = Stream (begin function | () -> Cons (x, s) end) end

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
      let memo = ref (begin function | () -> raise Uninitialized end) in
    let rec memoFun () =
      begin try
              let r = d () in begin memo := ((begin function | () -> r end));
                r end
      with
      | exn -> (begin memo := ((begin function | () -> raise exn end));
          raise exn end) end in
begin memo := memoFun; Stream (begin function | () -> (!) memo () end) end
let empty = Stream (begin function | () -> Empty end)
let rec cons (x, s) = Stream (begin function | () -> Cons (x, s) end) end 
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
    let rec null' = begin function | Empty -> true | Cons _ -> false end
    let rec hd s = hd' (expose s)
    let rec hd' =
      begin function | Empty -> raise EmptyStream | Cons (x, s) -> x end
  let rec tl s = tl' (expose s)
  let rec tl' =
    begin function | Empty -> raise EmptyStream | Cons (x, s) -> s end
let rec map f s = delay (begin function | () -> map' f (expose s) end)
let rec map' arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, Empty) -> Empty
  | (f, Cons (x, s)) -> Cons ((f x), (map f s)) end
let rec filter p s = delay (begin function | () -> filter' p (expose s) end)
let rec filter' arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (p, Empty) -> Empty
  | (p, Cons (x, s)) -> if p x then begin Cons (x, (filter p s)) end
      else begin filter' p (expose s) end end
let rec exists p s = exists' p (expose s)
let rec exists' arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (p, Empty) -> false
  | (p, Cons (x, s)) -> (p x) || (exists p s) end
let rec takePos =
  begin function | (s, 0) -> [] | (s, n) -> take' ((expose s), n) end
let rec take' =
  begin function
  | (Empty, _) -> []
  | (Cons (x, s), n) -> (::) x takePos (s, (n - 1)) end
let rec take (s, n) = if n < 0 then begin raise Subscript end
  else begin takePos (s, n) end
let rec fromList =
  begin function | [] -> empty | x::l -> cons (x, (fromList l)) end
let rec toList s = toList' (expose s)
let rec toList' =
  begin function | Empty -> [] | Cons (x, s) -> (::) x toList s end
let rec dropPos =
  begin function | (s, 0) -> s | (s, n) -> drop' ((expose s), n) end
let rec drop' =
  begin function
  | (Empty, _) -> empty
  | (Cons (x, s), n) -> dropPos (s, (n - 1)) end
let rec drop (s, n) = if n < 0 then begin raise Subscript end
  else begin dropPos (s, n) end
let rec tabulate f = delay (begin function | () -> tabulate' f end)
let rec tabulate' f =
  Cons ((f 0), (tabulate (begin function | i -> f (i + 1) end))) end 
module Stream : STREAM =
  (Stream)(struct module BasicStream = BasicStream end) 
module MStream : STREAM =
  (Stream)(struct module BasicStream = BasicMemoStream end) 