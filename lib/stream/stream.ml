
module type BASIC_STREAM  =
  sig
    type nonrec 'a stream
    type 'a front =
      | Empty 
      | Cons of ('a * 'a stream) 
    val delay : (unit -> 'a front) -> 'a stream
    val expose : 'a stream -> 'a front
    val empty : 'a stream
    val cons : 'a -> 'a stream -> 'a stream
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
    let empty = Stream (fun () -> Empty)
    let rec cons x s = Stream (fun () -> Cons (x, s))
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
      let memo = ref (fun () -> raise Uninitialized) in
      let rec memoFun () =
        try let r = d () in memo := ((fun () -> r)); r
        with | exn -> (memo := ((fun () -> raise exn)); raise exn) in
      memo := memoFun; Stream (fun () -> (!) memo ())
    let empty = Stream (fun () -> Empty)
    let rec cons x s = Stream (fun () -> Cons (x, s))
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
    val take : 'a stream -> int -> 'a list
    val drop : 'a stream -> int -> 'a stream
    val fromList : 'a list -> 'a stream
    val toList : 'a stream -> 'a list
    val tabulate : (int -> 'a) -> 'a stream
  end
module Stream(Stream:sig module BasicStream : BASIC_STREAM end) : STREAM =
  struct
    open BasicStream
    exception EmptyStream 
    let rec null s = null' (expose s)
    let rec null' = function | Empty -> true | Cons _ -> false
    let rec hd s = hd' (expose s)
    let rec hd' = function | Empty -> raise EmptyStream | Cons (x, s) -> x
    let rec tl s = tl' (expose s)
    let rec tl' = function | Empty -> raise EmptyStream | Cons (x, s) -> s
    let rec map f s = delay (fun () -> map' f (expose s))
    let rec map' __0__ __1__ =
      match (__0__, __1__) with
      | (f, Empty) -> Empty
      | (f, Cons (x, s)) -> Cons ((f x), (map f s))
    let rec filter p s = delay (fun () -> filter' p (expose s))
    let rec filter' __2__ __3__ =
      match (__2__, __3__) with
      | (p, Empty) -> Empty
      | (p, Cons (x, s)) ->
          if p x then Cons (x, (filter p s)) else filter' p (expose s)
    let rec exists p s = exists' p (expose s)
    let rec exists' __4__ __5__ =
      match (__4__, __5__) with
      | (p, Empty) -> false
      | (p, Cons (x, s)) -> (p x) || (exists p s)
    let rec takePos __6__ __7__ =
      match (__6__, __7__) with
      | (s, 0) -> nil
      | (s, n) -> take' ((expose s), n)
    let rec take' __8__ __9__ =
      match (__8__, __9__) with
      | (Empty, _) -> nil
      | (Cons (x, s), n) -> (::) x takePos (s, (n - 1))
    let rec take s n = if n < 0 then raise Subscript else takePos (s, n)
    let rec fromList =
      function | nil -> empty | x::l -> cons (x, (fromList l))
    let rec toList s = toList' (expose s)
    let rec toList' =
      function | Empty -> nil | Cons (x, s) -> (::) x toList s
    let rec dropPos __10__ __11__ =
      match (__10__, __11__) with
      | (s, 0) -> s
      | (s, n) -> drop' ((expose s), n)
    let rec drop' __12__ __13__ =
      match (__12__, __13__) with
      | (Empty, _) -> empty
      | (Cons (x, s), n) -> dropPos (s, (n - 1))
    let rec drop s n = if n < 0 then raise Subscript else dropPos (s, n)
    let rec tabulate f = delay (fun () -> tabulate' f)
    let rec tabulate' f = Cons ((f 0), (tabulate (fun i -> f (i + 1))))
  end 
module Stream : STREAM =
  (Make_Stream)(struct module BasicStream = BasicStream end) 
module MStream : STREAM =
  (Make_Stream)(struct module BasicStream = BasicMemoStream end) ;;
