module type TRAIL  =
  sig
    type nonrec 'a trail
    val trail : unit -> 'a trail
    val suspend : ('a trail * ('a -> 'b)) -> 'b trail
    val resume : ('b trail * 'a trail * ('b -> 'a)) -> unit
    val reset : 'a trail -> unit
    val mark : 'a trail -> unit
    val unwind : ('a trail * ('a -> unit)) -> unit
    val log : ('a trail * 'a) -> unit
  end


module Trail : TRAIL =
  struct
    type 'a trail_ =
      | Cons of ('a * 'a trail_) 
      | Mark of 'a trail_ 
      | Nil 
    type nonrec 'a trail = 'a trail_ ref
    let rec trail () = ref Nil
    let rec reset trail = trail := Nil
    let rec suspend (trail, copy) =
      let rec suspend' =
        begin function
        | Nil -> Nil
        | Mark trail -> suspend' trail
        | Cons (action, trail) -> Cons ((copy action), (suspend' trail)) end
      (*	  | suspend' (Mark trail) = (Mark (suspend' trail))*) in
    let ftrail = suspend' !trail in ref ftrail
    let rec resume (ftrail, trail, reset) =
      let rec resume' =
        begin function
        | Nil -> Nil
        | Mark ftrail -> resume' ftrail
        | Cons (faction, ftrail) -> Cons ((reset faction), (resume' ftrail)) end
      (*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *) in
    let trail' = resume' !ftrail in trail := trail'
  let rec mark trail = trail := Mark !trail
  let rec unwind (trail, undo) =
    let rec unwind' =
      begin function
      | Nil -> Nil
      | Mark trail -> trail
      | Cons (action, trail) -> (begin undo action; unwind' trail end) end in
  trail := unwind' !trail
let rec log (trail, action) = trail := Cons (action, !trail)

let trail = trail
let suspend = suspend
let resume = resume
let reset = reset
let mark = mark
let unwind = unwind
let log = log end
