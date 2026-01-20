
module type QUEUE  =
  sig
    type nonrec 'a queue
    val empty : 'a queue
    val insert : 'a -> 'a queue -> 'a queue
    val delete : 'a queue -> ('a * 'a queue) option
    val insertFront : 'a -> 'a queue -> 'a queue
    val deleteEnd : 'a queue -> ('a * 'a queue) option
    val toList : 'a queue -> ('a list * 'a queue option)
  end;;




module Queue : QUEUE =
  struct
    type nonrec 'a queue = ('a list * 'a list)
    let empty = (nil, nil)
    let rec insert x (inp, out) = ((x :: inp), out)
    let rec delete __0__ __1__ =
      match (__0__, __1__) with
      | (nil, nil) -> NONE
      | (inp, x::out) -> Some (x, (inp, out))
      | (inp, nil) -> delete (nil, (List.rev inp))
    let rec insertFront x (inp, out) = (inp, (x :: out))
    let rec deleteEnd __2__ __3__ =
      match (__2__, __3__) with
      | (nil, nil) -> NONE
      | (x::inp, out) -> Some (x, (inp, out))
      | (nil, out) -> delete ((List.rev out), nil)
    let rec toList __4__ __5__ =
      match (__4__, __5__) with
      | (nil, out) -> (out, NONE)
      | (inp, out) ->
          let out' = (@) out List.rev inp in (out', (Some (nil, out')))
  end ;;
