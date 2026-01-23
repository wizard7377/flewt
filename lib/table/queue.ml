module type QUEUE  =
  sig
    type nonrec 'a queue
    val empty : 'a queue
    val insert : ('a * 'a queue) -> 'a queue
    val delete : 'a queue -> ('a * 'a queue) option
    val insertFront : ('a * 'a queue) -> 'a queue
    val deleteEnd : 'a queue -> ('a * 'a queue) option
    val toList : 'a queue -> ('a list * 'a queue option)
  end


module Queue : QUEUE =
  struct
    type nonrec 'a queue = ('a list * 'a list)
    let empty = ([], [])
    let rec insert (x, (inp, out)) = ((x :: inp), out)
    let rec delete =
      begin function
      | ([], []) -> None
      | (inp, x::out) -> Some (x, (inp, out))
      | (inp, []) -> delete ([], (List.rev inp)) end
    let rec insertFront (x, (inp, out)) = (inp, (x :: out))
    let rec deleteEnd =
      begin function
      | ([], []) -> None
      | (x::inp, out) -> Some (x, (inp, out))
      | ([], out) -> delete ((List.rev out), []) end
  let rec toList =
    begin function
    | ([], out) -> (out, None)
    | (inp, out) ->
        let out' = out @ List.rev inp in (out', (Some ([], out'))) end end
