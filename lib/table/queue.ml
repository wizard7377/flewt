
module type QUEUE  =
  sig
    type nonrec 'a queue(* Author: Frank Pfenning *)
    (* Queues *)
    val empty : 'a queue
    val insert : ('a * 'a queue) -> 'a queue
    val delete : 'a queue -> ('a * 'a queue) option
    val insertFront : ('a * 'a queue) -> 'a queue
    val deleteEnd : 'a queue -> ('a * 'a queue) option
    val toList :
      'a queue ->
        ((('a)(* then q == q' and toList q' is constant time *)(* If  toList (q) ==> (l, SOME(q')) *))
          list * 'a queue option)
  end;;




module Queue : QUEUE =
  struct
    type nonrec 'a queue =
      ((('a)(* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
        (*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)
        (* Standard functional implementation of queues *)
        (* Author: Frank Pfenning *)(* Queues *))
        list * 'a list)
    let empty = (nil, nil)
    let rec insert (x, (inp, out)) = ((x :: inp), out)
    let rec delete =
      function
      | (nil, nil) -> NONE
      | (inp, x::out) -> SOME (x, (inp, out))
      | (inp, nil) -> delete (nil, (List.rev inp))
    let rec insertFront (x, (inp, out)) = (inp, (x :: out))
    let rec deleteEnd =
      function
      | (nil, nil) -> NONE
      | (x::inp, out) -> SOME (x, (inp, out))
      | (nil, out) -> delete ((List.rev out), nil)
    let rec toList =
      function
      | (((nil)(* toList q ==> (l, NONE)  means q == l and toList is constant time *)
         (* toList q ==> (l, SOME(q')) means q == l == q' *)
         (* and toList q' is constant time *)), out) ->
          (out, NONE)
      | (inp, out) ->
          let out' = (@) out List.rev inp in (out', (SOME (nil, out')))
  end ;;
