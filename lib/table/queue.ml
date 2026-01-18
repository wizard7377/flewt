
(* Queues *)
(* Author: Frank Pfenning *)
module type QUEUE  =
  sig
    type nonrec 'a queue
    val empty : 'a queue
    val insert : ('a * 'a queue) -> 'a queue
    val delete : 'a queue -> ('a * 'a queue) option
    val insertFront : ('a * 'a queue) -> 'a queue
    val deleteEnd : 'a queue -> ('a * 'a queue) option
    (* If  toList (q) ==> (l, Some(q')) *)
    (* then q == q' and toList q' is constant time *)
    val toList : 'a queue -> ('a list * 'a queue option)
  end;;




(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)
module Queue : QUEUE =
  struct
    (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
    type nonrec 'a queue = ('a list * 'a list)
    let empty = (nil, nil)
    let rec insert (x, (inp, out)) = ((x :: inp), out)
    let rec delete =
      function
      | (nil, nil) -> None
      | (inp, x::out) -> Some (x, (inp, out))
      | (inp, nil) -> delete (nil, (List.rev inp))
    let rec insertFront (x, (inp, out)) = (inp, (x :: out))
    let rec deleteEnd =
      function
      | (nil, nil) -> None
      | (x::inp, out) -> Some (x, (inp, out))
      | (nil, out) -> delete ((List.rev out), nil)
    (* toList q ==> (l, None)  means q == l and toList is constant time *)
    (* toList q ==> (l, Some(q')) means q == l == q' *)
    (* and toList q' is constant time *)
    let rec toList =
      function
      | (nil, out) -> (out, None)
      | (inp, out) ->
          let out' = (@) out List.rev inp in (out', (Some (nil, out')))
  end ;;
