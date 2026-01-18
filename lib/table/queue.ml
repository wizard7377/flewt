
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
    (* If  toList (q) ==> (l, SOME(q')) *)
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
      | (nil, nil) -> NONE
      | (inp, x::out) -> SOME (x, (inp, out))
      | (inp, nil) -> delete (nil, (List.rev inp))
    let rec insertFront (x, (inp, out)) = (inp, (x :: out))
    let rec deleteEnd =
      function
      | (nil, nil) -> NONE
      | (x::inp, out) -> SOME (x, (inp, out))
      | (nil, out) -> delete ((List.rev out), nil)
    (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
    (* toList q ==> (l, SOME(q')) means q == l == q' *)
    (* and toList q' is constant time *)
    let rec toList =
      function
      | (nil, out) -> (out, NONE)
      | (inp, out) ->
          let out' = (@) out List.rev inp in (out', (SOME (nil, out')))
  end ;;
