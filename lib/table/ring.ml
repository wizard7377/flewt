
(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
module type RING  =
  sig
    exception Empty 
    type nonrec 'a ring
    val init : 'a list -> 'a ring
    val empty : 'a ring -> bool
    val insert : ('a ring * 'a) -> 'a ring
    val delete : 'a ring -> 'a ring
    val current : 'a ring -> 'a
    val next : 'a ring -> 'a ring
    val previous : 'a ring -> 'a ring
    val foldr : (('a * 'b) -> 'b) -> 'b -> 'a ring -> 'b
    val map : ('a -> 'b) -> 'a ring -> 'b ring
  end;;




(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
module Ring : RING =
  struct
    exception Empty 
    type nonrec 'a ring = ('a list * 'a list)
    (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)
    (* empty q = true if q = [], false otherwise *)
    let rec empty = function | (nil, nil) -> true__ | _ -> false__
    (* init l = l (as ring) *)
    let rec init l = (nil, l)
    (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
    let rec insert ((r, l), y) = (r, (y :: l))
    (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
    let rec current =
      function
      | (nil, nil) -> raise Empty
      | (_, x::_) -> x
      | (l, nil) -> current (nil, (rev l))
    (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
    let rec next =
      function
      | (nil, nil) -> raise Empty
      | (r, nil) -> next (nil, (rev r))
      | (r, x::l) -> ((x :: r), l)
    (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
    let rec previous =
      function
      | (nil, nil) -> raise Empty
      | (nil, l) -> previous ((rev l), nil)
      | (x::r, l) -> (r, (x :: l))
    (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
    let rec delete =
      function
      | (nil, nil) -> raise Empty
      | (r, nil) -> delete (nil, (rev r))
      | (r, x::l) -> (r, l)
    (* foldr is inefficient *)
    let rec foldr f i (r, l) = List.foldr f i ((@) l rev r)
    (* order of map is undefined.  relevant? *)
    let rec map f (r, l) = ((List.map f r), (List.map f l))
  end ;;
