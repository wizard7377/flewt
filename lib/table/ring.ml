
module type RING  =
  sig
    exception Empty (* Author: Carsten Schuermann *)
    (* Rings (aka cyclic lists) *)
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




module Ring : RING =
  struct
    exception Empty (* Author: Carsten Schuermann *)
    (* Rings (aka cyclic lists) *)
    type nonrec 'a ring = ('a list * 'a list)
    let rec empty =
      function
      | (((nil)(* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)
         (* empty q = true if q = [], false otherwise *)),
         nil) -> true__
      | _ -> false__
    let rec init ((l)(* init l = l (as ring) *)) = (nil, l)
    let rec insert
      ((((r)(* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)),
        l),
       y)
      = (r, (y :: l))
    let rec current =
      function
      | (((nil)(* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)),
         nil) -> raise Empty
      | (_, x::_) -> x
      | (l, nil) -> current (nil, (rev l))
    let rec next =
      function
      | (((nil)(* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)),
         nil) -> raise Empty
      | (r, nil) -> next (nil, (rev r))
      | (r, x::l) -> ((x :: r), l)
    let rec previous =
      function
      | (((nil)(* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)),
         nil) -> raise Empty
      | (nil, l) -> previous ((rev l), nil)
      | (x::r, l) -> (r, (x :: l))
    let rec delete =
      function
      | (((nil)(* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)),
         nil) -> raise Empty
      | (r, nil) -> delete (nil, (rev r))
      | (r, x::l) -> (r, l)
    let rec foldr ((f)(* foldr is inefficient *)) i 
      (r, l) = List.foldr f i ((@) l rev r)
    let rec map
      ((f)(* order of map is undefined.  relevant? *))
      (r, l) = ((List.map f r), (List.map f l))
  end ;;
