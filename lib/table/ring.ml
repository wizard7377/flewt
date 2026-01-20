
module type RING  =
  sig
    exception Empty 
    type nonrec 'a ring
    val init : 'a list -> 'a ring
    val empty : 'a ring -> bool
    val insert : 'a ring -> 'a -> 'a ring
    val delete : 'a ring -> 'a ring
    val current : 'a ring -> 'a
    val next : 'a ring -> 'a ring
    val previous : 'a ring -> 'a ring
    val foldr : ('a -> 'b -> 'b) -> 'b -> 'a ring -> 'b
    val map : ('a -> 'b) -> 'a ring -> 'b ring
  end;;




module Ring : RING =
  struct
    exception Empty 
    type nonrec 'a ring = ('a list * 'a list)
    let rec empty __0__ __1__ =
      match (__0__, __1__) with | (nil, nil) -> true__ | _ -> false__
    let rec init l = (nil, l)
    let rec insert (r, l) y = (r, (y :: l))
    let rec current __2__ __3__ =
      match (__2__, __3__) with
      | (nil, nil) -> raise Empty
      | (_, x::_) -> x
      | (l, nil) -> current (nil, (rev l))
    let rec next __4__ __5__ =
      match (__4__, __5__) with
      | (nil, nil) -> raise Empty
      | (r, nil) -> next (nil, (rev r))
      | (r, x::l) -> ((x :: r), l)
    let rec previous __6__ __7__ =
      match (__6__, __7__) with
      | (nil, nil) -> raise Empty
      | (nil, l) -> previous ((rev l), nil)
      | (x::r, l) -> (r, (x :: l))
    let rec delete __8__ __9__ =
      match (__8__, __9__) with
      | (nil, nil) -> raise Empty
      | (r, nil) -> delete (nil, (rev r))
      | (r, x::l) -> (r, l)
    let rec foldr f i r l = List.foldr f i ((@) l rev r)
    let rec map f r l = ((List.map f r), (List.map f l))
  end ;;
