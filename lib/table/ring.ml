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
  end


module Ring : RING =
  struct
    exception Empty 
    type nonrec 'a ring = ('a list * 'a list)
    let rec empty = begin function | ([], []) -> true | _ -> false end
    let rec init l = ([], l)
    let rec insert ((r, l), y) = (r, (y :: l))
    let rec current =
      begin function
      | ([], []) -> raise Empty
      | (_, x::_) -> x
      | (l, []) -> current ([], (List.rev l)) end
  let rec next =
    begin function
    | ([], []) -> raise Empty
    | (r, []) -> next ([], (List.rev r))
    | (r, x::l) -> ((x :: r), l) end
let rec previous =
  begin function
  | ([], []) -> raise Empty
  | ([], l) -> previous ((List.rev l), [])
  | (x::r, l) -> (r, (x :: l)) end
let rec delete =
  begin function
  | ([], []) -> raise Empty
  | (r, []) -> delete ([], (List.rev r))
  | (r, x::l) -> (r, l) end
let rec foldr f i (r, l) = List.fold_right (fun x y -> f (x, y)) (l  @ List.rev r) i
let rec map f (r, l) = ((List.map f r), (List.map f l)) end
