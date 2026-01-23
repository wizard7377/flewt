module Streamm : STREAMM =
  struct
    type 'a str =
      | EVAL of ('a * 'a str ref) 
      | UNEVAL of (unit -> 'a) 
    type nonrec 'a stream = 'a str ref
    let rec get =
      begin function
      | { contents = EVAL t } -> t
      | { contents = UNEVAL f } as s ->
          let t = ((f ()), (ref (UNEVAL f))) in (begin (:=) s EVAL t; t end) end
  let rec streamify f = ref (UNEVAL f)
  let rec cons (a, s) = ref (EVAL (a, s)) end
