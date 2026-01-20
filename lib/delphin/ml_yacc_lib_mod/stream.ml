
module Streamm : STREAMM =
  struct
    type 'a str =
      | EVAL of ('a * 'a str ref) 
      | UNEVAL of (unit -> 'a) 
    type nonrec 'a stream = 'a str ref
    let rec get =
      function
      | { contents = EVAL t } -> t
      | { contents = UNEVAL f } as s ->
          let t = ((f ()), (ref (UNEVAL f))) in ((:=) s EVAL t; t)
    let rec streamify f = ref (UNEVAL f)
    let rec cons a s = ref (EVAL (a, s))
  end ;;
