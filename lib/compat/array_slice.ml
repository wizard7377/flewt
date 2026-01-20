
module type ARRAY_SLICE  =
  sig
    type nonrec 'a slice
    val slice : 'a Array.array -> int -> int option -> 'a slice
    val appi : (int -> 'a -> unit) -> 'a slice -> unit
  end;;




module ArraySlice : ARRAY_SLICE =
  struct
    type nonrec 'a slice = ('a Array.array * int * int option)
    let rec slice s = s
    let appi = Array.appi
  end ;;
