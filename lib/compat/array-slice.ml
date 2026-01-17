
module type ARRAY_SLICE  =
  sig
    type nonrec 'a slice(* Author: Christopher Richards *)
    (* Compatibility shim to cope with Standard Basis version skew *)
    val slice : ('a Array.array * int * int option) -> 'a slice
    val appi : ((int * 'a) -> unit) -> 'a slice -> unit
  end;;




module ArraySlice : ARRAY_SLICE =
  struct
    type nonrec 'a slice =
      ((('a)(* Author: Christopher Richards *)(* Compatibility shim from Basis-current ArraySlice to Basis-97 Array *))
        Array.array * int * int option)
    let rec slice s = s
    let appi = Array.appi
  end ;;
