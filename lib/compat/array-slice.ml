
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type ARRAY_SLICE  =
  sig
    type nonrec 'a slice
    val slice : ('a Array.array * int * int option) -> 'a slice
    val appi : ((int * 'a) -> unit) -> 'a slice -> unit
  end;;




(* Compatibility shim from Basis-current ArraySlice to Basis-97 Array *)
(* Author: Christopher Richards *)
module ArraySlice : ARRAY_SLICE =
  struct
    type nonrec 'a slice = ('a Array.array * int * int option)
    let rec slice s = s
    let appi = Array.appi
  end ;;
