
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type VECTOR_SLICE  =
  sig
    type nonrec 'a slice
    val slice : ('a Vector.vector * int * int option) -> 'a slice
    val appi : ((int * 'a) -> unit) -> 'a slice -> unit
    val mapi : ((int * 'a) -> 'b) -> 'a slice -> 'b Vector.vector
  end;;




(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *)
(* Author: Christopher Richards *)
module VectorSlice : VECTOR_SLICE =
  struct
    type nonrec 'a slice = ('a Vector.vector * int * int option)
    let rec slice s = s
    let appi = Vector.appi
    let mapi = Vector.mapi
  end ;;
