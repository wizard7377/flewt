
module type VECTOR_SLICE  =
  sig
    type nonrec 'a slice(* Author: Christopher Richards *)
    (* Compatibility shim to cope with Standard Basis version skew *)
    val slice : ('a Vector.vector * int * int option) -> 'a slice
    val appi : ((int * 'a) -> unit) -> 'a slice -> unit
    val mapi : ((int * 'a) -> 'b) -> 'a slice -> 'b Vector.vector
  end;;




module VectorSlice : VECTOR_SLICE =
  struct
    type nonrec 'a slice =
      ((('a)(* Author: Christopher Richards *)(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *))
        Vector.vector * int * int option)
    let rec slice s = s
    let appi = Vector.appi
    let mapi = Vector.mapi
  end ;;
