
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type MONO_ARRAY_SLICE  =
  sig
    type nonrec array
    type nonrec slice
    type nonrec vector
    val slice : (array * int * int option) -> slice
    val vector : slice -> vector
  end;;
