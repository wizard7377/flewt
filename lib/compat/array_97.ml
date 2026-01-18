
(* Compatibility shim from Basis-current Array to Basis-97 Array *)
(* Author: Christopher Richards *)
module CompatArray97 : COMPAT_ARRAY =
  struct let rec appi f arr = Array.appi f (arr, 0, NONE) end ;;
