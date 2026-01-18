
(* Compatibility shim from Basis-current Vector to Basis-97 Vector *)
(* Author: Christopher Richards *)
module CompatVector97 : COMPAT_VECTOR =
  struct
    let rec appi f vec = Vector.appi f (vec, 0, None)
    let rec mapi f vec = Vector.mapi f (vec, 0, None)
  end ;;
