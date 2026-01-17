
module CompatArray97 : COMPAT_ARRAY =
  struct
    let rec appi
      ((f)(* Compatibility shim from Basis-current Array to Basis-97 Array *)
      (* Author: Christopher Richards *)) arr =
      Array.appi f (arr, 0, NONE)
  end ;;
