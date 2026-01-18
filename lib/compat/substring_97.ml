
(* Compatibility shim from Basis-current Substring to Basis-97 Substring *)
(* Author: Christopher Richards *)
module CompatSubstring97 : COMPAT_SUBSTRING =
  struct let full = Substring.all end ;;
