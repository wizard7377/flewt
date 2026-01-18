
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type COMPAT_PATH  =
  sig val mkAbsolute : < path: string  ;relativeTo: string   >  -> string end;;
