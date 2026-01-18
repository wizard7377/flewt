
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type COMPAT_SUBSTRING  =
  sig val full : string -> Substring.substring end;;
