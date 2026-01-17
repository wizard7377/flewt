
module type COMPAT_SUBSTRING  =
  sig
    val full :
      string ->
        ((Substring.substring)(* Author: Christopher Richards *)
        (* Compatibility shim to cope with Standard Basis version skew *))
  end;;
