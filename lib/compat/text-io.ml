
module type COMPAT_TEXT_IO  =
  sig
    val inputLine :
      TextIO.instream ->
        ((string)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
          option
  end;;
