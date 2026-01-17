
module type COMPAT_PATH  =
  sig
    val mkAbsolute :
      < path: string  ;relativeTo: string   >  ->
        ((string)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
  end;;
