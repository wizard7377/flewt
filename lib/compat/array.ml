
module type COMPAT_ARRAY  =
  sig
    val appi :
      ((int * 'a) -> unit) ->
        'a Array.array ->
          ((unit)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
  end;;
