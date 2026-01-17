
module type COMPAT_VECTOR  =
  sig
    val appi :
      ((int * 'a) -> unit) ->
        'a Vector.vector ->
          ((unit)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
    val mapi : ((int * 'a) -> 'b) -> 'a Vector.vector -> 'b Vector.vector
  end;;
