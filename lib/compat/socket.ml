
module type COMPAT_SOCKET_IO  =
  sig
    val sendVec :
      (('a, Socket.active Socket.stream) Socket.sock * Word8Vector.vector) ->
        ((int)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
  end;;




module CompatSocketIO : COMPAT_SOCKET_IO =
  struct
    let rec sendVec
      (((sock)(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
       (* Author: Christopher Richards *)), vs)
      = Socket.sendVec (sock, (Word8VectorSlice.full vs))
  end ;;
