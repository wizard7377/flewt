
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type COMPAT_SOCKET_IO  =
  sig
    val sendVec :
      (('a, Socket.active Socket.stream) Socket.sock * Word8Vector.vector) ->
        int
  end;;




(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
(* Author: Christopher Richards *)
module CompatSocketIO : COMPAT_SOCKET_IO =
  struct
    let rec sendVec (sock, vs) =
      Socket.sendVec (sock, (Word8VectorSlice.full vs))
  end ;;
