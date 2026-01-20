
module type COMPAT_SOCKET_IO  =
  sig
    val sendVec :
      ('a, Socket.active Socket.stream) Socket.sock ->
        Word8Vector.vector -> int
  end;;




module CompatSocketIO : COMPAT_SOCKET_IO =
  struct
    let rec sendVec sock vs =
      Socket.sendVec (sock, (Word8VectorSlice.full vs))
  end ;;
