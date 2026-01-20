
module CompatSocketIO97 : COMPAT_SOCKET_IO =
  struct
    let rec sendVec sock vs =
      Socket.sendVec (sock, { buf = vs; i = 0; sz = NONE })
  end ;;
