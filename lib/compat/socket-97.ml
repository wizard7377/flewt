
module CompatSocketIO97 : COMPAT_SOCKET_IO =
  struct
    let rec sendVec
      (((sock)(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
       (* Author: Christopher Richards *)), vs)
      = Socket.sendVec (sock, { buf = vs; i = 0; sz = NONE })
  end ;;
