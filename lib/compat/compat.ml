
(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module type COMPAT  =
  sig
    val inputLine97 : TextIO.instream -> string
    module Array : COMPAT_ARRAY
    module Vector : COMPAT_VECTOR
    module OS : sig module Path : COMPAT_PATH end
    module Substring : COMPAT_SUBSTRING
    module TextIO : COMPAT_TEXT_IO
    module Timer : COMPAT_TIMER
    module SocketIO : COMPAT_SOCKET_IO
  end;;




(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)
module Compat(Compat:sig
                       module Array : COMPAT_ARRAY
                       module Vector : COMPAT_VECTOR
                       module Path : COMPAT_PATH
                       module Substring : COMPAT_SUBSTRING
                       module TextIO : COMPAT_TEXT_IO
                       module Timer : COMPAT_TIMER
                       module SocketIO : COMPAT_SOCKET_IO
                     end) : COMPAT =
  struct
    module Array = Array
    module Vector = Vector
    module OS = struct module Path = Path end
    module Substring = Substring
    module TextIO = TextIO
    module Timer = Timer
    module SocketIO = SocketIO
    let rec inputLine97 instream = getOpt ((TextIO.inputLine instream), "")
  end ;;




(* Compatibility shim from Basis-current to itself *)
(* Author: Christopher Richards *)
module Compat : COMPAT =
  (Make_Compat)(struct
                  module Array = Array
                  module Vector = Vector
                  module Path = OS.Path
                  module Substring = Substring
                  module TextIO = TextIO
                  module Timer = Timer
                  module SocketIO = CompatSocketIO
                end) ;;
