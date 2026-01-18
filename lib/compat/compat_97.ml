
(* Compatibility shim from Basis-current to Basis-97 *)
(* Author: Christopher Richards *)
module Compat : COMPAT =
  (Make_Compat)(struct
                  module Array = CompatArray97
                  module Vector = CompatVector97
                  module Path = CompatPath97
                  module Substring = CompatSubstring97
                  module TextIO = CompatTextIO97
                  module Timer = CompatTimer97
                  module SocketIO = CompatSocketIO97
                end) ;;
