
(* Compatibility shim from Basis-current to Poly/ML Basis as of 4.1.3 *)
(* Author: Christopher Richards *)
module Compat : COMPAT =
  (Make_Compat)(struct
                  module Array = CompatArray97
                  module Vector = CompatVector97
                  module Path = OS.Path
                  module Substring = CompatSubstring97
                  module TextIO = CompatTextIO97
                  module Timer = Timer
                end) ;;
