module type TYPECHECK  =
  sig
    val check_signat : (Syntax.const * Syntax.dec) list -> unit
    val check_signat_clear : (Syntax.const * Syntax.dec) list -> unit
  end


module Typecheck = struct module EE = TypecheckEE end