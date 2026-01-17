
module CompatTimer97 : COMPAT_TIMER =
  struct
    let rec checkCPUTimer
      ((timer)(* Compatibility shim from Basis-current Timer to Basis-97 Timer *)
      (* Author: Christopher Richards *)) =
      let { usr; sys; gc; sys; gc; gc } = Timer.checkCPUTimer timer in
      { usr; sys }
    let rec checkGCTime timer = let { gc } = Timer.checkCPUTimer timer in gc
  end ;;
