
module CompatTimer97 : COMPAT_TIMER =
  struct
    let rec checkCPUTimer timer =
      let { usr; sys; gc; sys; gc; gc } = Timer.checkCPUTimer timer in
      { usr; sys }
    let rec checkGCTime timer = let { gc } = Timer.checkCPUTimer timer in gc
  end ;;
