
module type COMPAT_TIMER  =
  sig
    val checkCPUTimer :
      Timer.cpu_timer ->
        <
          usr: ((Time.time)(* Author: Christopher Richards *)(* Compatibility shim to cope with Standard Basis version skew *))
             ;sys: Time.time   > 
    val checkGCTime : Timer.cpu_timer -> Time.time
  end;;
