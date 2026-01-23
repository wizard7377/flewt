module type COMPAT_TIMER  =
  sig
    val checkCPUTimer :
      Timer.cpu_timer -> < usr: Time.time  ;sys: Time.time   > 
    val checkGCTime : Timer.cpu_timer -> Time.time
  end