module SwMachine(SwMachine:sig
                             module Trace : TRACE
                             module AbsMachine : ABSMACHINE
                             module TMachine : ABSMACHINE
                           end) : ABSMACHINE =
  struct
    let rec solve args =
      if Trace.tracing () then begin TMachine.solve args end
      else begin AbsMachine.solve args end end
