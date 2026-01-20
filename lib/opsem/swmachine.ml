
module SwMachine(SwMachine:sig
                             module Trace : TRACE
                             module AbsMachine : ABSMACHINE
                             module TMachine : ABSMACHINE
                           end) : ABSMACHINE =
  struct
    let rec solve args =
      if Trace.tracing () then TMachine.solve args else AbsMachine.solve args
  end ;;
