
module SwMachine(SwMachine:sig
                             module Trace : TRACE
                             module AbsMachine : ABSMACHINE
                             module TMachine : ABSMACHINE
                           end) : ABSMACHINE =
  struct
    let rec solve
      ((args)(*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
      (*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
      (*! structure IntSyn = AbsMachine.IntSyn !*)(*! structure CompSyn = AbsMachine.CompSyn !*))
      =
      if Trace.tracing () then TMachine.solve args else AbsMachine.solve args
  end ;;
