
module SwMachine(SwMachine:sig
                             module Trace : TRACE
                             module AbsMachine : ABSMACHINE
                             module TMachine : ABSMACHINE
                           end) : ABSMACHINE =
  struct
    (*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
    (*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
    (*! structure IntSyn = AbsMachine.IntSyn !*)
    (*! structure CompSyn = AbsMachine.CompSyn !*)
    let rec solve args =
      if Trace.tracing () then TMachine.solve args else AbsMachine.solve args
  end ;;
