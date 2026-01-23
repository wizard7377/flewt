module SigINT : SIGINT =
  struct
    let rec interruptLoop (loop : unit -> unit) =
      let _ =
        MLton.Cont.callcc
          (begin function
           | k ->
               MLton.Signal.setHandler
                 (Posix.Signal.int,
                   (MLton.Signal.Handler.handler
                      (begin function
                       | _ ->
                           MLton.Thread.prepare
                             ((MLton.Thread.new_
                                 (begin function
                                  | () -> MLton.Cont.throw (k, ()) end)), ()) end))) end) in
  ((loop ())(* open MLton *)) end
