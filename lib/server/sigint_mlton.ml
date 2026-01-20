
module SigINT : SIGINT =
  struct
    let rec interruptLoop loop =
      let _ =
        MLton.Cont.callcc
          (fun k ->
             MLton.Signal.setHandler
               (Posix.Signal.int,
                 (MLton.Signal.Handler.handler
                    (fun _ ->
                       MLton.Thread.prepare
                         ((MLton.Thread.new__
                             (fun () -> MLton.Cont.throw (k, ()))), ()))))) in
      ((loop ())(* open MLton *))
  end ;;
