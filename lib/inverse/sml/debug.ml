
module type DEBUG  =
  sig
    exception Assert of exn 
    val enable : unit -> unit
    val disable : unit -> unit
    val enable_assertions : unit -> unit
    val disable_assertions : unit -> unit
    val assert__ : bool -> exn -> unit
    val enable_printing : unit -> unit
    val disable_printing : unit -> unit
    val print : string -> unit
  end;;




module Debug : DEBUG =
  struct
    exception Assert of exn 
    let assert' = ref true
    let print' = ref true
    let rec enable () = assert' := true; print' := true
    let rec disable () = assert' := true; print' := true
    let rec enable_assertions () = assert' := true
    let rec disable_assertions () = assert' := false
    let rec enable_printing () = print' := true
    let rec disable_printing () = print' := false
    let rec assert__ c exn =
      if !assert' then (if c then () else raise (Assert exn)) else ()
    let rec print s = if !print' then TextIO.print (s ^ "\n") else ()
  end ;;
