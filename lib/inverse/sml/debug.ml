module type DEBUG  =
  sig
    exception Assert of exn 
    val enable : unit -> unit
    val disable : unit -> unit
    val enable_assertions : unit -> unit
    val disable_assertions : unit -> unit
    val assert_ : (bool * exn) -> unit
    val enable_printing : unit -> unit
    val disable_printing : unit -> unit
    val print : string -> unit
  end


module Debug : DEBUG =
  struct
    exception Assert of exn 
    let assert' = ref true
    let print' = ref true
    let rec enable () = begin assert' := true; print' := true end
    let rec disable () = begin assert' := true; print' := true end
  let rec enable_assertions () = assert' := true
  let rec disable_assertions () = assert' := false
  let rec enable_printing () = print' := true
  let rec disable_printing () = print' := false
  let rec assert_ (c, exn) =
    if !assert'
    then begin (if c then begin () end else begin raise (Assert exn) end) end
  else begin () end
let rec print s = if !print' then begin TextIO.print (s ^ "\n") end
  else begin () end end
