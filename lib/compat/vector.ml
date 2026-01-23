module type COMPAT_VECTOR  =
  sig
    val appi : ((int * 'a) -> unit) -> 'a Array.t -> unit
    val mapi : ((int * 'a) -> 'b) -> 'a Array.t -> 'b Array.t
  end