module type VECTOR_SLICE  =
  sig
    type nonrec 'a slice
    val slice : ('a Array.t * int * int option) -> 'a slice
    val appi : ((int * 'a) -> unit) -> 'a slice -> unit
    val mapi : ((int * 'a) -> 'b) -> 'a slice -> 'b Array.t
  end


module VectorSlice : VECTOR_SLICE =
  struct
    type nonrec 'a slice = ('a Array.t * int * int option)
    let rec slice s = s
    let appi = Vector.appi
    let mapi = Vector.mapi
  end 