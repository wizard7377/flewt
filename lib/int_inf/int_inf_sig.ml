
module type INT_INF  =
  sig
    include INTEGER
    val divmod : int -> int -> (int * int)
    val quotrem : int -> int -> (int * int)
    val pow : int -> Int.int -> int
    val log2 : int -> Int.int
  end;;
