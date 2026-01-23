module type ORDERED_FIELD  =
  sig
    include FIELD
    val sign : number -> int
    val abs : number -> number
    val (>) : (number * number) -> bool
    val (<) : (number * number) -> bool
    val (>=) : (number * number) -> bool
    val (<=) : (number * number) -> bool
    val compare : (number * number) -> order
  end