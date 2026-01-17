
module type ORDERED_FIELD  =
  sig
    include
      ((FIELD)(* Ordered Field *)(* Author: Roberto Virga *))
    val sign : number -> ((int)(* Sign operations *))
    val abs : number -> number
    val (>) :
      (number * number) ->
        ((bool)(* Comparisons predicates *))
    val (<) : (number * number) -> bool
    val (>=) : (number * number) -> bool
    val (<=) : (number * number) -> bool
    val compare : (number * number) -> order
  end;;
