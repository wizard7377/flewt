
module type FIELD  =
  sig
    val name :
      ((string)(* Name of the set *)(* Author: Roberto Virga *)
        (* Field *))
    type nonrec number(* Main type *)
    exception Div (* Non-invertible element *)
    val zero : ((number)(* Constants *))
    val one : number
    val (~) : number -> ((number)(* Operators *))
    val (+) : (number * number) -> number
    val (-) : (number * number) -> number
    val ( * ) : (number * number) -> number
    val inverse : number -> number
    val fromInt :
      int ->
        ((number)(* Conversions *)(* raises Div *))
    val fromString : string -> number option
    val toString : number -> string
  end;;
