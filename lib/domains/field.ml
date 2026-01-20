
module type FIELD  =
  sig
    val name : string
    type nonrec number
    exception Div 
    val zero : number
    val one : number
    val (~) : number -> number
    val (+) : number -> number -> number
    val (-) : number -> number -> number
    val ( * ) : number -> number -> number
    val inverse : number -> number
    val fromInt : int -> number
    val fromString : string -> number option
    val toString : number -> string
  end;;
