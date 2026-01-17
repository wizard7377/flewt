
module type RECURSE  =
  sig
    module State :
    ((STATE)(* Recurse: Version 1.4 *)(* Author: Carsten Schuermann *))
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;
