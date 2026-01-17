
module type GLOBAL  =
  sig
    val chatter :
      ((int)(* Author: Frank Pfenning *)(* Global parameters *))
        ref
    val style : int ref
    val maxCid : int
    val maxMid : int
    val maxCSid : int
    val doubleCheck : bool ref
    val unsafe : bool ref
    val autoFreeze : bool ref
    val chPrint : int -> (unit -> string) -> unit
    val chMessage : int -> (unit -> string) -> (string -> unit) -> unit
    val timeLimit : Time.time option ref
  end;;




module Global : GLOBAL =
  struct
    let ((chatter)(* Global parameters *)(* Author: Frank Pfenning *))
      = ref 3
    let style = ref 0
    let maxCid = 19999
    let maxMid = 999
    let maxCSid = 49
    let doubleCheck = ref false__
    let unsafe = ref false__
    let autoFreeze = ref true__
    let ((timeLimit)(* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *))
      = ref (NONE : Time.time option)
    let rec chPrint n s = if (!chatter) >= n then print (s ()) else ()
    let rec chMessage n s f = if (!chatter) >= n then f (s ()) else ()
  end ;;
