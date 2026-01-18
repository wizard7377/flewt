
(* Global parameters *)
(* Author: Frank Pfenning *)
module type GLOBAL  =
  sig
    val chatter : int ref
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




(* Global parameters *)
(* Author: Frank Pfenning *)
module Global : GLOBAL =
  struct
    let chatter = ref 3
    let style = ref 0
    let maxCid = 19999
    let maxMid = 999
    let maxCSid = 49
    let doubleCheck = ref false__
    let unsafe = ref false__
    let autoFreeze = ref true__
    (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
    let timeLimit = ref (NONE : Time.time option)
    let rec chPrint n s = if (!chatter) >= n then print (s ()) else ()
    let rec chMessage n s f = if (!chatter) >= n then f (s ()) else ()
  end ;;
