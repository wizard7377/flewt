
module type MODESYN  =
  sig
    type __Mode =
      | Plus 
      | Star 
      | Minus 
      | Minus1 
    type __ModeSpine =
      | Mnil 
      | Mapp of (__Marg * __ModeSpine) 
    and __Marg =
      | Marg of (__Mode * string option) 
    val modeEqual : (__Mode * __Mode) -> bool
    val modeToString : __Mode -> string
  end (* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)
(*! structure IntSyn : INTSYN !*)
(* signature MODESYN *)
module ModeSyn : MODESYN =
  struct
    exception Error of string 
    type __Mode =
      | Plus 
      | Star 
      | Minus 
      | Minus1 
    type __ModeSpine =
      | Mnil 
      | Mapp of (__Marg * __ModeSpine) 
    and __Marg =
      | Marg of (__Mode * string option) 
    (* modeEqual (M1, M2) = true iff M1 = M2 *)
    let rec modeEqual =
      function
      | (Plus, Plus) -> true__
      | (Star, Star) -> true__
      | (Minus, Minus) -> true__
      | (Minus1, Minus1) -> true__
      | (_, _) -> false__
    (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
    let rec modeToString =
      function
      | Plus -> "input (+)"
      | Star -> "unrestricted (*)"
      | Minus -> "output (-)"
      | Minus1 -> "unique output (-1)"
  end ;;
