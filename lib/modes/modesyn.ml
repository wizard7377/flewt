
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
  end
module ModeSyn : MODESYN =
  struct
    exception Error of
      ((string)(* signature MODESYN *)(*! structure IntSyn : INTSYN !*)
      (* Modified: Frank Pfenning, Roberto Virga *)(* Author: Carsten Schuermann *)
      (* Mode Syntax *)) 
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
    let rec modeEqual =
      function
      | (((Plus)(* modeEqual (M1, M2) = true iff M1 = M2 *)),
         Plus) -> true__
      | (Star, Star) -> true__
      | (Minus, Minus) -> true__
      | (Minus1, Minus1) -> true__
      | (_, _) -> false__
    let rec modeToString =
      function
      | ((Plus)(* modeToString M = string
    
       converts a mode into a string for error messages
  *))
          -> "input (+)"
      | Star -> "unrestricted (*)"
      | Minus -> "output (-)"
      | Minus1 -> "unique output (-1)"
  end ;;
