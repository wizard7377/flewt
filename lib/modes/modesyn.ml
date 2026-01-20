
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
    val modeEqual : __Mode -> __Mode -> bool
    val modeToString : __Mode -> string
  end
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
    let rec modeEqual __0__ __1__ =
      match (__0__, __1__) with
      | (Plus, Plus) -> true
      | (Star, Star) -> true
      | (Minus, Minus) -> true
      | (Minus1, Minus1) -> true
      | (_, _) -> false
    let rec modeToString =
      function
      | Plus -> "input (+)"
      | Star -> "unrestricted (*)"
      | Minus -> "output (-)"
      | Minus1 -> "unique output (-1)"
  end ;;
