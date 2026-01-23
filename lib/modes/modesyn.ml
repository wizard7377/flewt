module type MODESYN  =
  sig
    type mode_ =
      | Plus 
      | Star 
      | Minus 
      | Minus1 
    type modeSpine_ =
      | Mnil 
      | Mapp of (marg_ * modeSpine_) 
    and marg_ =
      | Marg of (mode_ * string option) 
    val modeEqual : (mode_ * mode_) -> bool
    val modeToString : mode_ -> string
  end
module ModeSyn : MODESYN =
  struct
    exception Error of string 
    type mode_ =
      | Plus 
      | Star 
      | Minus 
      | Minus1 
    type modeSpine_ =
      | Mnil 
      | Mapp of (marg_ * modeSpine_) 
    and marg_ =
      | Marg of (mode_ * string option) 
    let rec modeEqual =
      begin function
      | (Plus, Plus) -> true
      | (Star, Star) -> true
      | (Minus, Minus) -> true
      | (Minus1, Minus1) -> true
      | (_, _) -> false end
    let rec modeToString =
      begin function
      | Plus -> "input (+)"
      | Star -> "unrestricted (*)"
      | Minus -> "output (-)"
      | Minus1 -> "unique output (-1)" end end
