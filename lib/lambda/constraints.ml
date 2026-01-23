module type CONSTRAINTS  =
  sig
    exception Error of IntSyn.cnstr list 
    val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
    val warnConstraints : string list -> unit
  end


module Constraints(Constraints:sig module Conv : CONV end) : CONSTRAINTS =
  struct
    exception Error of IntSyn.cnstr list 
    module I = IntSyn
    let rec simplify =
      begin function
      | [] -> []
      | { contents = I.Solved }::cnstrs -> simplify cnstrs
      | ({ contents = Eqn (g_, u1_, u2_) } as Eqn)::cnstrs ->
          if Conv.conv ((u1_, I.id), (u2_, I.id))
          then begin simplify cnstrs end
          else begin Eqn :: (simplify cnstrs) end
      | ({ contents = FgnCnstr csfc } as FgnCnstr)::cnstrs ->
          if I.FgnCnstrStd.Simplify.apply csfc ()
          then begin simplify cnstrs end
          else begin FgnCnstr :: (simplify cnstrs) end end
let rec namesToString =
  begin function
  | name::[] -> name ^ "."
  | name::names -> (^) (name ^ ", ") namesToString names end
let rec warnConstraints =
  begin function
  | [] -> ()
  | names ->
      print (((^) "Constraints remain on " namesToString names) ^ "\n") end
let simplify = simplify
let namesToString = namesToString
let warnConstraints = warnConstraints end
