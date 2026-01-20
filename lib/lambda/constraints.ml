
module type CONSTRAINTS  =
  sig
    exception Error of IntSyn.cnstr list 
    val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
    val warnConstraints : string list -> unit
  end;;




module Constraints(Constraints:sig module Conv : CONV end) : CONSTRAINTS =
  struct
    exception Error of IntSyn.cnstr list 
    module I = IntSyn
    let rec simplify =
      function
      | nil -> nil
      | { contents = I.Solved }::cnstrs -> simplify cnstrs
      | ({ contents = Eqn (__G, __U1, __U2) } as Eqn)::cnstrs ->
          if Conv.conv ((__U1, I.id), (__U2, I.id))
          then simplify cnstrs
          else Eqn :: (simplify cnstrs)
      | ({ contents = FgnCnstr csfc } as FgnCnstr)::cnstrs ->
          if I.FgnCnstrStd.Simplify.apply csfc ()
          then simplify cnstrs
          else FgnCnstr :: (simplify cnstrs)
    let rec namesToString =
      function
      | name::nil -> name ^ "."
      | name::names -> (^) (name ^ ", ") namesToString names
    let rec warnConstraints =
      function
      | nil -> ()
      | names ->
          print (((^) "Constraints remain on " namesToString names) ^ "\n")
    let simplify = simplify
    let namesToString = namesToString
    let warnConstraints = warnConstraints
  end ;;
