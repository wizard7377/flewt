
module type CONSTRAINTS  =
  sig
    exception Error of
      ((IntSyn.cnstr)(*! structure IntSyn : INTSYN !*)
      (* Modified: Roberto Virga *)(* Author: Jeff Polakow, Frank Pfenning *)
      (* Manipulating Constraints *)) list 
    val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
    val warnConstraints : string list -> unit
  end;;




module Constraints(Constraints:sig
                                 module Conv :
                                 ((CONV)(* Manipulating Constraints *)
                                 (* Author: Jeff Polakow, Frank Pfenning *)
                                 (* Modified: Roberto Virga *)(*! structure IntSyn' : INTSYN !*))
                               end) : CONSTRAINTS =
  struct
    exception Error of
      ((IntSyn.cnstr)(*! structure IntSyn = IntSyn' !*)
      (*! sharing Conv.IntSyn = IntSyn' !*)) list 
    module I = IntSyn
    let rec simplify =
      function
      | nil -> nil
      | (ref (I.Solved))::cnstrs -> simplify cnstrs
      | (ref (Eqn (g, u1, u2)) as Eqn)::cnstrs ->
          if Conv.conv ((u1, I.id), (u2, I.id))
          then simplify cnstrs
          else Eqn :: (simplify cnstrs)
      | (ref (FgnCnstr csfc) as FgnCnstr)::cnstrs ->
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
    let ((simplify)(*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       g |- s : g'  g' |- X<I> : V
       g |- U : W
       g |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)
      (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where g |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *))
      = simplify
    let namesToString = namesToString
    let warnConstraints = warnConstraints
  end ;;
