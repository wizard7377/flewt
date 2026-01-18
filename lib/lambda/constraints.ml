
(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)
module type CONSTRAINTS  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of IntSyn.cnstr list 
    val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
    val warnConstraints : string list -> unit
  end;;




(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)
module Constraints(Constraints:sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 module Conv : CONV
                               end) : CONSTRAINTS =
  struct
    (*! sharing Conv.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of IntSyn.cnstr list 
    (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)
    module I = IntSyn
    let rec simplify =
      function
      | nil -> nil
      | (ref (I.Solved))::cnstrs -> simplify cnstrs
      | (ref (Eqn (G, U1, U2)) as Eqn)::cnstrs ->
          if Conv.conv ((U1, I.id), (U2, I.id))
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
    (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *)
    let simplify = simplify
    let namesToString = namesToString
    let warnConstraints = warnConstraints
  end ;;
