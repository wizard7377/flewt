
module type CS  =
  sig
    val solver :
      ((CSManager.solver)(* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
        (*! structure CSManager : CS_MANAGER !*)(* Constraint Solver *))
  end;;
