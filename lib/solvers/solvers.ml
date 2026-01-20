
module CSEqQ =
  (Make_CSEqField)(struct
                     module Field = Rationals
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                   end)
module CSIneqQ =
  (Make_CSIneqField)(struct
                       module OrderedField = Rationals
                       module Trail = Trail
                       module Unify = UnifyTrail
                       module SparseArray = SparseArray
                       module SparseArray2 = SparseArray2
                       module CSEqField = CSEqQ
                       module Compat = Compat
                     end)
module CSEqStrings =
  (Make_CSEqStrings)(struct module Whnf = Whnf
                            module Unify = UnifyTrail end)
module CSEqBools =
  (Make_CSEqBools)(struct module Whnf = Whnf
                          module Unify = UnifyTrail end)
module CSEqZ =
  (Make_CSEqIntegers)(struct
                        module Integers = Integers
                        module Whnf = Whnf
                        module Unify = UnifyTrail
                      end)
module CSIneqZ =
  (Make_CSIneqIntegers)(struct
                          module Integers = Integers
                          module Rationals = Rationals
                          module Trail = Trail
                          module Unify = UnifyTrail
                          module SparseArray = SparseArray
                          module SparseArray2 = SparseArray2
                          module CSEqIntegers = CSEqZ
                          module Compat = Compat
                        end)
module CSIntWord32 =
  (Make_CSIntWord)(struct
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                     let wordSize = 32
                   end)
module type CS_INSTALLER  = sig val version : string end
module CSInstaller : CS_INSTALLER =
  struct
    let solvers =
      [CSEqQ.solver;
      CSIneqQ.solver;
      CSEqStrings.solver;
      CSEqBools.solver;
      CSEqZ.solver;
      CSIneqZ.solver;
      CSIntWord32.solver]
    let _ = List.app (fun s -> CSManager.installSolver s; ()) solvers
    let version =
      List.foldr (fun s -> fun str -> (((fun r -> r.name) s) ^ "\n") ^ str)
        "" solvers
  end ;;
