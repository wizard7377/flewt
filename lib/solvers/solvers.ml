module CSEqQ =
  (CSEqField)(struct
                     module Field = Rationals
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                   end)
module CSIneqQ =
  (CSIneqField)(struct
                       module OrderedField = Rationals
                       module Trail = Trail
                       module Unify = UnifyTrail
                       module SparseArray = SparseArray
                       module SparseArray2 = SparseArray2
                       module CSEqField = CSEqQ
                       module Compat = Compat
                     end)
module CSEqStrings =
  (CSEqStrings)(struct module Whnf = Whnf
                            module Unify = UnifyTrail end)
module CSEqBools =
  (CSEqBools)(struct module Whnf = Whnf
                          module Unify = UnifyTrail end)
module CSEqZ =
  (CSEqIntegers)(struct
                        module Integers = Integers
                        module Whnf = Whnf
                        module Unify = UnifyTrail
                      end)
module CSIneqZ =
  (CSIneqIntegers)(struct
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
  (CSIntWord)(struct
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
    let _ =
      List.app
        (begin function | s -> (begin CSManager.installSolver s; () end) end)
      solvers
  let version =
    List.foldr
      (begin function | (s, str) -> (((fun r -> r.name) s) ^ "\n") ^ str end)
    "" solvers end
