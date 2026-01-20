
module AbsMachine =
  (Make_AbsMachine)(struct
                      module Unify = UnifyTrail
                      module Assign = Assign
                      module Index = Index
                      module CPrint = CPrint
                      module Print = Print
                      module Names = Names
                    end)
module AbstractTabled =
  (Make_AbstractTabled)(struct
                          module Print = Print
                          module Whnf = Whnf
                          module Unify = UnifyTrail
                          module Constraints = Constraints
                          module Subordinate = Subordinate
                          module Conv = Conv
                          module Print = Print
                        end)
module MemoTable =
  (Make_MemoTable)(struct
                     module Conv = Conv
                     module Whnf = Whnf
                     module Print = Print
                     module AbstractTabled = AbstractTabled
                     module Table = IntRedBlackTree
                   end)
module MemoTableInst =
  (Make_MemoTableInst)(struct
                         module Conv = Conv
                         module Whnf = Whnf
                         module Match = Match
                         module Assign = Assign
                         module Print = Print
                         module AbstractTabled = AbstractTabled
                         module Table = IntRedBlackTree
                       end)
module SwMemoTable =
  (Make_SwMemoTable)(struct
                       module MemoTable = MemoTable
                       module MemoTableInst = MemoTableInst
                     end)
module Tabled =
  (Make_Tabled)(struct
                  module Unify = UnifyTrail
                  module Match = Match
                  module TabledSyn = TabledSyn
                  module Assign = Assign
                  module Index = Index
                  module Queue = Queue
                  module MemoTable = SwMemoTable
                  module AbstractTabled = AbstractTabled
                  module CPrint = CPrint
                  module Print = Print
                end)
module PtRecon =
  (Make_PtRecon)(struct
                   module Unify = UnifyTrail
                   module MemoTable = SwMemoTable
                   module Assign = Assign
                   module Index = Index
                   module CPrint = CPrint
                   module Names = Names
                 end)
module Trace =
  (Make_Trace)(struct
                 module Names = Names
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Print = Print
               end)
module AbsMachineSbt =
  (Make_AbsMachineSbt)(struct
                         module IntSyn' = IntSyn
                         module CompSyn' = CompSyn
                         module SubTree = SubTree
                         module Unify = UnifyTrail
                         module Assign = Assign
                         module Index = Index
                         module CPrint = CPrint
                         module Print = Print
                         module Names = Names
                         module CSManager = CSManager
                       end)
module TMachine =
  (Make_TMachine)(struct
                    module Unify = UnifyTrail
                    module Index = Index
                    module Assign = Assign
                    module CPrint = CPrint
                    module Names = Names
                    module Trace = Trace
                  end)
module SwMachine =
  (Make_SwMachine)(struct
                     module Trace = Trace
                     module AbsMachine = AbsMachine
                     module TMachine = TMachine
                   end);;
