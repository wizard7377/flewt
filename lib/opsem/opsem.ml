
module AbsMachine =
  (Make_AbsMachine)(struct
                      module Unify =
                        ((UnifyTrail)(*! structure IntSyn' = IntSyn !*)
                        (*! structure CompSyn' = CompSyn !*))
                      module Assign = Assign
                      module Index = Index
                      module CPrint = CPrint
                      module Print = Print
                      module Names = Names
                    end)
module AbstractTabled =
  (Make_AbstractTabled)(struct
                          module Print =
                            ((Print)(*! structure CSManager = CSManager !*)
                            (*! structure IntSyn' = IntSyn !*))
                          module Whnf = Whnf
                          module Unify = UnifyTrail
                          module Constraints = Constraints
                          module Subordinate = Subordinate
                          module Conv =
                            ((Conv)(*! structure TableParam = TableParam !*))
                          module Print = Print
                        end)
module MemoTable =
  (Make_MemoTable)(struct
                     module Conv =
                       ((Conv)(*! structure IntSyn' = IntSyn !*)
                       (*! structure CompSyn' = CompSyn !*))
                     module Whnf = Whnf
                     module Print = Print
                     module AbstractTabled =
                       ((AbstractTabled)(*! structure TableParam = TableParam !*))
                     module Table = IntRedBlackTree
                   end)
module MemoTableInst =
  (Make_MemoTableInst)(struct
                         module Conv =
                           ((Conv)(*! structure RBSet = RBSet!*)
                           (*! structure IntSyn' = IntSyn !*)(*! structure CompSyn' = CompSyn !*))
                         module Whnf = Whnf
                         module Match = Match
                         module Assign = Assign
                         module Print = Print
                         module AbstractTabled =
                           ((AbstractTabled)(*! structure TableParam = TableParam !*))
                         module Table = IntRedBlackTree
                       end)
module SwMemoTable =
  (Make_SwMemoTable)(struct
                       module MemoTable =
                         ((MemoTable)(*! structure RBSet = RBSet!*)
                         (*! structure TableParam = TableParam !*))
                       module MemoTableInst = MemoTableInst
                     end)
module Tabled =
  (Make_Tabled)(struct
                  module Unify =
                    ((UnifyTrail)(*! structure IntSyn' = IntSyn !*)
                    (*! structure CompSyn' = CompSyn !*))
                  module Match = Match
                  module TabledSyn = TabledSyn
                  module Assign = Assign
                  module Index = Index
                  module Queue = Queue
                  module MemoTable =
                    ((SwMemoTable)(*! structure TableParam = TableParam !*)
                    (*	  structure MemoTable = MemoTable    *))
                  module AbstractTabled = AbstractTabled
                  module CPrint = CPrint
                  module Print = Print
                end)
module PtRecon =
  (Make_PtRecon)(struct
                   module Unify =
                     ((UnifyTrail)(*	  structure Names = Names*)
                     (*! structure CSManager = CSManager !*)
                     (*	  structure Subordinate = Subordinate*)
                     (*! structure IntSyn' = IntSyn !*)
                     (*! structure CompSyn' = CompSyn !*))
                   module MemoTable =
                     ((SwMemoTable)(*! structure TableParam = TableParam !*))
                   module Assign = Assign
                   module Index = Index
                   module CPrint = CPrint
                   module Names = Names
                 end)
module Trace =
  (Make_Trace)(struct
                 module Names =
                   ((Names)(*! structure CSManager = CSManager !*)
                   (*! structure IntSyn' = IntSyn !*))
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
                    module Unify =
                      ((UnifyTrail)(*! structure IntSyn' = IntSyn !*)
                      (*! structure CompSyn' = CompSyn !*))
                    module Index = Index
                    module Assign = Assign
                    module CPrint = CPrint
                    module Names = Names
                    module Trace = Trace
                  end)
module SwMachine =
  (Make_SwMachine)(struct
                     module Trace =
                       ((Trace)(*! structure CSManager = CSManager !*))
                     module AbsMachine = AbsMachine
                     module TMachine = TMachine
                   end);;
