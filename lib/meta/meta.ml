
module MTPGlobal =
  (Make_MTPGlobal)(struct module MetaGlobal = MetaGlobal end)
module StateSyn =
  (Make_StateSyn)(struct module Whnf = Whnf
                         module Conv = Conv end)
module FunNames =
  (Make_FunNames)(struct
                    module Global = Global
                    module HashTable = StringHashTable
                  end)
module FunPrint =
  (Make_FunPrint)(struct
                    module Formatter = Formatter
                    module Print = Print
                    module Names = Names
                  end)
module Weaken = (Make_Weaken)(struct module Whnf = Whnf end)
module FunWeaken = (Make_FunWeaken)(struct module Weaken = Weaken end)
module FunTypeCheck =
  (Make_FunTypeCheck)(struct
                        module StateSyn' = StateSyn
                        module Abstract = Abstract
                        module TypeCheck = TypeCheck
                        module Conv = Conv
                        module Weaken = Weaken
                        module Subordinate = Subordinate
                        module Whnf = Whnf
                        module Print = Print
                        module FunPrint = FunPrint
                      end)
module RelFun =
  (Make_RelFun)(struct
                  module Global = Global
                  module ModeTable = ModeTable
                  module Names = Names
                  module TypeCheck = TypeCheck
                  module Trail = Trail
                  module Unify = UnifyTrail
                  module Whnf = Whnf
                  module Print = Print
                  module Weaken = Weaken
                  module FunWeaken = FunWeaken
                  module FunNames = FunNames
                end)
module MTPData = (Make_MTPData)(struct module MTPGlobal = MTPGlobal end)
module MTPAbstract =
  (Make_MTPAbstract)(struct
                       module StateSyn' = StateSyn
                       module Whnf = Whnf
                       module Constraints = Constraints
                       module Unify = UnifyTrail
                       module Subordinate = Subordinate
                       module TypeCheck = TypeCheck
                       module FunTypeCheck = FunTypeCheck
                       module Abstract = Abstract
                     end)
module MTPInit =
  (Make_MTPInit)(struct
                   module MTPGlobal = MTPGlobal
                   module Names = Names
                   module StateSyn' = StateSyn
                   module MTPData = MTPData
                   module Formatter = Formatter
                   module Whnf = Whnf
                   module Print = Print
                   module FunPrint = FunPrint
                 end)
module MTPrint =
  (Make_MTPrint)(struct
                   module Global = Global
                   module Names = Names
                   module StateSyn' = StateSyn
                   module Formatter' = Formatter
                   module Print = Print
                   module FunPrint = FunPrint
                 end)
module MTPSearch =
  (Make_MTPSearch)(struct
                     module Global = Global
                     module MTPGlobal = MTPGlobal
                     module Abstract = Abstract
                     module Conv = Conv
                     module StateSyn' = StateSyn
                     module Compile = Compile
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                     module Index = IndexSkolem
                     module Assign = Assign
                     module CPrint = CPrint
                     module Print = Print
                     module Names = Names
                   end)
module MTPFilling =
  (Make_MTPFilling)(struct
                      module MTPGlobal = MTPGlobal
                      module StateSyn' = StateSyn
                      module MTPData = MTPData
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module TypeCheck = TypeCheck
                      module Search = MTPSearch
                      module Whnf = Whnf
                    end)
module MTPSplitting =
  (Make_MTPSplitting)(struct
                        module MTPGlobal = MTPGlobal
                        module Global = Global
                        module StateSyn' = StateSyn
                        module Heuristic = Heuristic
                        module MTPrint = MTPrint
                        module MTPAbstract = MTPAbstract
                        module Names = Names
                        module Conv = Conv
                        module Whnf = Whnf
                        module TypeCheck = TypeCheck
                        module Subordinate = Subordinate
                        module FunTypeCheck = FunTypeCheck
                        module Index = Index
                        module Print = Print
                        module Unify = UnifyTrail
                      end)
module UniqueSearch =
  (Make_UniqueSearch)(struct
                        module Global = Global
                        module StateSyn' = StateSyn
                        module Abstract = Abstract
                        module MTPGlobal = MTPGlobal
                        module Whnf = Whnf
                        module Unify = UnifyTrail
                        module Assign = Assign
                        module Index = Index
                        module Compile = Compile
                        module CPrint = CPrint
                        module Print = Print
                        module Names = Names
                      end)
module Inference =
  (Make_Inference)(struct
                     module MTPGlobal = MTPGlobal
                     module StateSyn' = StateSyn
                     module Abstract = Abstract
                     module TypeCheck = TypeCheck
                     module FunTypeCheck = FunTypeCheck
                     module UniqueSearch = UniqueSearch
                     module Whnf = Whnf
                     module Print = Print
                   end)
module MTPRecursion =
  (Make_MTPRecursion)(struct
                        module MTPGlobal = MTPGlobal
                        module Global = Global
                        module StateSyn' = StateSyn
                        module FunTypeCheck = FunTypeCheck
                        module MTPSearch = MTPSearch
                        module Abstract = Abstract
                        module MTPAbstract = MTPAbstract
                        module Whnf = Whnf
                        module Unify = UnifyTrail
                        module Conv = Conv
                        module Names = Names
                        module Subordinate = Subordinate
                        module MTPrint = MTPrint
                        module Print = Print
                        module TypeCheck = TypeCheck
                        module FunPrint = FunPrint
                        module Formatter = Formatter
                      end)
module MTPStrategy =
  (Make_MTPStrategy)(struct
                       module MTPGlobal = MTPGlobal
                       module StateSyn' = StateSyn
                       module MTPrint = MTPrint
                       module MTPData = MTPData
                       module MTPFilling = MTPFilling
                       module MTPSplitting = MTPSplitting
                       module MTPRecursion = MTPRecursion
                       module Inference = Inference
                       module Timers = Timers
                     end)
module MTProver =
  (Make_MTProver)(struct
                    module MTPGlobal = MTPGlobal
                    module StateSyn = StateSyn
                    module Order = Order
                    module MTPrint = MTPrint
                    module MTPInit = MTPInit
                    module MTPStrategy = MTPStrategy
                    module RelFun = RelFun
                  end)
module CombiProver =
  (Make_CombiProver)(struct
                       module MTPGlobal = MTPGlobal
                       module ProverNew = MTProver
                       module ProverOld = Prover
                     end)
module MTPi =
  (Make_MTPi)(struct
                module MTPGlobal = MTPGlobal
                module StateSyn' = StateSyn
                module FunTypeCheck = FunTypeCheck
                module RelFun = RelFun
                module Formatter = Formatter
                module Print = Print
                module MTPrint = MTPrint
                module MTPInit = MTPInit
                module MTPFilling = MTPFilling
                module MTPData = MTPData
                module MTPSplitting = MTPSplitting
                module MTPRecursion = MTPRecursion
                module Inference = Inference
                module MTPStrategy = MTPStrategy
                module Names = Names
                module Order = Order
                module Timers = Timers
                module Ring = Ring
              end);;
