
module MemoTable =
  (Make_HashTable)(struct
                     type nonrec key' = (int * int)
                     let hash n m = (7 * n) + m
                     let eq = (=)
                   end)
module WorldSyn =
  (Make_WorldSyn)(struct
                    module Global = Global
                    module Whnf = Whnf
                    module Names = Names
                    module Unify = UnifyTrail
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Index = Index
                    module Subordinate = Subordinate
                    module Print = Print
                    module Table = IntRedBlackTree
                    module Paths = Paths
                    module Origins = Origins
                    module Timers = Timers
                  end)
module Worldify =
  (Make_Worldify)(struct
                    module Global = Global
                    module WorldSyn = WorldSyn
                    module Whnf = Whnf
                    module Names = Names
                    module Unify = UnifyTrail
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Index = Index
                    module CSManager = CSManager
                    module Subordinate = Subordinate
                    module Print = Print
                    module Table = IntRedBlackTree
                    module MemoTable = MemoTable
                    module IntSet = IntSet
                    module Origins = Origins
                  end);;
