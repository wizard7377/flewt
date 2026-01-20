
module State =
  (Make_State)(struct
                 module WorldSyn' = WorldSyn
                 module Formatter = Formatter
               end)
module Introduce =
  (Make_Introduce)(struct
                     module TomegaNames = TomegaNames
                     module State' = State
                   end)
module Elim =
  (Make_Elim)(struct
                module Data = Data
                module State' = State
                module Whnf = Whnf
                module Abstract = Abstract
                module Unify = UnifyTrail
                module Constraints = Constraints
                module Index = Index
                module TypeCheck = TypeCheck
              end)
module FixedPoint = (Make_FixedPoint)(struct module State' = State end)
module Split =
  (Make_Split)(struct
                 module Global = Global
                 module State' = State
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Unify = UnifyTrail
                 module Constraints = Constraints
                 module Index = Index
                 module Names = Names
                 module Print = Print
                 module TypeCheck = TypeCheck
                 module Subordinate = Subordinate
               end)
module Search =
  (Make_Search)(struct
                  module Global = Global
                  module Data = Data
                  module State' = State
                  module Abstract = Abstract
                  module Conv = Conv
                  module CompSyn' = CompSyn
                  module Compile = Compile
                  module Whnf = Whnf
                  module Unify = UnifyTrail
                  module Index = IndexSkolem
                  module Assign = Assign
                  module CPrint = CPrint
                  module Print = Print
                  module Names = Names
                  module CSManager = CSManager
                end)
module Fill =
  (Make_Fill)(struct
                module Data = Data
                module State' = State
                module Whnf = Whnf
                module Abstract = Abstract
                module Unify = UnifyTrail
                module Constraints = Constraints
                module Index = Index
                module Search = Search
                module TypeCheck = TypeCheck
              end)
module Weaken = (Make_Weaken)(struct module Whnf = Whnf end)
module Interactive =
  (Make_Interactive)(struct
                       module Global = Global
                       module State' = State
                       module Ring = Ring
                       module Formatter = Formatter
                       module Trail = Trail
                       module Names = Names
                       module Weaken = Weaken
                       module ModeSyn = ModeSyn
                       module WorldSyn = WorldSyn
                       module Introduce = Introduce
                       module FixedPoint = FixedPoint
                       module Split = Split
                       module Fill = Fill
                       module Elim = Elim
                     end);;
