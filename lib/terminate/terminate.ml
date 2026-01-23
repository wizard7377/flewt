module Checking =
  (Checking)(struct
                    module Global = Global
                    module Whnf = Whnf
                    module Conv = Conv
                    module Unify = UnifyTrail
                    module Trail = Trail
                    module Names = Names
                    module Index = Index
                    module Subordinate = Subordinate
                    module Formatter = Formatter
                    module Print = Print
                    module Order = Order
                    module Paths = Paths
                    module Origins = Origins
                  end)
module Reduces =
  (Reduces)(struct
                   module Global = Global
                   module Whnf = Whnf
                   module Names = Names
                   module Index = Index
                   module Subordinate = Subordinate
                   module Formatter = Formatter
                   module Print = Print
                   module Order = Order
                   module Checking = Checking
                   module Paths = Paths
                   module Origins = Origins
                 end)