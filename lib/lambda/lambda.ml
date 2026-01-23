module Constraints = (Constraints)(struct module Conv = Conv end)
module UnifyNoTrail =
  (Unify)(struct module Whnf = Whnf
                      module Trail = NoTrail end)
module UnifyTrail =
  (Unify)(struct module Whnf = Whnf
                      module Trail = Trail end)
module Match =
  (Match)(struct
                 module Whnf = Whnf
                 module Unify = UnifyTrail
                 module Trail = Trail
               end)
module Abstract =
  (Abstract)(struct
                    module Whnf = Whnf
                    module Constraints = Constraints
                    module Unify = UnifyNoTrail
                  end)
module Approx = (Approx)(struct module Whnf = Whnf end)