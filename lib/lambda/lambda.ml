
module Constraints = (Make_Constraints)(struct module Conv = Conv end)
module UnifyNoTrail =
  (Make_Unify)(struct module Whnf = Whnf
                      module Trail = NoTrail end)
module UnifyTrail =
  (Make_Unify)(struct module Whnf = Whnf
                      module Trail = Trail end)
module Match =
  (Make_Match)(struct
                 module Whnf = Whnf
                 module Unify = UnifyTrail
                 module Trail = Trail
               end)
module Abstract =
  (Make_Abstract)(struct
                    module Whnf = Whnf
                    module Constraints = Constraints
                    module Unify = UnifyNoTrail
                  end)
module Approx = (Make_Approx)(struct module Whnf = Whnf end);;
