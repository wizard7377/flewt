
module Constraints =
  (Make_Constraints)(struct
                       module Conv =
                         ((Conv)(* Now in intsyn.fun *)
                         (*
structure IntSyn =
  IntSyn (structure Global = Global);
*)
                         (* Now in tomega.sml *)(*
structure Whnf =
  Whnf (! structure IntSyn' = IntSyn !*)
                         (*! structure IntSyn' = IntSyn !*)
                         (*! structure IntSyn' = IntSyn !*))
                     end)
module UnifyNoTrail =
  (Make_Unify)(struct
                 module Whnf =
                   ((Whnf)(*! structure IntSyn' = IntSyn !*))
                 module Trail = NoTrail
               end)
module UnifyTrail =
  (Make_Unify)(struct
                 module Whnf =
                   ((Whnf)(*! structure IntSyn' = IntSyn !*))
                 module Trail = Trail
               end)
module Match =
  (Make_Match)(struct
                 module Whnf =
                   ((Whnf)(* structure Normalize : NORMALIZE =  
  Normalize (! structure IntSyn' = IntSyn !*)
                   (*! structure Tomega' = Tomega !*))
                 module Unify = UnifyTrail
                 module Trail = Trail
               end)
module Abstract =
  (Make_Abstract)(struct
                    module Whnf = Whnf
                    module Constraints = Constraints
                    module Unify = UnifyNoTrail
                  end)
module Approx =
  (Make_Approx)(struct
                  module Whnf =
                    ((Whnf)(*! structure IntSyn' = IntSyn !*))
                end);;
