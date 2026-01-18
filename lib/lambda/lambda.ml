
(* Now in intsyn.fun *)
(*
structure IntSyn =
  IntSyn (structure Global = Global);
*)
(* Now in tomega.sml *)
(*
structure Whnf =
  Whnf (! structure IntSyn' = IntSyn !*)
(*! structure IntSyn' = IntSyn !*)
module Constraints =
  (Make_Constraints)(struct
                       (*! structure IntSyn' = IntSyn !*)
                       module Conv = Conv
                     end)
module UnifyNoTrail =
  (Make_Unify)(struct
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Trail = NoTrail
               end)
module UnifyTrail =
  (Make_Unify)(struct
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Trail = Trail
               end)
(* structure Normalize : NORMALIZE =  
  Normalize (! structure IntSyn' = IntSyn !*)
(*! structure Tomega' = Tomega !*)
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
module Approx =
  (Make_Approx)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  module Whnf = Whnf
                end);;
