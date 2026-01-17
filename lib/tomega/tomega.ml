
module TomegaAbstract =
  (Make_TomegaAbstract)(struct
                          module Global = Global
                          module Abstract = Abstract
                          module Whnf = Whnf
                          module Subordinate = Subordinate
                        end)
module TomegaPrint =
  (Make_TomegaPrint)(struct
                       module Formatter =
                         ((Formatter)(*! structure IntSyn' = IntSyn !*)
                         (*! structure Tomega' = Tomega !*))
                       module Names = Names
                       module Print = Print
                     end)
module TomegaTypeCheck =
  (Make_TomegaTypeCheck)(struct
                           module Global = Global
                           module Abstract =
                             ((Abstract)(*! structure IntSyn' = IntSyn !*))
                           module TypeCheck =
                             ((TypeCheck)(*! structure Tomega' = Tomega !*))
                           module Conv = Conv
                           module Whnf = Whnf
                           module Subordinate = Subordinate
                           module TomegaPrint = TomegaPrint
                           module Print = Print
                           module Weaken = Weaken
                           module TomegaAbstract = TomegaAbstract
                         end)
module Opsem =
  (Make_Opsem)(struct
                 module Global =
                   ((Global)(* structure TomegaUnify = TomegaUnify
  (structure Global = Global
   ! structure IntSyn' = IntSyn !*)
                   (*! structure Tomega' = Tomega !*))
                 module IntSyn' = IntSyn
                 module Abstract = Abstract
                 module Tomega' = Tomega
                 module TypeCheck = TypeCheck
                 module Unify = UnifyNoTrail
                 module Conv = Conv
                 module Whnf = Whnf
                 module Print = Print
                 module Subordinate = Subordinate
                 module TomegaPrint = TomegaPrint
                 module TomegaTypeCheck = TomegaTypeCheck
                 module Weaken = Weaken
               end)
module Redundant =
  (Make_Redundant)(struct
                     module Opsem =
                       ((Opsem)(*
structure Opsem = OpsemCont
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Unify = UnifyNoTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Print = Print
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Weaken = Weaken);
*))
                   end)
module Converter =
  (Make_Converter)(struct
                     module Global = Global
                     module IntSyn' = IntSyn
                     module Abstract = Abstract
                     module Tomega' = Tomega
                     module Names = Names
                     module ModeTable = ModeTable
                     module TypeCheck = TypeCheck
                     module TomegaAbstract = TomegaAbstract
                     module TomegaTypeCheck = TomegaTypeCheck
                     module Trail = Trail
                     module Unify = UnifyTrail
                     module TomegaPrint = TomegaPrint
                     module Whnf = Whnf
                     module WorldSyn = WorldSyn
                     module Worldify = Worldify
                     module Subordinate = Subordinate
                     module Print = Print
                     module Redundant = Redundant
                     module Weaken = Weaken
                   end)
module TomegaCoverage =
  (Make_TomegaCoverage)(struct
                          module Global = Global
                          module IntSyn' = IntSyn
                          module Tomega' = Tomega
                          module TomegaPrint = TomegaPrint
                          module TomegaTypeCheck = TomegaTypeCheck
                          module Cover = Cover
                        end);;
