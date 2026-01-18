
(* structure ModeSyn  in modesyn.sml *)
module ModeTable =
  (Make_ModeTable)(struct module Table = IntRedBlackTree end)
module ModeDec = (Make_ModeDec)(struct  end)
module ModeCheck =
  (Make_ModeCheck)(struct
                     (*! structure IntSyn = IntSyn !*)
                     module ModeTable = ModeTable
                     module Whnf = Whnf
                     module Index = Index
                     (*! structure Paths = Paths !*)
                     module Origins = Origins
                   end)
module ModePrint =
  (Make_ModePrint)(struct
                     (*! structure ModeSyn' = ModeSyn !*)
                     module Names = Names
                     module Formatter = Formatter
                     module Print = Print
                   end);;
