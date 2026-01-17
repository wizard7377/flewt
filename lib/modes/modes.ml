
module ModeTable =
  (Make_ModeTable)(struct
                     module Table =
                       ((IntRedBlackTree)(* structure ModeSyn  in modesyn.sml *))
                   end) module ModeDec = (Make_ModeDec)(struct  end)
module ModeCheck =
  (Make_ModeCheck)(struct
                     module ModeTable =
                       ((ModeTable)(*! structure ModeSyn' = ModeSyn !*)
                       (*! structure Paths' = Paths !*)
                       (*! structure IntSyn = IntSyn !*))
                     module Whnf = Whnf
                     module Index = Index
                     module Origins =
                       ((Origins)(*! structure Paths = Paths !*))
                   end)
module ModePrint =
  (Make_ModePrint)(struct
                     module Names =
                       ((Names)(*! structure ModeSyn' = ModeSyn !*))
                     module Formatter = Formatter
                     module Print = Print
                   end);;
