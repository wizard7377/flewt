
module ModeTable =
  (Make_ModeTable)(struct module Table = IntRedBlackTree end)
module ModeDec = (Make_ModeDec)(struct  end)
module ModeCheck =
  (Make_ModeCheck)(struct
                     module ModeTable = ModeTable
                     module Whnf = Whnf
                     module Index = Index
                     module Origins = Origins
                   end)
module ModePrint =
  (Make_ModePrint)(struct
                     module Names = Names
                     module Formatter = Formatter
                     module Print = Print
                   end);;
