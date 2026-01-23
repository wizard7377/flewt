module ModeTable =
  (ModeTable)(struct module Table = IntRedBlackTree end)
module ModeDec = (ModeDec)(struct  end)
module ModeCheck =
  (ModeCheck)(struct
                     module ModeTable = ModeTable
                     module Whnf = Whnf
                     module Index = Index
                     module Origins = Origins
                   end)
module ModePrint =
  (ModePrint)(struct
                     module Names = Names
                     module Formatter = Formatter
                     module Print = Print
                   end)