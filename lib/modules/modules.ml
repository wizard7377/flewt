
module ModSyn =
  (Make_ModSyn)(struct
                  module Global = Global
                  module Names' = Names
                  module Origins = Origins
                  module Whnf = Whnf
                  module Strict = Strict
                  module IntTree = IntRedBlackTree
                  module HashTable = StringHashTable
                end);;
