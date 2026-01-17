
module ModSyn =
  (Make_ModSyn)(struct
                  module Global = Global
                  module Names' =
                    ((Names)(*! structure IntSyn' = IntSyn !*))
                  module Origins =
                    ((Origins)(*! structure Paths' = Paths !*))
                  module Whnf = Whnf
                  module Strict = Strict
                  module IntTree = IntRedBlackTree
                  module HashTable = StringHashTable
                end);;
