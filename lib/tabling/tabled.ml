
module TabledSyn =
  (Make_TabledSyn)(struct
                     module Names = Names
                     module Table = IntRedBlackTree
                     module Index = Index
                   end);;
