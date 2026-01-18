
module TabledSyn =
  (Make_TabledSyn)(struct
                     (*! structure IntSyn' = IntSyn !*)
                     module Names = Names
                     module Table = IntRedBlackTree
                     module Index = Index
                   end);;
