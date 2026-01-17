
module TabledSyn =
  (Make_TabledSyn)(struct
                     module Names =
                       ((Names)(*! structure IntSyn' = IntSyn !*))
                     module Table = IntRedBlackTree
                     module Index = Index
                   end);;
