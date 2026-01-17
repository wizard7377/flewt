
module Flit =
  (Make_Flit)(struct
                module Global =
                  ((Global)(* cope with nonstandard old smlnj name of PackWord32Little -jcreed 2006.9.15 *))
                module Word = Word32
                module Pack = Pack32Little
                module IntSyn = IntSyn
                module Whnf = Whnf
                module Print = Print
                module Names = Names
                module Index = Index
                module Table = IntRedBlackTree
              end);;
