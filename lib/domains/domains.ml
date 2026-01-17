
module Integers = (Make_Integers)(struct ;;IntInf end)
module Rationals = (Make_Rationals)(struct ;;Integers end)
module IntegersMod7 = (Make_IntegersMod)(struct let p = 7 end);;
