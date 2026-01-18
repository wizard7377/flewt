
module Integers_impl = Integers(Int_inf.IntInf)
module Rationals_impl = Rationals(Integers_impl)
module IntegersMod7 = IntegersMod(struct let p = 7 end);;
