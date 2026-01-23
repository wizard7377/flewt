module CompatArray97 : COMPAT_ARRAY =
  struct let rec appi f arr = Array.appi f (arr, 0, None) end 