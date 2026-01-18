
(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*)
module UnknownExn =
  (Make_UnknownExn)(struct let exnHistory = SMLofNJ.exnHistory end);;
