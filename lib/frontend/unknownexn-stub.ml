
(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*)
module UnknownExn =
  (Make_UnknownExn)(struct let exnHistory = function | exn -> nil end);;
