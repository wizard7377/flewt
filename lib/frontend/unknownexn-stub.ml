
module UnknownExn =
  (Make_UnknownExn)(struct
                      let ((exnHistory)(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*))
                        = function | exn -> nil
                    end);;
