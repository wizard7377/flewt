
module UnknownExn =
  (Make_UnknownExn)(struct
                      let ((exnHistory)(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*))
                        = SMLofNJ.exnHistory
                    end);;
