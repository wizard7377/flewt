
module type DATA  =
  sig
    val maxFill :
      ((int)(* Author: Carsten Schuermann *)(* Data Global parameters *))
        ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end;;




module Data : DATA =
  struct
    let ((maxFill)(* Meta data parameters *)(* Author: Carsten Schuermann *))
      = ref 5
    let maxSplit = ref 5
    let maxRecurse = ref 2
  end ;;
