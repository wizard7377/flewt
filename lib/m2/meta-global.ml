
module type METAGLOBAL  =
  sig
    type __Strategy =
      | RFS 
      | FRS (* Author: Carsten Schuermann *)(* Global parameters *)
    val strategy : __Strategy ref
    val maxFill : int ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end;;




module MetaGlobal : METAGLOBAL =
  struct
    type __Strategy =
      | RFS 
      | FRS (* Author: Carsten Schuermann *)(* Global parameters *)
    let strategy = ref FRS
    let maxFill = ref 6
    let maxSplit = ref 2
    let maxRecurse = ref 10
  end ;;
