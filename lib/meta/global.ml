
module type MTPGLOBAL  =
  sig
    type __ProverType =
      | New 
      | Old 
    val prover : __ProverType ref
    val maxFill : int ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end;;




module MTPGlobal(MTPGlobal:sig module MetaGlobal : METAGLOBAL end) :
  MTPGLOBAL =
  struct
    type __ProverType =
      | New 
      | Old 
    let prover = ref New
    let maxFill = MetaGlobal.maxFill
    let maxSplit = MetaGlobal.maxSplit
    let maxRecurse = MetaGlobal.maxRecurse
  end ;;
