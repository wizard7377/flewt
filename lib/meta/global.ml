
module type MTPGLOBAL  =
  sig
    type __ProverType =
      | New 
      | Old (* Author: Carsten Schuermann *)(* Global parameters *)
    val prover : __ProverType ref
    val maxFill : int ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end;;




module MTPGlobal(MTPGlobal:sig
                             module MetaGlobal :
                             ((METAGLOBAL)(* Meta Global parameters *)
                             (* Author: Carsten Schuermann *))
                           end) : MTPGLOBAL =
  struct
    type __ProverType =
      | New 
      | Old 
    let prover = ref New
    let maxFill = MetaGlobal.maxFill
    let maxSplit = MetaGlobal.maxSplit
    let maxRecurse = MetaGlobal.maxRecurse
  end ;;
