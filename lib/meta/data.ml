
module type MTPDATA  =
  sig
    val maxFill :
      ((int)(* Author: Carsten Schuermann *)(* Data aquired during proof search *))
        ref
  end;;




module MTPData(MTPData:sig
                         module MTPGlobal :
                         ((MTPGLOBAL)(* Meta Global parameters *)
                         (* Author: Carsten Schuermann *))
                       end) : MTPDATA = struct let maxFill = ref 0 end ;;
