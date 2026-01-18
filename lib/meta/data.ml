
(* Data aquired during proof search *)
(* Author: Carsten Schuermann *)
module type MTPDATA  = sig val maxFill : int ref end;;




(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPData(MTPData:sig module MTPGlobal : MTPGLOBAL end) : MTPDATA =
  struct let maxFill = ref 0 end ;;
