module type MTPDATA  = sig val maxFill : int ref end


module MTPData(MTPData:sig module MTPGlobal : MTPGLOBAL end) : MTPDATA =
  struct let maxFill = ref 0 end 