module type METAGLOBAL  =
  sig
    type strategy_ =
      | RFS 
      | FRS 
    val strategy : strategy_ ref
    val maxFill : int ref
    val maxSplit : int ref
    val maxRecurse : int ref
  end


module MetaGlobal : METAGLOBAL =
  struct
    type strategy_ =
      | RFS 
      | FRS 
    let strategy = ref FRS
    let maxFill = ref 6
    let maxSplit = ref 2
    let maxRecurse = ref 10
  end 