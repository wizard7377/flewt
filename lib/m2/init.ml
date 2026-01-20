
module type INIT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val init : IntSyn.cid list -> MetaSyn.__State list
  end;;




module Init(Init:sig
                   module MetaSyn' : METASYN
                   module MetaAbstract : METAABSTRACT
                 end) : INIT =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    let rec init' cid =
      let (__V, _) = M.createAtomConst (I.Null, (I.Const cid)) in
      MetaAbstract.abstract
        (M.State
           ((((^) "/" I.conDecName (I.sgnLookup cid)) ^ "/"),
             (M.Prefix (I.Null, I.Null, I.Null)), __V))
    let rec init cidList = map init' cidList
    let init = init
  end ;;
