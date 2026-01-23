module type INIT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val init : IntSyn.cid list -> MetaSyn.state_ list
  end


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
      let (v_, _) = M.createAtomConst (I.Null, (I.Const cid)) in
      MetaAbstract.abstract
        (M.State
           ((((^) "/" I.conDecName (I.sgnLookup cid)) ^ "/"),
             (M.Prefix (I.Null, I.Null, I.Null)), v_))
    let rec init cidList = map init' cidList
    let init = init
  end 