
(* Initialization *)
(* Author: Carsten Schuermann *)
module type INIT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val init : IntSyn.cid list -> MetaSyn.__State list
  end;;




(* Initialization *)
(* Author: Carsten Schuermann *)
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
      let (V, _) = M.createAtomConst (I.Null, (I.Const cid)) in
      MetaAbstract.abstract
        (M.State
           ((((^) "/" I.conDecName (I.sgnLookup cid)) ^ "/"),
             (M.Prefix (I.Null, I.Null, I.Null)), V))
    let rec init cidList = map init' cidList
    (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover state.
    *)
    (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover state.
    *)
    let init = init
  end ;;
