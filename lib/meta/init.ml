
(* Initialization *)
(* Author: Carsten Schuermann *)
module type MTPINIT  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    (* Current restriction to non-mutual inductive theorems ! *)
    val init : (FunSyn.__For * StateSyn.__Order) -> StateSyn.__State list
  end;;




(* Initialization *)
(* Author: Carsten Schuermann *)
module MTPInit(MTPInit:sig
                         module MTPGlobal : MTPGLOBAL
                         module MTPData : MTPDATA
                         module Names : NAMES
                         module StateSyn' : STATESYN
                         module Formatter : FORMATTER
                         module Whnf : WHNF
                         module Print : PRINT
                         (*! structure IntSyn : INTSYN !*)
                         (*! sharing Names.IntSyn = IntSyn !*)
                         (*! structure FunSyn' : FUNSYN !*)
                         (*! sharing FunSyn'.IntSyn = IntSyn !*)
                         (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                         (*! sharing Whnf.IntSyn = IntSyn !*)
                         (*! sharing Print.IntSyn = IntSyn !*)
                         module FunPrint : FUNPRINT
                       end) : MTPINIT =
  struct
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter
    let rec init (F, OF) =
      let rec init' =
        function
        | ((__g, B), All (_, O), All (Prim (__d), __F'), __Ss) ->
            let __d' = Names.decName (__g, __d) in
            init'
              (((I.Decl (__g, __d')),
                 (I.Decl (B, (S.Lemma (S.Splits (!MTPGlobal.maxSplit)))))),
                O, __F', __Ss)
        | (GB, And (O1, O2), And (__F1, __F2), __Ss) ->
            init' (GB, O1, __F1, (init' (GB, O2, __F2, __Ss)))
        | (GB, O, (Ex _ as __F'), __Ss) ->
            (S.State (((List.length __Ss) + 1), GB, (F, OF), 1, O, nil, __F')) ::
              __Ss
        | (GB, O, (F.True as __F'), __Ss) ->
            (S.State (((List.length __Ss) + 1), GB, (F, OF), 1, O, nil, __F')) ::
              __Ss in
      Names.varReset I.Null;
      MTPData.maxFill := 0;
      init' ((I.Null, I.Null), OF, F, nil)
    (* init (F, OF) = __Ss'

       Invariant:
       If   . |- F formula    and   F in nf
       and  . |- OF order
       then __Ss' is a list of initial states for the theorem prover
    *)
    (* it is possible to calculuate
                 index/induction variable information here
                 define occursOrder in StateSyn.fun  --cs *)
    (*      | init' (__g, B, O, (F.All (F.Block _, F), s)) =
           no such case yet  --cs *)
    (* added in case there are no existentials -fp *)
    let init = init
  end ;;
