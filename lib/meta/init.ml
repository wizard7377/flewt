
module type MTPINIT  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val init : FunSyn.__For -> StateSyn.__Order -> StateSyn.__State list
  end;;




module MTPInit(MTPInit:sig
                         module MTPGlobal : MTPGLOBAL
                         module MTPData : MTPDATA
                         module Names : NAMES
                         module StateSyn' : STATESYN
                         module Formatter : FORMATTER
                         module Whnf : WHNF
                         module Print : PRINT
                         module FunPrint : FUNPRINT
                       end) : MTPINIT =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter
    let rec init (__F) (OF) =
      let rec init' __0__ __1__ __2__ __3__ =
        match (__0__, __1__, __2__, __3__) with
        | ((__G, __B), All (_, __O), All (Prim (__D), __F'), __Ss) ->
            let __D' = Names.decName (__G, __D) in
            init'
              (((I.Decl (__G, __D')),
                 (I.Decl (__B, (S.Lemma (S.Splits (!MTPGlobal.maxSplit)))))),
                __O, __F', __Ss)
        | (GB, And (__O1, __O2), And (__F1, __F2), __Ss) ->
            init' (GB, __O1, __F1, (init' (GB, __O2, __F2, __Ss)))
        | (GB, __O, (Ex _ as F'), __Ss) ->
            (S.State
               (((List.length __Ss) + 1), GB, (__F, OF), 1, __O, nil, __F'))
              :: __Ss
        | (GB, __O, (F.True as F'), __Ss) ->
            (S.State
               (((List.length __Ss) + 1), GB, (__F, OF), 1, __O, nil, __F'))
              :: __Ss(*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
           no such case yet  --cs *)
        (* it is possible to calculuate
                 index/induction variable information here
                 define occursOrder in StateSyn.fun  --cs *) in
      ((Names.varReset I.Null;
        MTPData.maxFill := 0;
        init' ((I.Null, I.Null), OF, __F, nil))
        (* added in case there are no existentials -fp *))
    let init = init
  end ;;
