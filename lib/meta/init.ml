module type MTPINIT  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val init : (FunSyn.for_ * StateSyn.order_) -> StateSyn.state_ list
  end


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
    let rec init (f_, OF) =
      let rec init' =
        begin function
        | ((g_, b_), All (_, o_), All (Prim (d_), f'_), ss_) ->
            let d'_ = Names.decName (g_, d_) in
            init'
              (((I.Decl (g_, d'_)),
                 (I.Decl (b_, (S.Lemma (S.Splits !MTPGlobal.maxSplit))))),
                o_, f'_, ss_)
        | (GB, And (o1_, o2_), And (f1_, f2_), ss_) ->
            init' (GB, o1_, f1_, (init' (GB, o2_, f2_, ss_)))
        | (GB, o_, (Ex _ as f'_), ss_) ->
            (S.State (((List.length ss_) + 1), GB, (f_, OF), 1, o_, [], f'_))
              :: ss_
        | (GB, o_, (F.True as f'_), ss_) ->
            (S.State (((List.length ss_) + 1), GB, (f_, OF), 1, o_, [], f'_))
              :: ss_ end(*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
           no such case yet  --cs *)
      (* it is possible to calculuate
                 index/induction variable information here
                 define occursOrder in StateSyn.fun  --cs *) in
    ((begin Names.varReset I.Null;
      MTPData.maxFill := 0;
      init' ((I.Null, I.Null), OF, f_, []) end)
      (* added in case there are no existentials -fp *))
  let init = init end
