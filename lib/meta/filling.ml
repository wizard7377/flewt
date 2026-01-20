
module type MTPFILLING  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> (int * FunSyn.__Pro)
    val menu : operator -> string
  end;;




module MTPFilling(MTPFilling:sig
                               module MTPGlobal : MTPGLOBAL
                               module StateSyn' : STATESYN
                               module Abstract : ABSTRACT
                               module TypeCheck : TYPECHECK
                               module MTPData : MTPDATA
                               module Search : MTPSEARCH
                               module Whnf : WHNF
                             end) : MTPFILLING =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    exception TimeOut 
    type nonrec operator = unit -> (int * FunSyn.__Pro)
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success of int 
    let rec createEVars __0__ __1__ =
      match (__0__, __1__) with
      | (__G, (F.True, s)) -> (nil, F.Unit)
      | (__G, (Ex (Dec (_, __V), __F), s)) ->
          let __X = I.newEVar (__G, (I.EClo (__V, s))) in
          let __X' = Whnf.lowerEVar __X in
          let (__Xs, __P) =
            createEVars (__G, (__F, (I.Dot ((I.Exp __X), s)))) in
          ((__X' :: __Xs), (F.Inx (__X, __P)))
    let rec expand (State (n, (__G, __B), (IH, OH), d, __O, __H, __F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx __G else () in
      let (__Xs, __P) = createEVars (__G, (__F, I.id)) in
      fun () ->
        try
          Search.searchEx
            ((!MTPGlobal.maxFill), __Xs,
              (fun max ->
                 if !Global.doubleCheck
                 then
                   map
                     (fun (EVar (_, __G', __V, _) as X) ->
                        TypeCheck.typeCheck (__G', (__X, __V))) __Xs
                 else [];
                 raise (Success max)));
          raise (Error "Filling unsuccessful")
        with
        | Success max ->
            ((:=) MTPData.maxFill Int.max ((!MTPData.maxFill), max);
             (max, __P))
    let rec apply f = f ()
    let rec menu _ = "Filling   (tries to close this subgoal)"
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
