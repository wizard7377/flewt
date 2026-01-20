
module type INFERENCE  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> StateSyn.__State
    val menu : operator -> string
  end;;




module Inference(Inference:sig
                             module MTPGlobal : MTPGLOBAL
                             module StateSyn' : STATESYN
                             module Abstract : ABSTRACT
                             module TypeCheck : TYPECHECK
                             module FunTypeCheck : FUNTYPECHECK
                             module UniqueSearch : UNIQUESEARCH
                             module Print : PRINT
                             module Whnf : WHNF
                           end) : INFERENCE =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = unit -> StateSyn'.__State
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success 
    let rec createEVars __0__ __1__ =
      match (__0__, __1__) with
      | (__G, (Pi ((Dec (_, __V), I.Meta), __V'), s)) ->
          let __X = I.newEVar (__G, (I.EClo (__V, s))) in
          let __X' = Whnf.lowerEVar __X in
          let (__Xs, FVs') =
            createEVars (__G, (__V', (I.Dot ((I.Exp __X), s)))) in
          ((__X' :: __Xs), FVs')
      | (__G, ((_, s) as FVs)) -> (nil, FVs)
    let rec forward __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, __B, (Pi ((_, I.Meta), _) as V)) ->
          let _ =
            if !Global.doubleCheck
            then TypeCheck.typeCheck (__G, (__V, (I.Uni I.Type)))
            else () in
          let (__Xs, (__V', s')) = createEVars (__G, (__V, I.id)) in
          (try
             match UniqueSearch.searchEx
                     (2, __Xs,
                       (function
                        | nil -> [Whnf.normalize (__V', s')]
                        | _ ->
                            raise (UniqueSearch.Error "Too many solutions")))
             with
             | (VF'')::[] -> Some VF''
             | [] -> NONE
           with | Error _ -> NONE)
      | (__G, __B, __V) -> NONE
    let rec expand' __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | ((__G0, __B0), (I.Null, I.Null), n) ->
          ((I.Null, I.Null),
            ((fun (__G', __B') -> fun w' -> ((__G', __B'), w'))))
      | ((__G0, __B0),
         (Decl (__G, (Dec (_, __V) as D)), Decl (__B, (Lemma (S.RL) as T))),
         n) ->
          let ((G0', B0'), sc') = expand' ((__G0, __B0), (__G, __B), (n + 1)) in
          let s = I.Shift (n + 1) in
          let __Vs = Whnf.normalize (__V, s) in
          (match forward (__G0, __B0, __Vs) with
           | NONE -> (((I.Decl (G0', __D)), (I.Decl (B0', __T))), sc')
           | Some (__V') ->
               (((I.Decl (G0', __D)), (I.Decl (B0', (S.Lemma S.RLdone)))),
                 ((fun (__G', __B') ->
                     fun w' ->
                       let V'' = Whnf.normalize (__V', w') in
                       ((sc'
                           (((I.Decl (__G', (I.Dec (NONE, V'')))),
                              (I.Decl
                                 (__B',
                                   (S.Lemma (S.Splits (!MTPGlobal.maxSplit)))))),
                             (I.comp (w', I.shift))))
                         (* G' |- V'' : type *))))))
      | (GB0, (Decl (__G, __D), Decl (__B, __T)), n) ->
          let ((G0', B0'), sc') = expand' (GB0, (__G, __B), (n + 1)) in
          (((I.Decl (G0', __D)), (I.Decl (B0', __T))), sc')
    let rec expand (State (n, (__G, __B), (IH, OH), d, __O, __H, __F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx __G else () in
      let ((Gnew, Bnew), sc) = expand' ((__G, __B), (__G, __B), 0) in
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx Gnew else () in
      let ((__G', __B'), w') = sc ((Gnew, Bnew), I.id) in
      let _ = TypeCheck.typeCheckCtx __G' in
      let __S' =
        S.State
          (n, (__G', __B'), (IH, OH), d, (S.orderSub (__O, w')),
            (map (fun i -> fun (__F') -> (i, (F.forSub (__F', w')))) __H),
            (F.forSub (__F, w'))) in
      let _ = if !Global.doubleCheck then FunTypeCheck.isState __S' else () in
      fun () -> __S'
    let rec apply f = f ()
    let rec menu _ = "Inference"
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
