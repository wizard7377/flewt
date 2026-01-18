
(* Inference: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type INFERENCE  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> StateSyn.__State
    val menu : operator -> string
  end;;




(* Inference:  Version 1.3*)
(* Author: Carsten Schuermann *)
module Inference(Inference:sig
                             module MTPGlobal : MTPGLOBAL
                             module StateSyn' : STATESYN
                             module Abstract : ABSTRACT
                             module TypeCheck : TYPECHECK
                             module FunTypeCheck : FUNTYPECHECK
                             module UniqueSearch : UNIQUESEARCH
                             module Print : PRINT
                             (*! structure IntSyn : INTSYN !*)
                             (*! structure FunSyn' : FUNSYN !*)
                             (*! sharing FunSyn'.IntSyn = IntSyn !*)
                             (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                             (*! sharing Abstract.IntSyn = IntSyn !*)
                             (*! sharing TypeCheck.IntSyn = IntSyn !*)
                             (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                             (*! sharing UniqueSearch.IntSyn = IntSyn !*)
                             (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn !*)
                             module Whnf : WHNF
                           end) : INFERENCE =
  struct
    (*! sharing Whnf.IntSyn = IntSyn !*)
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = unit -> StateSyn'.__State
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success 
    let rec createEVars =
      function
      | (__g, (Pi ((Dec (_, __v), I.Meta), __v'), s)) ->
          let x = I.newEVar (__g, (I.EClo (__v, s))) in
          let x' = Whnf.lowerEVar x in
          let (__Xs, FVs') = createEVars (__g, (__v', (I.Dot ((I.Exp x), s)))) in
          ((x' :: __Xs), FVs')
      | (__g, ((_, s) as FVs)) -> (nil, FVs)
    let rec forward =
      function
      | (__g, B, (Pi ((_, I.Meta), _) as __v)) ->
          let _ =
            if !Global.doubleCheck
            then TypeCheck.typeCheck (__g, (__v, (I.Uni I.Type)))
            else () in
          let (__Xs, (__v', s')) = createEVars (__g, (__v, I.id)) in
          (try
             match UniqueSearch.searchEx
                     (2, __Xs,
                       (function
                        | nil -> [Whnf.normalize (__v', s')]
                        | _ ->
                            raise (UniqueSearch.Error "Too many solutions")))
             with
             | (VF'')::[] -> Some VF''
             | [] -> None
           with | Error _ -> None)
      | (__g, B, __v) -> None
    let rec expand' =
      function
      | ((G0, B0), (I.Null, I.Null), n) ->
          ((I.Null, I.Null), ((function | ((__g', B'), w') -> ((__g', B'), w'))))
      | ((G0, B0),
         (Decl (__g, (Dec (_, __v) as __d)), Decl (B, (Lemma (S.RL) as T))), n) ->
          let ((G0', B0'), sc') = expand' ((G0, B0), (__g, B), (n + 1)) in
          let s = I.Shift (n + 1) in
          let __Vs = Whnf.normalize (__v, s) in
          (match forward (G0, B0, __Vs) with
           | None -> (((I.Decl (G0', __d)), (I.Decl (B0', T))), sc')
           | Some (__v') ->
               (((I.Decl (G0', __d)), (I.Decl (B0', (S.Lemma S.RLdone)))),
                 ((function
                   | ((__g', B'), w') ->
                       let __v'' = Whnf.normalize (__v', w') in
                       sc'
                         (((I.Decl (__g', (I.Dec (None, __v'')))),
                            (I.Decl
                               (B',
                                 (S.Lemma (S.Splits (!MTPGlobal.maxSplit)))))),
                           (I.comp (w', I.shift)))))))
      | (GB0, (Decl (__g, __d), Decl (B, T)), n) ->
          let ((G0', B0'), sc') = expand' (GB0, (__g, B), (n + 1)) in
          (((I.Decl (G0', __d)), (I.Decl (B0', T))), sc')
    let rec expand (State (n, (__g, B), (IH, OH), d, O, H, F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx __g else () in
      let ((Gnew, Bnew), sc) = expand' ((__g, B), (__g, B), 0) in
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx Gnew else () in
      let ((__g', B'), w') = sc ((Gnew, Bnew), I.id) in
      let _ = TypeCheck.typeCheckCtx __g' in
      let S' =
        S.State
          (n, (__g', B'), (IH, OH), d, (S.orderSub (O, w')),
            (map (function | (i, __F') -> (i, (F.forSub (__F', w')))) H),
            (F.forSub (F, w'))) in
      let _ = if !Global.doubleCheck then FunTypeCheck.isState S' else () in
      function | () -> S'
    let rec apply f = f ()
    let rec menu _ = "Inference"
    (* createEVars (__g, (F, __v, s)) = (__Xs', (__F', __v', s'))

       Invariant:
       If   |- __g ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} __F1 formula
       and  G0 |- __v = { x1:A1}  .. {xn:An} V1 : type
       and  __g |- s : G0
       then __Xs' = (X1', .., Xn') a list of EVars
       and  __g |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  __g |- s: __g'
       and  G0 |- __F' = __F1 for
       and  G0 |- __v' = V1 : type
    *)
    (* forward (__g, B, (__v, F)) = (__v', __F')  (or none)

       Invariant:
       If   |- __g ctx
       and  __g |- B tags
       and  __g |- __v type
       and  __g; . |- F : formula
       then __g |- __v' type
       and  __g; . |- __F' : formula

    *)
    (* expand' ((__g, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- __g ctx     __g |- B tags
       and  __g prefix of G0 , and B prefix of B0
       and  n + |__g| = |G0|
       then sc is a continutation which maps
            |- __g' ctx
            and __g' |- B' tags
            and __g', B' |- w' : G0, B0
            to  |- __g'' ctx
            and __g'' |- B'' tags
            and __g'', B'' extends __g, B
       and |- Gnew = __g ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)
    (* __g' |- __v'' : type *)
    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
