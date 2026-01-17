
module type INFERENCE  =
  sig
    module StateSyn :
    ((STATESYN)(* Inference: Version 1.3 *)(* Author: Carsten Schuermann *)
    (*! structure FunSyn : FUNSYN !*))
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
                             module Whnf :
                             ((WHNF)(* Inference:  Version 1.3*)
                             (* Author: Carsten Schuermann *)(*! structure IntSyn : INTSYN !*)
                             (*! structure FunSyn' : FUNSYN !*)(*! sharing FunSyn'.IntSyn = IntSyn !*)
                             (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                             (*! sharing Abstract.IntSyn = IntSyn !*)
                             (*! sharing TypeCheck.IntSyn = IntSyn !*)
                             (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                             (*! sharing UniqueSearch.IntSyn = IntSyn !*)
                             (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn !*))
                           end) : INFERENCE =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing Whnf.IntSyn = IntSyn !*)
      (*! structure FunSyn = FunSyn' !*))
    exception Error of string 
    type nonrec operator = unit -> StateSyn'.__State
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success 
    let rec createEVars =
      function
      | (g, (Pi ((Dec (_, V), I.Meta), V'), s)) ->
          let X = I.newEVar (g, (I.EClo (V, s))) in
          let X' = Whnf.lowerEVar X in
          let (Xs, FVs') = createEVars (g, (V', (I.Dot ((I.Exp X), s)))) in
          ((X' :: Xs), FVs')
      | (g, ((_, s) as FVs)) -> (nil, FVs)
    let rec forward =
      function
      | (g, B, (Pi ((_, I.Meta), _) as V)) ->
          let _ =
            if !Global.doubleCheck
            then TypeCheck.typeCheck (g, (V, (I.Uni I.Type)))
            else () in
          let (Xs, (V', s')) = createEVars (g, (V, I.id)) in
          (try
             match UniqueSearch.searchEx
                     (2, Xs,
                       (function
                        | nil -> [Whnf.normalize (V', s')]
                        | _ ->
                            raise (UniqueSearch.Error "Too many solutions")))
             with
             | (VF'')::[] -> SOME VF''
             | [] -> NONE
           with | Error _ -> NONE)
      | (g, B, V) -> NONE
    let rec expand' =
      function
      | ((G0, B0), (I.Null, I.Null), n) ->
          ((I.Null, I.Null), ((function | ((g', B'), w') -> ((g', B'), w'))))
      | ((G0, B0),
         (Decl (g, (Dec (_, V) as D)), Decl (B, (Lemma (S.RL) as T))), n) ->
          let ((G0', B0'), sc') = expand' ((G0, B0), (g, B), (n + 1)) in
          let s = I.Shift (n + 1) in
          let Vs = Whnf.normalize (V, s) in
          (match forward (G0, B0, Vs) with
           | NONE -> (((I.Decl (G0', D)), (I.Decl (B0', T))), sc')
           | SOME (V') ->
               (((I.Decl (G0', D)), (I.Decl (B0', (S.Lemma S.RLdone)))),
                 ((function
                   | ((g', B'), w') ->
                       let V'' = Whnf.normalize (V', w') in
                       sc'
                         (((I.Decl (g', (I.Dec (NONE, V'')))),
                            (I.Decl
                               (B',
                                 (S.Lemma (S.Splits (!MTPGlobal.maxSplit)))))),
                           (I.comp (w', I.shift)))))))
      | (GB0, (Decl (g, D), Decl (B, T)), n) ->
          let ((G0', B0'), sc') = expand' (GB0, (g, B), (n + 1)) in
          (((I.Decl (G0', D)), (I.Decl (B0', T))), sc')
    let rec expand (State (n, (g, B), (IH, OH), d, O, H, F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx g else () in
      let ((Gnew, Bnew), sc) = expand' ((g, B), (g, B), 0) in
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx Gnew else () in
      let ((g', B'), w') = sc ((Gnew, Bnew), I.id) in
      let _ = TypeCheck.typeCheckCtx g' in
      let S' =
        S.State
          (n, (g', B'), (IH, OH), d, (S.orderSub (O, w')),
            (map (function | (i, F') -> (i, (F.forSub (F', w')))) H),
            (F.forSub (F, w'))) in
      let _ = if !Global.doubleCheck then FunTypeCheck.isState S' else () in
      function | () -> S'
    let rec apply f = f ()
    let rec menu _ = "Inference"
    let ((expand)(* createEVars (g, (F, V, s)) = (Xs', (F', V', s'))

       Invariant:
       If   |- g ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} F1 formula
       and  G0 |- V = { x1:A1}  .. {xn:An} V1 : type
       and  g |- s : G0
       then Xs' = (X1', .., Xn') a list of EVars
       and  g |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  g |- s: g'
       and  G0 |- F' = F1 for
       and  G0 |- V' = V1 : type
    *)
      (* forward (g, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- g ctx
       and  g |- B tags
       and  g |- V type
       and  g; . |- F : formula
       then g |- V' type
       and  g; . |- F' : formula

    *)
      (* expand' ((g, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- g ctx     g |- B tags
       and  g prefix of G0 , and B prefix of B0
       and  n + |g| = |G0|
       then sc is a continutation which maps
            |- g' ctx
            and g' |- B' tags
            and g', B' |- w' : G0, B0
            to  |- g'' ctx
            and g'' |- B'' tags
            and g'', B'' extends g, B
       and |- Gnew = g ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)
      (* g' |- V'' : type *)(* expand' S = op'

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
    *))
      = expand
    let apply = apply
    let menu = menu
  end ;;
