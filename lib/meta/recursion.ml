
(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPRECURSION  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> StateSyn.__State
    val menu : operator -> string
  end;;




(* Meta Recursion Version 1.3 *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)
module MTPRecursion(MTPRecursion:sig
                                   module MTPGlobal : MTPGLOBAL
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module MTPAbstract : MTPABSTRACT
                                   module FunTypeCheck : FUNTYPECHECK
                                   module MTPrint : MTPRINT
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                   module Conv : CONV
                                   module Names : NAMES
                                   module Subordinate : SUBORDINATE
                                   module Print : PRINT
                                   module TypeCheck : TYPECHECK
                                   module Formatter : FORMATTER
                                   (*! structure IntSyn : INTSYN !*)
                                   (*! structure FunSyn : FUNSYN !*)
                                   (*! sharing FunSyn.IntSyn = IntSyn !*)
                                   (*! sharing StateSyn'.IntSyn = IntSyn !*)
                                   (*! sharing StateSyn'.FunSyn = FunSyn !*)
                                   (*! sharing Abstract.IntSyn = IntSyn !*)
                                   (*! sharing MTPAbstract.IntSyn = IntSyn !*)
                                   (*! sharing MTPAbstract.FunSyn = FunSyn !*)
                                   (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
                                   (*! sharing Whnf.IntSyn = IntSyn !*)
                                   (*! sharing Unify.IntSyn = IntSyn !*)
                                   (*! sharing Conv.IntSyn = IntSyn !*)
                                   (*! sharing Names.IntSyn = IntSyn !*)
                                   (*! sharing Subordinate.IntSyn = IntSyn !*)
                                   (*! sharing Print.IntSyn = IntSyn !*)
                                   (*! sharing TypeCheck.IntSyn = IntSyn !*)
                                   module FunPrint : FUNPRINT
                                 end) : MTPRECURSION =
  struct
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn !*)
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = StateSyn.__State
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module N = Names
    module Fmt = Formatter
    module A = MTPAbstract
    type __Dec =
      | Lemma of (int * F.__For) 
    let rec closedCtx =
      function
      | I.Null -> ()
      | Decl (G, D) ->
          if Abstract.closedDec (G, (D, I.id))
          then raise Domain
          else closedCtx G
    let rec spine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1)))
    let rec someEVars =
      function
      | (G, nil, s) -> s
      | (G, (Dec (_, V))::L, s) ->
          someEVars
            (G, L, (I.Dot ((I.Exp (I.newEVar (G, (I.EClo (V, s))))), s)))
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((D)::G, s) -> (::) (I.decSub (D, s)) ctxSub (G, (I.dot1 s))
    let rec appendCtx =
      function
      | (GB1, T, nil) -> GB1
      | ((G1, B1), T, (D)::G2) ->
          appendCtx (((I.Decl (G1, D)), (I.Decl (B1, T))), T, G2)
    let rec createCtx =
      function
      | ((G, B), nil, s) -> ((G, B), s, ((function | AF -> AF)))
      | ((G, B), n::ll, s) ->
          let LabelDec (l, G1, G2) = F.labelLookup n in
          let t = someEVars (G, G1, I.id) in
          let G2' = ctxSub (G2, t) in
          let (G', B') = appendCtx ((G, B), (S.Parameter (SOME n)), G2') in
          let s' = I.comp (s, (I.Shift (List.length G2'))) in
          let (GB'', s'', af'') = createCtx ((G', B'), ll, s') in
          (GB'', s'',
            ((function
              | AF -> A.Block ((G, t, (List.length G1), G2'), (af'' AF)))))
    let rec createEVars =
      function
      | (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, Decl (G0, Dec (_, V))) ->
          let s = createEVars (G, G0) in
          I.Dot ((I.Exp (I.newEVar (G, (I.EClo (V, s))))), s)
    let rec checkCtx =
      function
      | (G, nil, (V2, s)) -> false__
      | (G, (Dec (_, V1) as D)::G2, (V2, s)) ->
          (CSManager.trail
             (function | () -> Unify.unifiable (G, (V1, I.id), (V2, s))))
            || (checkCtx ((I.Decl (G, D)), G2, (V2, (I.comp (s, I.shift)))))
    let rec checkLabels ((G', B'), (V, s), ll, l) =
      if l < 0
      then NONE
      else
        (let LabelDec (name, G1, G2) = F.labelLookup l in
         let s = someEVars (G', G1, I.id) in
         let G2' = ctxSub (G2, s) in
         let t = someEVars (G', G1, I.id) in
         let G2' = ctxSub (G2, t) in
         if
           (not (List.exists (function | l' -> l = l') ll)) &&
             (checkCtx (G', G2', (V, s)))
         then SOME l
         else checkLabels ((G', B'), (V, s), ll, (l - 1)))
    let rec appendRL =
      function
      | (nil, Ds) -> Ds
      | ((Lemma (n, F) as L)::Ds1, Ds2) ->
          let Ds' = appendRL (Ds1, Ds2) in
          if
            List.exists
              (function
               | Lemma (n', F') ->
                   (n = n') && (F.convFor ((F, I.id), (F', I.id)))) Ds'
          then Ds'
          else L :: Ds'
    let rec recursion
      ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) =
      let ((G', B'), s', af) = createCtx ((G0, B0), ll, I.id) in
      let t' = createEVars (G', Gall) in
      let AF = af (A.Head (G', (Fex, t'), (I.ctxLength Gall))) in
      let Oex' = S.orderSub (Oex, t') in
      let Ocurrent' = S.orderSub (Ocurrent, s') in
      let rec sc (Ds) =
        let Fnew = A.abstractApproxFor AF in
        if
          List.exists
            (function
             | (nhist, Fhist) ->
                 (nih = nhist) && (F.convFor ((Fnew, I.id), (Fhist, I.id))))
            H
        then Ds
        else (Lemma (nih, Fnew)) :: Ds in
      let rec ac ((G', B'), Vs, Ds) =
        match checkLabels ((G', B'), Vs, ll, ((F.labelSize ()) - 1)) with
        | NONE -> Ds
        | SOME l' ->
            let Ds' =
              recursion
                ((nih, Gall, Fex, Oex),
                  (ncurrent, (G0, B0), (l' :: ll), Ocurrent, H, F)) in
            appendRL (Ds', Ds) in
      if ncurrent < nih
      then ordle ((G', B'), Oex', Ocurrent', sc, ac, nil)
      else ordlt ((G', B'), Oex', Ocurrent', sc, ac, nil)
    let rec set_parameter
      (((G1, B1) as GB), (EVar (r, _, V, _) as X), k, sc, ac, Ds) =
      let rec set_parameter' =
        function
        | ((I.Null, I.Null), _, Ds) -> Ds
        | ((Decl (G, D), Decl (B, Parameter _)), k, Ds) ->
            let Dec (_, V') as D' = I.decSub (D, (I.Shift k)) in
            let Ds' =
              CSManager.trail
                (function
                 | () ->
                     if
                       (Unify.unifiable (G1, (V, I.id), (V', I.id))) &&
                         (Unify.unifiable
                            (G1, (X, I.id),
                              ((I.Root ((I.BVar k), I.Nil)), I.id)))
                     then sc Ds
                     else Ds) in
            set_parameter' ((G, B), (k + 1), Ds')
        | ((Decl (G, D), Decl (B, _)), k, Ds) ->
            set_parameter' ((G, B), (k + 1), Ds) in
      set_parameter' (GB, 1, Ds)
    let rec ltinit (GB, k, (Us, Vs), UsVs', sc, ac, Ds) =
      ltinitW (GB, k, (Whnf.whnfEta (Us, Vs)), UsVs', sc, ac, Ds)
    let rec ltinitW =
      function
      | (GB, k, (Us, ((Root _, _) as Vs)), UsVs', sc, ac, Ds) ->
          lt (GB, k, (Us, Vs), UsVs', sc, ac, Ds)
      | ((G, B), k, ((Lam (D1, U), s1), (Pi (D2, V), s2)),
         ((U', s1'), (V', s2')), sc, ac, Ds) ->
          ltinit
            (((I.Decl (G, (I.decSub (D1, s1)))),
               (I.Decl (B, (S.Parameter NONE)))), (k + 1),
              ((U, (I.dot1 s1)), (V, (I.dot1 s2))),
              ((U', (I.comp (s1', I.shift))), (V', (I.comp (s2', I.shift)))),
              sc, ac, Ds)
    let rec lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
      ltW (GB, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ac, Ds)
    let rec ltW =
      function
      | (GB, k, (Us, Vs), ((Root (Const c, S'), s'), Vs'), sc, ac, Ds) ->
          ltSpine
            (GB, k, (Us, Vs), ((S', s'), ((I.constType c), I.id)), sc, ac,
              Ds)
      | (((G, B) as GB), k, (Us, Vs), ((Root (BVar n, S'), s'), Vs'), sc, ac,
         Ds) ->
          (match I.ctxLookup (B, n) with
           | Parameter _ ->
               let Dec (_, V') = I.ctxDec (G, n) in
               ltSpine (GB, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ac, Ds)
           | Lemma _ -> Ds)
      | (GB, _, _, ((EVar _, _), _), _, _, Ds) -> Ds
      | (((G, B) as GB), k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ac, Ds) ->
          let Ds' = Ds in
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' =
              function | Ds'' -> set_parameter (GB, X, k, sc, ac, Ds'') in
            lt
              (GB, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ac, Ds')
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               lt
                 (GB, k, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, ac, Ds'))
            else Ds'
    let rec ltSpine (GB, k, (Us, Vs), (Ss', Vs'), sc, ac, Ds) =
      ltSpineW (GB, k, (Us, Vs), (Ss', (Whnf.whnf Vs')), sc, ac, Ds)
    let rec ltSpineW =
      function
      | (GB, k, (Us, Vs), ((I.Nil, _), _), _, _, Ds) -> Ds
      | (GB, k, (Us, Vs), ((SClo (S, s'), s''), Vs'), sc, ac, Ds) ->
          ltSpineW
            (GB, k, (Us, Vs), ((S, (I.comp (s', s''))), Vs'), sc, ac, Ds)
      | (GB, k, (Us, Vs),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ac,
         Ds) ->
          let Ds' = le (GB, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ac, Ds) in
          ltSpine
            (GB, k, (Us, Vs),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))),
              sc, ac, Ds')
    let rec eq ((G, B), (Us, Vs), (Us', Vs'), sc, ac, Ds) =
      CSManager.trail
        (function
         | () ->
             if
               (Unify.unifiable (G, Vs, Vs')) &&
                 (Unify.unifiable (G, Us, Us'))
             then sc Ds
             else Ds)
    let rec le (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
      let Ds' = eq (GB, (Us, Vs), (Us', Vs'), sc, ac, Ds) in
      leW (GB, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ac, Ds')
    let rec leW =
      function
      | (((G, B) as GB), k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ac, Ds) ->
          let Ds' = ac (GB, (V1', s1'), Ds) in
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' =
              function | Ds'' -> set_parameter (GB, X, k, sc, ac, Ds'') in
            le
              (GB, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ac, Ds')
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               let sc' = sc in
               let Ds'' =
                 le
                   (GB, k, ((U, s1), (V, s2)),
                     ((U', (I.Dot ((I.Exp X), s1'))),
                       (V', (I.Dot ((I.Exp X), s2')))), sc', ac, Ds') in
               Ds'')
            else Ds'
      | (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) ->
          lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds)
    let rec ordlt =
      function
      | (GB, Arg (UsVs), Arg (UsVs'), sc, ac, Ds) ->
          ltinit (GB, 0, UsVs, UsVs', sc, ac, Ds)
      | (GB, Lex (L), Lex (L'), sc, ac, Ds) ->
          ordltLex (GB, L, L', sc, ac, Ds)
      | (GB, Simul (L), Simul (L'), sc, ac, Ds) ->
          ordltSimul (GB, L, L', sc, ac, Ds)
    let rec ordltLex =
      function
      | (GB, nil, nil, sc, ac, Ds) -> Ds
      | (GB, (O)::L, (O')::L', sc, ac, Ds) ->
          let Ds' =
            CSManager.trail (function | () -> ordlt (GB, O, O', sc, ac, Ds)) in
          ordeq
            (GB, O, O',
              (function | Ds'' -> ordltLex (GB, L, L', sc, ac, Ds'')), ac,
              Ds')
    let rec ordltSimul =
      function
      | (GB, nil, nil, sc, ac, Ds) -> Ds
      | (GB, (O)::L, (O')::L', sc, ac, Ds) ->
          let Ds'' =
            CSManager.trail
              (function
               | () ->
                   ordlt
                     (GB, O, O',
                       (function | Ds' -> ordleSimul (GB, L, L', sc, ac, Ds')),
                       ac, Ds)) in
          ordeq
            (GB, O, O',
              (function | Ds' -> ordltSimul (GB, L, L', sc, ac, Ds')), ac,
              Ds'')
    let rec ordleSimul =
      function
      | (GB, nil, nil, sc, ac, Ds) -> sc Ds
      | (GB, (O)::L, (O')::L', sc, ac, Ds) ->
          ordle
            (GB, O, O',
              (function | Ds' -> ordleSimul (GB, L, L', sc, ac, Ds')), ac,
              Ds)
    let rec ordeq =
      function
      | ((G, B), Arg (Us, Vs), Arg (Us', Vs'), sc, ac, Ds) ->
          if (Unify.unifiable (G, Vs, Vs')) && (Unify.unifiable (G, Us, Us'))
          then sc Ds
          else Ds
      | (GB, Lex (L), Lex (L'), sc, ac, Ds) -> ordeqs (GB, L, L', sc, ac, Ds)
      | (GB, Simul (L), Simul (L'), sc, ac, Ds) ->
          ordeqs (GB, L, L', sc, ac, Ds)
    let rec ordeqs =
      function
      | (GB, nil, nil, sc, ac, Ds) -> sc Ds
      | (GB, (O)::L, (O')::L', sc, ac, Ds) ->
          ordeq
            (GB, O, O', (function | Ds' -> ordeqs (GB, L, L', sc, ac, Ds')),
              ac, Ds)
    let rec ordle (GB, O, O', sc, ac, Ds) =
      let Ds' =
        CSManager.trail (function | () -> ordeq (GB, O, O', sc, ac, Ds)) in
      ordlt (GB, O, O', sc, ac, Ds')
    let rec skolem =
      function
      | ((du, de), GB, w, F.True, sc) -> (GB, w)
      | ((du, de), GB, w, All (Prim (D), F), sc) ->
          skolem
            (((du + 1), de), GB, w, F,
              (function
               | (s, de') ->
                   let (s', V', F') = sc (s, de') in
                   ((I.dot1 s'),
                     ((function
                       | V ->
                           V'
                             (Abstract.piDepend
                                (((Whnf.normalizeDec (D, s')), I.Meta),
                                  (Whnf.normalize (V, I.id)))))),
                     ((function
                       | F -> F' (F.All ((F.Prim (I.decSub (D, s'))), F)))))))
      | ((du, de), (G, B), w, Ex (Dec (name, V), F), sc) ->
          let (s', V', F') = sc (w, de) in
          let V1 = I.EClo (V, s') in
          let V2 = Whnf.normalize ((V' V1), I.id) in
          let F1 = F.Ex ((I.Dec (name, V1)), F.True) in
          let F2 = F' F1 in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (G, F2) else () in
          let D2 = I.Dec (NONE, V2) in
          let T2 =
            match F2 with
            | All _ -> S.Lemma S.RL
            | _ -> S.Lemma (S.Splits (!MTPGlobal.maxSplit)) in
          skolem
            ((du, (de + 1)), ((I.Decl (G, D2)), (I.Decl (B, T2))),
              (I.comp (w, I.shift)), F,
              (function
               | (s, de') ->
                   let (s', V', F') = sc (s, de') in
                   ((I.Dot
                       ((I.Exp
                           (I.Root ((I.BVar (du + (de' - de))), (spine du)))),
                         s')), V', F')))
    let rec updateState =
      function
      | (S, (nil, s)) -> S
      | ((State (n, (G, B), (IH, OH), d, O, H, F) as S),
         ((Lemma (n', Frl'))::L, s)) ->
          let ((G'', B''), s') =
            skolem
              ((0, 0), (G, B), I.id, (F.forSub (Frl', s)),
                (function
                 | (s', _) ->
                     (s', ((function | V' -> V')), ((function | F' -> F'))))) in
          let s'' = I.comp (s, s') in
          updateState
            ((S.State
                (n, (G'', B''), (IH, OH), d, (S.orderSub (O, s')),
                  ((::) (n', (F.forSub (Frl', s''))) map
                     (function | (n', F') -> (n', (F.forSub (F', s')))) H),
                  (F.forSub (F, s')))), (L, s''))
    let rec selectFormula =
      function
      | (n, (G0, All (Prim (Dec (_, V) as D), F), All (_, O)), S) ->
          selectFormula (n, ((I.Decl (G0, D)), F, O), S)
      | (n, (G0, And (F1, F2), And (O1, O2)), S) ->
          let (n', S') = selectFormula (n, (G0, F1, O1), S) in
          selectFormula (n, (G0, F2, O2), S')
      | (nih, (Gall, Fex, Oex),
         (State (ncurrent, (G0, B0), (_, _), _, Ocurrent, H, F) as S)) ->
          let Ds =
            recursion
              ((nih, Gall, Fex, Oex),
                (ncurrent, (G0, B0), nil, Ocurrent, H, F)) in
          ((nih + 1), (updateState (S, (Ds, I.id))))
    let rec expand (State (n, (G, B), (IH, OH), d, O, H, F) as S) =
      let _ = if !Global.doubleCheck then FunTypeCheck.isState S else () in
      let (_, S') = selectFormula (1, (I.Null, IH, OH), S) in S'
    let rec apply (S) =
      if !Global.doubleCheck then FunTypeCheck.isState S else (); S
    let rec menu _ =
      "Recursion (calculates ALL new assumptions & residual lemmas)"
    let rec handleExceptions f (P) =
      try f P with | Error s -> raise (Error s)
    (* Newly created *)
    (* Residual Lemma *)
    (*  spine n = S'

        Invariant:
        S' = n;..;1;Nil
     *)
    (* someEVars (G, G1, s) = s'

       Invariant:
       If  |- G ctx
       and  G |- s : G
       then G |- s' : G, G1
    *)
    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)
    (* appendCtx ((G1, B1), T, G2) = (G', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- G' = G1, G2 ctx
       and  G' |- B' tags
    *)
    (* createCtx ((G, B), ll, s) = ((G', B'), s', af')

     Invariant:
     If   |- G ctx
     and  G |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  G |- s : G1

     then |- G' : ctx
     and  G' |- B' tags
     and  G' = G, G''
     and  G' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{G''}} AF  auxFor
     *)
    (* G |- s' : G1 *)
    (* G |- G2' ctx *)
    (* . |- G' = G, G2' ctx *)
    (* G' |- s'' : G0 *)
    (* createEVars' (G, G0) = s'

       Invariant :
       If   |- G ctx
       and  |- G0 ctx
       then G |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)
    (* checkCtx (G, G2, (V, s)) = B'

       Invariant:
       If   |- G = G0, G1 ctx
       and  G |- G2 ctx
       and  G |- s : G0
       and  G0 |- V : L
       then B' holds iff
            G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
    *)
    (* checkLabels ((G', B'), V, ll, l) = lopt'

       Invariant:
       If   |- G' ctx
       and  G' |- B' ctx
       and  G' |- s : G0
       and  G0 |- V : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = NONE if no context block is applicable
       or   lopt' = SOME l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)
    (* as nil *)
    (* G' |- t : G1 *)
    (* G |- G2' ctx *)
    (*      | checkLabels _ = NONE   more than one context block is introduced *)
    (* appendRL (Ds1, Ds2) = Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)
    (* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = Ds

       Invariant:

       If

       nih  is the id or the induction hypothesis
       |- Gall ctx
       Gall |- Fex : for        (Fex doesn't contain any universal quantifiers)
       Gall |- Oex : order

       and
       ncurrent is the id of the current proof goal
       |- G0 ctx
       G0 |- B0 tags
       . |- ll label list
       G0 |- Ocurrent order
       G0 |- H history
       G0 |- F formula

       then
       G0 |- Ds decs
    *)
    (* G' |- s' : G0 *)
    (* G' |- t' : Gall *)
    (* set_parameter (GB, X, k, sc, ac, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    (* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *)
    (* ltinit (GB, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of all all possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators
    *)
    (* = I.decSub (D2, s2) *)
    (* lt (GB, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuate possible states
       and  sc is success continuation
           then Ds' is an extension of Ds, containing all
                recursion operators
    *)
    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    (*          if n <= k then   n must be a local variable *)
    (* k might not be needed any more: Check --cs *)
    (*            else Ds *)
    (* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)
    (* == I.targetFam V2' *)
    (* enforce that X gets only bound to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eq (GB, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that X can only bound to parameter *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')    BUG -cs *)
    (* ordlt (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    (* ordltLex (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    (* ordltSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    (* ordleSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    (* ordlteqs (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for all GB, Ds |- s' : GB
            returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
            and     V''  mapping (GB, Ds, G'[...] |- V  type)  to (GB, Ds |- {G'[...]} V type)
            and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)
    (* s'  :  GB, Ds |- s : GB   *)
    (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
    (* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
    (* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
    (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
    (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
    (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
    (* V   : GB, G |- V type *)
    (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
    (* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
    (* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
    (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
    (* V2  : GB, Ds |- {G'[...]} V2 : type *)
    (* F1  : GB, Ds, G'[...] |- F1 : for *)
    (* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
    (* D2  : GB, Ds |- D2 : type *)
    (* T2  : GB, Ds |- T2 : tag *)
    (* s   : GB, Ds, D2 |- s : GB *)
    (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
    (* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
    (* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)
    (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
    (* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)
    (* selectFormula (n, G, (G0, F, O), S) = S'

       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    let expand = handleExceptions expand
    let apply = apply
    let menu = menu
  end ;;
