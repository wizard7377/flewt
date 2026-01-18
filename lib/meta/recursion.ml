
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
      | Decl (__g, __d) ->
          if Abstract.closedDec (__g, (__d, I.id))
          then raise Domain
          else closedCtx __g
    let rec spine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1)))
    let rec someEVars =
      function
      | (__g, nil, s) -> s
      | (__g, (Dec (_, __v))::__l, s) ->
          someEVars
            (__g, __l, (I.Dot ((I.Exp (I.newEVar (__g, (I.EClo (__v, s))))), s)))
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((__d)::__g, s) -> (::) (I.decSub (__d, s)) ctxSub (__g, (I.dot1 s))
    let rec appendCtx =
      function
      | (GB1, T, nil) -> GB1
      | ((G1, B1), T, (__d)::G2) ->
          appendCtx (((I.Decl (G1, __d)), (I.Decl (B1, T))), T, G2)
    let rec createCtx =
      function
      | ((__g, B), nil, s) -> ((__g, B), s, ((function | AF -> AF)))
      | ((__g, B), n::ll, s) ->
          let LabelDec (l, G1, G2) = F.labelLookup n in
          let t = someEVars (__g, G1, I.id) in
          let G2' = ctxSub (G2, t) in
          let (__g', B') = appendCtx ((__g, B), (S.Parameter (Some n)), G2') in
          let s' = I.comp (s, (I.Shift (List.length G2'))) in
          let (GB'', s'', af'') = createCtx ((__g', B'), ll, s') in
          (GB'', s'',
            ((function
              | AF -> A.Block ((__g, t, (List.length G1), G2'), (af'' AF)))))
    let rec createEVars =
      function
      | (__g, I.Null) -> I.Shift (I.ctxLength __g)
      | (__g, Decl (G0, Dec (_, __v))) ->
          let s = createEVars (__g, G0) in
          I.Dot ((I.Exp (I.newEVar (__g, (I.EClo (__v, s))))), s)
    let rec checkCtx =
      function
      | (__g, nil, (V2, s)) -> false__
      | (__g, (Dec (_, V1) as __d)::G2, (V2, s)) ->
          (CSManager.trail
             (function | () -> Unify.unifiable (__g, (V1, I.id), (V2, s))))
            || (checkCtx ((I.Decl (__g, __d)), G2, (V2, (I.comp (s, I.shift)))))
    let rec checkLabels ((__g', B'), (__v, s), ll, l) =
      if l < 0
      then None
      else
        (let LabelDec (name, G1, G2) = F.labelLookup l in
         let s = someEVars (__g', G1, I.id) in
         let G2' = ctxSub (G2, s) in
         let t = someEVars (__g', G1, I.id) in
         let G2' = ctxSub (G2, t) in
         if
           (not (List.exists (function | l' -> l = l') ll)) &&
             (checkCtx (__g', G2', (__v, s)))
         then Some l
         else checkLabels ((__g', B'), (__v, s), ll, (l - 1)))
    let rec appendRL =
      function
      | (nil, __Ds) -> __Ds
      | ((Lemma (n, F) as __l)::Ds1, Ds2) ->
          let __Ds' = appendRL (Ds1, Ds2) in
          if
            List.exists
              (function
               | Lemma (n', __F') ->
                   (n = n') && (F.convFor ((F, I.id), (__F', I.id)))) __Ds'
          then __Ds'
          else __l :: __Ds'
    let rec recursion
      ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) =
      let ((__g', B'), s', af) = createCtx ((G0, B0), ll, I.id) in
      let t' = createEVars (__g', Gall) in
      let AF = af (A.Head (__g', (Fex, t'), (I.ctxLength Gall))) in
      let Oex' = S.orderSub (Oex, t') in
      let Ocurrent' = S.orderSub (Ocurrent, s') in
      let rec sc (__Ds) =
        let Fnew = A.abstractApproxFor AF in
        if
          List.exists
            (function
             | (nhist, Fhist) ->
                 (nih = nhist) && (F.convFor ((Fnew, I.id), (Fhist, I.id))))
            H
        then __Ds
        else (Lemma (nih, Fnew)) :: __Ds in
      let rec ac ((__g', B'), __Vs, __Ds) =
        match checkLabels ((__g', B'), __Vs, ll, ((F.labelSize ()) - 1)) with
        | None -> __Ds
        | Some l' ->
            let __Ds' =
              recursion
                ((nih, Gall, Fex, Oex),
                  (ncurrent, (G0, B0), (l' :: ll), Ocurrent, H, F)) in
            appendRL (__Ds', __Ds) in
      if ncurrent < nih
      then ordle ((__g', B'), Oex', Ocurrent', sc, ac, nil)
      else ordlt ((__g', B'), Oex', Ocurrent', sc, ac, nil)
    let rec set_parameter
      (((G1, B1) as GB), (EVar (r, _, __v, _) as x), k, sc, ac, __Ds) =
      let rec set_parameter' =
        function
        | ((I.Null, I.Null), _, __Ds) -> __Ds
        | ((Decl (__g, __d), Decl (B, Parameter _)), k, __Ds) ->
            let Dec (_, __v') as __d' = I.decSub (__d, (I.Shift k)) in
            let __Ds' =
              CSManager.trail
                (function
                 | () ->
                     if
                       (Unify.unifiable (G1, (__v, I.id), (__v', I.id))) &&
                         (Unify.unifiable
                            (G1, (x, I.id),
                              ((I.Root ((I.BVar k), I.Nil)), I.id)))
                     then sc __Ds
                     else __Ds) in
            set_parameter' ((__g, B), (k + 1), __Ds')
        | ((Decl (__g, __d), Decl (B, _)), k, __Ds) ->
            set_parameter' ((__g, B), (k + 1), __Ds) in
      set_parameter' (GB, 1, __Ds)
    let rec ltinit (GB, k, (__Us, __Vs), UsVs', sc, ac, __Ds) =
      ltinitW (GB, k, (Whnf.whnfEta (__Us, __Vs)), UsVs', sc, ac, __Ds)
    let rec ltinitW =
      function
      | (GB, k, (__Us, ((Root _, _) as __Vs)), UsVs', sc, ac, __Ds) ->
          lt (GB, k, (__Us, __Vs), UsVs', sc, ac, __Ds)
      | ((__g, B), k, ((Lam (D1, __u), s1), (Pi (D2, __v), s2)),
         ((__u', s1'), (__v', s2')), sc, ac, __Ds) ->
          ltinit
            (((I.Decl (__g, (I.decSub (D1, s1)))),
               (I.Decl (B, (S.Parameter None)))), (k + 1),
              ((__u, (I.dot1 s1)), (__v, (I.dot1 s2))),
              ((__u', (I.comp (s1', I.shift))), (__v', (I.comp (s2', I.shift)))),
              sc, ac, __Ds)
    let rec lt (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) =
      ltW (GB, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ac, __Ds)
    let rec ltW =
      function
      | (GB, k, (__Us, __Vs), ((Root (Const c, S'), s'), __Vs'), sc, ac, __Ds) ->
          ltSpine
            (GB, k, (__Us, __Vs), ((S', s'), ((I.constType c), I.id)), sc, ac,
              __Ds)
      | (((__g, B) as GB), k, (__Us, __Vs), ((Root (BVar n, S'), s'), __Vs'), sc, ac,
         __Ds) ->
          (match I.ctxLookup (B, n) with
           | Parameter _ ->
               let Dec (_, __v') = I.ctxDec (__g, n) in
               ltSpine (GB, k, (__Us, __Vs), ((S', s'), (__v', I.id)), sc, ac, __Ds)
           | Lemma _ -> __Ds)
      | (GB, _, _, ((EVar _, _), _), _, _, __Ds) -> __Ds
      | (((__g, B) as GB), k, ((__u, s1), (__v, s2)),
         ((Lam ((Dec (_, V1') as __d), __u'), s1'),
          (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, ac, __Ds) ->
          let __Ds' = __Ds in
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' =
              function | __Ds'' -> set_parameter (GB, x, k, sc, ac, __Ds'') in
            lt
              (GB, k, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', ac, __Ds')
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               lt
                 (GB, k, ((__u, s1), (__v, s2)),
                   ((__u', (I.Dot ((I.Exp x), s1'))),
                     (__v', (I.Dot ((I.Exp x), s2')))), sc, ac, __Ds'))
            else __Ds'
    let rec ltSpine (GB, k, (__Us, __Vs), (__Ss', __Vs'), sc, ac, __Ds) =
      ltSpineW (GB, k, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, ac, __Ds)
    let rec ltSpineW =
      function
      | (GB, k, (__Us, __Vs), ((I.Nil, _), _), _, _, __Ds) -> __Ds
      | (GB, k, (__Us, __Vs), ((SClo (S, s'), s''), __Vs'), sc, ac, __Ds) ->
          ltSpineW
            (GB, k, (__Us, __Vs), ((S, (I.comp (s', s''))), __Vs'), sc, ac, __Ds)
      | (GB, k, (__Us, __Vs),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ac,
         __Ds) ->
          let __Ds' = le (GB, k, (__Us, __Vs), ((__u', s1'), (V1', s2')), sc, ac, __Ds) in
          ltSpine
            (GB, k, (__Us, __Vs),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))),
              sc, ac, __Ds')
    let rec eq ((__g, B), (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) =
      CSManager.trail
        (function
         | () ->
             if
               (Unify.unifiable (__g, __Vs, __Vs')) &&
                 (Unify.unifiable (__g, __Us, __Us'))
             then sc __Ds
             else __Ds)
    let rec le (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) =
      let __Ds' = eq (GB, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) in
      leW (GB, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ac, __Ds')
    let rec leW =
      function
      | (((__g, B) as GB), k, ((__u, s1), (__v, s2)),
         ((Lam ((Dec (_, V1') as __d), __u'), s1'),
          (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, ac, __Ds) ->
          let __Ds' = ac (GB, (V1', s1'), __Ds) in
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' =
              function | __Ds'' -> set_parameter (GB, x, k, sc, ac, __Ds'') in
            le
              (GB, k, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', ac, __Ds')
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               let sc' = sc in
               let __Ds'' =
                 le
                   (GB, k, ((__u, s1), (__v, s2)),
                     ((__u', (I.Dot ((I.Exp x), s1'))),
                       (__v', (I.Dot ((I.Exp x), s2')))), sc', ac, __Ds') in
               __Ds'')
            else __Ds'
      | (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) ->
          lt (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds)
    let rec ordlt =
      function
      | (GB, Arg (UsVs), Arg (UsVs'), sc, ac, __Ds) ->
          ltinit (GB, 0, UsVs, UsVs', sc, ac, __Ds)
      | (GB, Lex (__l), Lex (__l'), sc, ac, __Ds) ->
          ordltLex (GB, __l, __l', sc, ac, __Ds)
      | (GB, Simul (__l), Simul (__l'), sc, ac, __Ds) ->
          ordltSimul (GB, __l, __l', sc, ac, __Ds)
    let rec ordltLex =
      function
      | (GB, nil, nil, sc, ac, __Ds) -> __Ds
      | (GB, (O)::__l, (O')::__l', sc, ac, __Ds) ->
          let __Ds' =
            CSManager.trail (function | () -> ordlt (GB, O, O', sc, ac, __Ds)) in
          ordeq
            (GB, O, O',
              (function | __Ds'' -> ordltLex (GB, __l, __l', sc, ac, __Ds'')), ac,
              __Ds')
    let rec ordltSimul =
      function
      | (GB, nil, nil, sc, ac, __Ds) -> __Ds
      | (GB, (O)::__l, (O')::__l', sc, ac, __Ds) ->
          let __Ds'' =
            CSManager.trail
              (function
               | () ->
                   ordlt
                     (GB, O, O',
                       (function | __Ds' -> ordleSimul (GB, __l, __l', sc, ac, __Ds')),
                       ac, __Ds)) in
          ordeq
            (GB, O, O',
              (function | __Ds' -> ordltSimul (GB, __l, __l', sc, ac, __Ds')), ac,
              __Ds'')
    let rec ordleSimul =
      function
      | (GB, nil, nil, sc, ac, __Ds) -> sc __Ds
      | (GB, (O)::__l, (O')::__l', sc, ac, __Ds) ->
          ordle
            (GB, O, O',
              (function | __Ds' -> ordleSimul (GB, __l, __l', sc, ac, __Ds')), ac,
              __Ds)
    let rec ordeq =
      function
      | ((__g, B), Arg (__Us, __Vs), Arg (__Us', __Vs'), sc, ac, __Ds) ->
          if (Unify.unifiable (__g, __Vs, __Vs')) && (Unify.unifiable (__g, __Us, __Us'))
          then sc __Ds
          else __Ds
      | (GB, Lex (__l), Lex (__l'), sc, ac, __Ds) -> ordeqs (GB, __l, __l', sc, ac, __Ds)
      | (GB, Simul (__l), Simul (__l'), sc, ac, __Ds) ->
          ordeqs (GB, __l, __l', sc, ac, __Ds)
    let rec ordeqs =
      function
      | (GB, nil, nil, sc, ac, __Ds) -> sc __Ds
      | (GB, (O)::__l, (O')::__l', sc, ac, __Ds) ->
          ordeq
            (GB, O, O', (function | __Ds' -> ordeqs (GB, __l, __l', sc, ac, __Ds')),
              ac, __Ds)
    let rec ordle (GB, O, O', sc, ac, __Ds) =
      let __Ds' =
        CSManager.trail (function | () -> ordeq (GB, O, O', sc, ac, __Ds)) in
      ordlt (GB, O, O', sc, ac, __Ds')
    let rec skolem =
      function
      | ((du, de), GB, w, F.True, sc) -> (GB, w)
      | ((du, de), GB, w, All (Prim (__d), F), sc) ->
          skolem
            (((du + 1), de), GB, w, F,
              (function
               | (s, de') ->
                   let (s', __v', __F') = sc (s, de') in
                   ((I.dot1 s'),
                     ((function
                       | __v ->
                           __v'
                             (Abstract.piDepend
                                (((Whnf.normalizeDec (__d, s')), I.Meta),
                                  (Whnf.normalize (__v, I.id)))))),
                     ((function
                       | F -> __F' (F.All ((F.Prim (I.decSub (__d, s'))), F)))))))
      | ((du, de), (__g, B), w, Ex (Dec (name, __v), F), sc) ->
          let (s', __v', __F') = sc (w, de) in
          let V1 = I.EClo (__v, s') in
          let V2 = Whnf.normalize ((__v' V1), I.id) in
          let __F1 = F.Ex ((I.Dec (name, V1)), F.True) in
          let __F2 = __F' __F1 in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (__g, __F2) else () in
          let D2 = I.Dec (None, V2) in
          let T2 =
            match __F2 with
            | All _ -> S.Lemma S.RL
            | _ -> S.Lemma (S.Splits (!MTPGlobal.maxSplit)) in
          skolem
            ((du, (de + 1)), ((I.Decl (__g, D2)), (I.Decl (B, T2))),
              (I.comp (w, I.shift)), F,
              (function
               | (s, de') ->
                   let (s', __v', __F') = sc (s, de') in
                   ((I.Dot
                       ((I.Exp
                           (I.Root ((I.BVar (du + (de' - de))), (spine du)))),
                         s')), __v', __F')))
    let rec updateState =
      function
      | (S, (nil, s)) -> S
      | ((State (n, (__g, B), (IH, OH), d, O, H, F) as S),
         ((Lemma (n', Frl'))::__l, s)) ->
          let ((__g'', B''), s') =
            skolem
              ((0, 0), (__g, B), I.id, (F.forSub (Frl', s)),
                (function
                 | (s', _) ->
                     (s', ((function | __v' -> __v')), ((function | __F' -> __F'))))) in
          let s'' = I.comp (s, s') in
          updateState
            ((S.State
                (n, (__g'', B''), (IH, OH), d, (S.orderSub (O, s')),
                  ((::) (n', (F.forSub (Frl', s''))) map
                     (function | (n', __F') -> (n', (F.forSub (__F', s')))) H),
                  (F.forSub (F, s')))), (__l, s''))
    let rec selectFormula =
      function
      | (n, (G0, All (Prim (Dec (_, __v) as __d), F), All (_, O)), S) ->
          selectFormula (n, ((I.Decl (G0, __d)), F, O), S)
      | (n, (G0, And (__F1, __F2), And (O1, O2)), S) ->
          let (n', S') = selectFormula (n, (G0, __F1, O1), S) in
          selectFormula (n, (G0, __F2, O2), S')
      | (nih, (Gall, Fex, Oex),
         (State (ncurrent, (G0, B0), (_, _), _, Ocurrent, H, F) as S)) ->
          let __Ds =
            recursion
              ((nih, Gall, Fex, Oex),
                (ncurrent, (G0, B0), nil, Ocurrent, H, F)) in
          ((nih + 1), (updateState (S, (__Ds, I.id))))
    let rec expand (State (n, (__g, B), (IH, OH), d, O, H, F) as S) =
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
    (* someEVars (__g, G1, s) = s'

       Invariant:
       If  |- __g ctx
       and  __g |- s : __g
       then __g |- s' : __g, G1
    *)
    (* ctxSub (__g, s) = __g'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- __g ctx
       then G2 |- __g' = __g[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)
    (* appendCtx ((G1, B1), T, G2) = (__g', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- __g' = G1, G2 ctx
       and  __g' |- B' tags
    *)
    (* createCtx ((__g, B), ll, s) = ((__g', B'), s', af')

     Invariant:
     If   |- __g ctx
     and  __g |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  __g |- s : G1

     then |- __g' : ctx
     and  __g' |- B' tags
     and  __g' = __g, __g''
     and  __g' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{__g''}} AF  auxFor
     *)
    (* __g |- s' : G1 *)
    (* __g |- G2' ctx *)
    (* . |- __g' = __g, G2' ctx *)
    (* __g' |- s'' : G0 *)
    (* createEVars' (__g, G0) = s'

       Invariant :
       If   |- __g ctx
       and  |- G0 ctx
       then __g |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)
    (* checkCtx (__g, G2, (__v, s)) = B'

       Invariant:
       If   |- __g = G0, G1 ctx
       and  __g |- G2 ctx
       and  __g |- s : G0
       and  G0 |- __v : __l
       then B' holds iff
            G1 = V1 .. Vn and __g, G1, V1 .. Vi-1 |- Vi unifies with __v [s o ^i] : __l
    *)
    (* checkLabels ((__g', B'), __v, ll, l) = lopt'

       Invariant:
       If   |- __g' ctx
       and  __g' |- B' ctx
       and  __g' |- s : G0
       and  G0 |- __v : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = None if no context block is applicable
       or   lopt' = Some l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)
    (* as nil *)
    (* __g' |- t : G1 *)
    (* __g |- G2' ctx *)
    (*      | checkLabels _ = None   more than one context block is introduced *)
    (* appendRL (Ds1, Ds2) = __Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       __Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)
    (* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = __Ds

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
       G0 |- __Ds decs
    *)
    (* __g' |- s' : G0 *)
    (* __g' |- t' : Gall *)
    (* set_parameter (GB, x, k, sc, ac, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating x with all possible local parameters (between 1 and k)
    *)
    (* set_parameter' ((__g, B), k, __Ds) = __Ds'

           Invariant:
           If    G1, __d < __g
        *)
    (* ltinit (GB, k, ((__U1, s1), (V2, s2)), ((__U3, s3), (V4, s4)), sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1
       and  __g |- s2 : G2   G2 |- V2 : __l
                __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  __Ds is a set of all all possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators
    *)
    (* = I.decSub (D2, s2) *)
    (* lt (GB, k, ((__u, s1), (__v, s2)), (__u', s'), sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  k is the length of the local context
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  __Ds is a set of already calculuate possible states
       and  sc is success continuation
           then __Ds' is an extension of __Ds, containing all
                recursion operators
    *)
    (* __Vs is Root!!! *)
    (* (__Us',__Vs') may not be eta-expanded!!! *)
    (*          if n <= k then   n must be a local variable *)
    (* k might not be needed any more: Check --cs *)
    (*            else __Ds *)
    (* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, __Ds) *)
    (* == I.targetFam V2' *)
    (* enforce that x gets only bound to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eq (GB, ((__u, s1), (__v, s2)), (__u', s'), sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators resulting from __u[s1] = __u'[s']
    *)
    (* le (__g, k, ((__u, s1), (__v, s2)), (__u', s'), sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
                __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  k is the length of the local context
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators resulting from __u[s1] <= __u'[s']
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that x can only bound to parameter *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (*              val sc'' = fn __Ds'' => set_parameter (GB, x, k, sc, ac, __Ds'')    BUG -cs *)
    (* ordlt (GB, O1, O2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    (* ordltLex (GB, L1, L2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    (* ordltSimul (GB, L1, L2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    (* ordleSimul (GB, L1, L2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    (* ordeq (GB, O1, O2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    (* ordlteqs (GB, L1, L2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    (* ordeq (GB, O1, O2, sc, ac, __Ds) = __Ds'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  __Ds is a set of already calculuated possible states
       and  sc is success continuation
       then __Ds' is an extension of __Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, __Ds |- w : GB
       and  GB, __g |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for all GB, __Ds |- s' : GB
            returns s''  of type  GB, __Ds, __g'[...] |- w'' : GB, __g
            and     __v''  mapping (GB, __Ds, __g'[...] |- __v  type)  to (GB, __Ds |- {__g'[...]} __v type)
            and     __F''  mapping (GB, __Ds, __g'[...] |- F) to (GB, __Ds |- {{__g'[...]}} F formula)
       then GB' = GB, __Ds'
       and  |__Ds'| = de
       and  each declaration in __Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)
    (* s'  :  GB, __Ds |- s : GB   *)
    (* s'  : GB, __Ds, __g'[...] |- s' : GB, __g *)
    (* __v'  : maps (GB, __Ds, __g'[...] |- __v type) to (GB, __Ds |- {__g'[...]} __v type) *)
    (* __F'  : maps (GB, __Ds, __g'[...] |- F for) to (GB, __Ds |- {{__g'[...]}} F for) *)
    (* _   : GB, __Ds, __g'[...], __d[?] |- _ : GB, __g, __d *)
    (* _   : maps (GB, __Ds, __g'[....], __d[?] |- __v : type) to  (GB, __Ds, |- {__g[....], __d[?]} __v : type) *)
    (* _   : maps (GB, __Ds, __g'[....], __d[?] |- F : for) to  (GB, __Ds, |- {{__g[....], __d[?]}} F : for) *)
    (* __v   : GB, __g |- __v type *)
    (* s'  : GB, __Ds, __g'[...] |- s' : GB, __g *)
    (* __v'  : maps  (GB, __Ds, __g'[...] |- __v : type)   to   (GB, __Ds |- {__g'[...]} __v : type) *)
    (* __F'  : maps  (GB, __Ds, __g'[...] |- F : for)    to   (GB, __Ds |- {{__g'[...]}} F : for) *)
    (* V1  : GB, __Ds, __g'[...] |- V1 = __v [s'] : type *)
    (* V2  : GB, __Ds |- {__g'[...]} V2 : type *)
    (* __F1  : GB, __Ds, __g'[...] |- __F1 : for *)
    (* __F2  : GB, __Ds |- {{__g'[...]}} __F2 : for *)
    (* D2  : GB, __Ds |- D2 : type *)
    (* T2  : GB, __Ds |- T2 : tag *)
    (* s   : GB, __Ds, D2 |- s : GB *)
    (* s'  : GB, __Ds, D2, __g'[...] |- s' : GB, __g *)
    (* __v'  : maps (GB, __Ds, D2, __g'[...] |- __v type) to (GB, __Ds, D2 |- {__g'[...]} __v type) *)
    (* __F'  : maps (GB, __Ds, D2, __g'[...] |- F for) to (GB, __Ds, D2 |- {{__g'[...]}} F for) *)
    (* _ : GB, __Ds, D2, __g'[...] |- s'' : GB, __g, __d *)
    (* updateState (S, (__Ds, s))

       Invariant:
       __g context
       __g' |- S state
       __g |- __Ds new decs
       __g' |- s : __g
    *)
    (* selectFormula (n, __g, (G0, F, O), S) = S'

       Invariant:
       If   __g |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    let expand = handleExceptions expand
    let apply = apply
    let menu = menu
  end ;;
