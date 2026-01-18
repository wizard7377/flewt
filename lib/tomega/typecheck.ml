
(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)
module type TOMEGATYPECHECK  =
  sig
    exception Error of string 
    val checkCtx : Tomega.__Dec IntSyn.__Ctx -> unit
    val checkFor : (Tomega.__Dec IntSyn.__Ctx * Tomega.__For) -> unit
    val checkPrg :
      (Tomega.__Dec IntSyn.__Ctx * (Tomega.__Prg * Tomega.__For)) -> unit
    val checkSub :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Sub * Tomega.__Dec IntSyn.__Ctx)
        -> unit
  end;;




(* Type checking for Tomega *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)
module TomegaTypeCheck(TomegaTypeCheck:sig
                                         module Abstract : ABSTRACT
                                         module TypeCheck : TYPECHECK
                                         module Conv : CONV
                                         module Whnf : WHNF
                                         module Print : PRINT
                                         module TomegaPrint : TOMEGAPRINT
                                         module Subordinate : SUBORDINATE
                                         module Weaken : WEAKEN
                                         module TomegaAbstract :
                                         TOMEGAABSTRACT
                                       end) : TOMEGATYPECHECK =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module S = Subordinate
    module TA = TomegaAbstract
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec normalizeHead =
      function
      | (Const lemma, t) -> T.Const lemma
      | (Var k, t) -> (match T.varSub (k, t) with | Idx k' -> T.Var k')
    let rec inferSpine (Psi, S, Ft) = inferSpineW (Psi, S, (T.whnfFor Ft))
    let rec inferSpineW =
      function
      | (Psi, T.Nil, (F, t)) -> (F, t)
      | (Psi, AppExp (M, S), (All ((UDec (Dec (_, A)), _), F), t)) ->
          let _ = chatter 4 (function | () -> "[appExp") in
          let __g = T.coerceCtx Psi in
          let _ = TypeCheck.typeCheck (__g, (M, (I.EClo (A, (T.coerceSub t))))) in
          let _ = chatter 4 (function | () -> "]") in
          inferSpine (Psi, S, (F, (T.Dot ((T.Exp M), t))))
      | (Psi, AppBlock (Bidx k, S),
         (All ((UDec (BDec (_, (cid, s))), _), __F2), t2)) ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (__g', _) = I.conDecBlock (I.sgnLookup cid') in
          let _ =
            if cid <> cid'
            then raise (Error "Block label incompatible")
            else () in
          let s'' = T.coerceSub (T.comp ((T.embedSub s), t2)) in
          let _ = Conv.convSub (s', s'') in
          inferSpine (Psi, S, (__F2, (T.Dot ((T.Block (I.Bidx k)), t2))))
      | (Psi, AppPrg (P, S), (All ((PDec (_, __F1, _, _), _), __F2), t)) ->
          let _ = checkPrg (Psi, (P, (__F1, t))) in
          inferSpine (Psi, S, (__F2, (T.dot1 t)))
      | (Psi, _, _) -> raise (Error "applied, but not of function type.")
    let rec inferPrg =
      function
      | (Psi, Lam (__d, P)) ->
          let F = inferPrg ((I.Decl (Psi, __d)), P) in
          T.All ((__d, T.Explicit), F)
      | (Psi, New (P)) ->
          let All ((UDec (BDec _ as __d), _), F) = inferPrg (Psi, P) in
          TA.raiseF ((I.Decl (I.Null, __d)), (F, I.id))
      | (Psi, PairExp (__u, P)) ->
          let __v = TypeCheck.infer' ((T.coerceCtx Psi), __u) in
          let F = inferPrg (Psi, P) in
          T.Ex (((I.Dec (None, __v)), T.Explicit), F)
      | (Psi, PairBlock (Bidx k, P)) ->
          let __d = I.ctxLookup ((T.coerceCtx Psi), k) in
          let F = inferPrg (Psi, P) in T.Ex ((__d, T.Explicit), F)
      | (Psi, PairPrg (__P1, __P2)) ->
          let __F1 = inferPrg (Psi, __P1) in
          let __F2 = inferPrg (Psi, __P2) in T.And (__F1, __F2)
      | (Psi, T.Unit) -> T.True
      | (Psi, Var k) ->
          (match T.ctxDec (Psi, k) with | PDec (_, __F', _, _) -> __F')
      | (Psi, Const c) -> inferLemma c
      | (Psi, Redex (P, S)) ->
          let __F1 = inferPrg (Psi, P) in
          let __F2 = inferSpine (Psi, S, (__F1, T.id)) in T.forSub __F2
      | (Psi, Rec ((PDec (_, F, _, _) as __d), P)) ->
          let _ = checkPrg ((I.Decl (Psi, __d)), (P, (F, T.id))) in F
      | (Psi, Let ((PDec (_, __F1, _, _) as __d), __P1, __P2)) ->
          let _ = checkPrg (Psi, (__P1, (__F1, T.id))) in
          let __F2 = inferPrg ((I.Decl (Psi, __d)), __P2) in __F2
    let rec checkPrg (Psi, (P, Ft)) = checkPrgW (Psi, (P, (T.whnfFor Ft)))
    let rec checkPrgW =
      function
      | (_, (T.Unit, (T.True, _))) ->
          let _ = chatter 4 (function | () -> "[true]") in ()
      | (Psi, (Const lemma, (F, t))) ->
          convFor (Psi, ((inferLemma lemma), T.id), (F, t))
      | (Psi, (Var k, (F, t))) ->
          (match T.ctxDec (Psi, k) with
           | PDec (_, __F', _, _) -> convFor (Psi, (__F', T.id), (F, t)))
      | (Psi,
         (Lam ((PDec (x, __F1, _, _) as __d), P),
          (All ((PDec (x', __F1', _, _), _), __F2), t))) ->
          let _ = chatter 4 (function | () -> "[lam[p]") in
          let _ = convFor (Psi, (__F1, T.id), (__F1', t)) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg ((I.Decl (Psi, __d)), (P, (__F2, (T.dot1 t))))
      | (Psi, (Lam (UDec (__d), P), (All ((UDec (__d'), _), F), t2))) ->
          let _ = chatter 4 (function | () -> "[lam[u]") in
          let _ = Conv.convDec ((__d, I.id), (__d', (T.coerceSub t2))) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg ((I.Decl (Psi, (T.UDec __d))), (P, (F, (T.dot1 t2))))
      | (Psi, (PairExp (M, P), (Ex ((Dec (x, A), _), __F2), t))) ->
          let _ = chatter 4 (function | () -> "[pair [e]") in
          let __g = T.coerceCtx Psi in
          let _ = TypeCheck.typeCheck (__g, (M, (I.EClo (A, (T.coerceSub t))))) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg (Psi, (P, (__F2, (T.Dot ((T.Exp M), t)))))
      | (Psi, (PairBlock (Bidx k, P), (Ex ((BDec (_, (cid, s)), _), __F2), t)))
          ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (__g', _) = I.conDecBlock (I.sgnLookup cid) in
          let _ =
            if cid' <> cid then raise (Error "Block label mismatch") else () in
          let _ =
            convSub
              (Psi, (T.embedSub s'), (T.comp ((T.embedSub s), t)),
                (T.revCoerceCtx __g')) in
          checkPrg (Psi, (P, (__F2, (T.Dot ((T.Block (I.Bidx k)), t)))))
      | (Psi, (PairPrg (__P1, __P2), (And (__F1, __F2), t))) ->
          let _ = chatter 4 (function | () -> "[and") in
          let _ = checkPrg (Psi, (__P1, (__F1, t))) in
          let _ = chatter 4 (function | () -> "...") in
          let _ = checkPrg (Psi, (__P2, (__F2, t))) in
          let _ = chatter 4 (function | () -> "]") in ()
      | (Psi, (Case (Omega), Ft)) -> checkCases (Psi, (Omega, Ft))
      | (Psi, (Rec ((PDec (x, F, _, _) as __d), P), (__F', t))) ->
          let _ = chatter 4 (function | () -> "[rec") in
          let _ = convFor (Psi, (F, T.id), (__F', t)) in
          let _ = chatter 4 (function | () -> "]\n") in
          checkPrg ((I.Decl (Psi, __d)), (P, (__F', t)))
      | (Psi, (Let ((PDec (_, __F1, _, _) as __d), __P1, __P2), (__F2, t))) ->
          let _ = chatter 4 (function | () -> "[let") in
          let _ = checkPrg (Psi, (__P1, (__F1, T.id))) in
          let _ = chatter 4 (function | () -> ".") in
          let _ =
            checkPrg ((I.Decl (Psi, __d)), (__P2, (__F2, (T.comp (t, T.shift))))) in
          let _ = chatter 4 (function | () -> "]\n") in ()
      | (Psi, (New (Lam (UDec (BDec (_, (cid, s)) as __d), P) as __P'), (F, t)))
          ->
          let _ = chatter 5 (function | () -> "[new1...") in
          let All ((UDec (__d''), _), __F') = inferPrg (Psi, __P') in
          let _ = chatter 5 (function | () -> "][new2...") in
          let __F'' = TA.raiseF ((I.Decl (I.Null, __d)), (__F', I.id)) in
          (convFor (Psi, (__F'', T.id), (F, t));
           chatter 5 (function | () -> "]\n"))
      | (Psi, (Redex (__P1, S2), (F, t))) ->
          let __F' = inferPrg (Psi, __P1) in
          checkSpine (Psi, S2, (__F', T.id), (F, t))
      | (Psi, (Box (W, P), (World (W', F), t))) ->
          checkPrgW (Psi, (P, (F, t)))
    let rec checkSpine =
      function
      | (Psi, T.Nil, (F, t), (__F', t')) -> convFor (Psi, (F, t), (__F', t'))
      | (Psi, AppExp (__u, S), (All ((UDec (Dec (_, __v)), _), F), t), (__F', t'))
          ->
          (TypeCheck.typeCheck
             ((T.coerceCtx Psi), (__u, (I.EClo (__v, (T.coerceSub t)))));
           checkSpine (Psi, S, (F, (T.Dot ((T.Exp __u), t))), (__F', t')))
      | (Psi, AppPrg (P, S), (All ((PDec (_, __F1, _, _), _), __F2), t),
         (__F', t')) ->
          (checkPrgW (Psi, (P, (__F1, t)));
           checkSpine (Psi, S, (__F2, (T.Dot (T.Undef, t))), (__F', t')))
      | (Psi, AppExp (__u, S), (FClo (F, t1), t), (__F', t')) ->
          checkSpine
            (Psi, (T.AppExp (__u, S)), (F, (T.comp (t1, t))), (__F', t'))
    let rec checkCases =
      function
      | (Psi, (Cases nil, (__F2, t2))) -> ()
      | (Psi, (Cases ((Psi', t', P)::Omega), (__F2, t2))) ->
          let _ = chatter 4 (function | () -> "[case... ") in
          let _ = chatter 4 (function | () -> "sub... ") in
          let _ = checkSub (Psi', t', Psi) in
          let _ = chatter 4 (function | () -> "prg... ") in
          let t2' = T.comp (t2, t') in
          let _ = checkCtx Psi in
          let _ = checkCtx Psi' in
          let _ = chatter 4 (function | () -> "]") in
          let _ = checkPrg (Psi', (P, (__F2, t2'))) in
          let _ = chatter 4 (function | () -> "]\n") in
          let _ = checkCases (Psi, ((T.Cases Omega), (__F2, t2))) in ()
    let rec inferLemma lemma =
      match T.lemmaLookup lemma with
      | ForDec (_, F) -> F
      | ValDec (_, _, F) -> F
    let rec convFor (Psi, Ft1, Ft2) =
      convForW (Psi, (T.whnfFor Ft1), (T.whnfFor Ft2))
    let rec convForW =
      function
      | (_, (T.True, _), (T.True, _)) -> ()
      | (Psi, (All (((UDec (Dec (_, A1)) as __d), _), __F1), t1),
         (All ((UDec (Dec (_, A2)), _), __F2), t2)) ->
          let __g = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((A1, s1), (A2, s2)) in
          let _ =
            TypeCheck.typeCheck (__g, ((I.EClo (A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (__g, ((I.EClo (A2, s2)), (I.Uni I.Type))) in
          let __d' = T.decSub (__d, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __d')), (__F1, (T.dot1 t1)), (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (All (((UDec (BDec (_, (l1, s1))) as __d), _), __F1), t1),
         (All ((UDec (BDec (_, (l2, s2))), _), __F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (__g', _) = I.conDecBlock (I.sgnLookup l1) in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx __g')) in
          let __d' = T.decSub (__d, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __d')), (__F1, (T.dot1 t1)), (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((Dec (_, A1) as __d), _), __F1), t1),
         (Ex ((Dec (_, A2), _), __F2), t2)) ->
          let __g = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((A1, s1), (A2, s2)) in
          let _ =
            TypeCheck.typeCheck (__g, ((I.EClo (A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (__g, ((I.EClo (A2, s2)), (I.Uni I.Type))) in
          let __d' = I.decSub (__d, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec __d'))), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((BDec (name, (l1, s1)) as __d), _), __F1), t1),
         (Ex ((BDec (_, (l2, s2)), _), __F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (__g', _) = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx __g')) in
          let __d' = I.decSub (__d, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec __d'))), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (And (__F1, __F1'), t1), (And (__F2, __F2'), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in
          let _ = convFor (Psi, (__F1', t1), (__F2', t2)) in ()
      | (Psi, (All (((PDec (_, __F1, _, _) as __d), _), __F1'), t1),
         (All ((PDec (_, __F2, _, _), _), __F2'), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in
          let __d' = T.decSub (__d, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __d')), (__F1', (T.dot1 t1)), (__F2', (T.dot1 t2))) in
          ()
      | (Psi, (World (W1, __F1), t1), (World (W2, __F2), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in ()
      | _ -> raise (Error "Typecheck error")
    let rec convSub =
      function
      | (__g, Shift k1, Shift k2, __g') ->
          if k1 = k2 then () else raise (Error "Sub not equivalent")
      | (__g, Shift k, (Dot _ as s2), __g') ->
          convSub (__g, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), s2, __g')
      | (__g, (Dot _ as s1), Shift k, __g') ->
          convSub (__g, s1, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), __g')
      | (__g, Dot (Idx k1, s1), Dot (Idx k2, s2), Decl (__g', _)) ->
          if k1 = k2
          then convSub (__g, s1, s2, __g')
          else raise (Error "Sub not equivalent")
      | (__g, Dot (Exp (M1), s1), Dot (Exp (M2), s2), Decl
         (__g', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv (M1, M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __g), (M1, A)) in
          convSub (__g, s1, s2, __g')
      | (__g, Dot (Block (Bidx v1), s1), Dot (Block (Bidx v2), s2), Decl
         (__g', UDec (BDec (_, (l, s))))) ->
          let UDec (BDec (_, (l1, s11))) = T.ctxDec (__g, v1) in
          let UDec (BDec (_, (l2, s22))) = T.ctxDec (__g, v2) in
          let _ = if l1 = l2 then () else raise (Error "Sub not equivalent") in
          let _ = if l1 = l then () else raise (Error "Sub not equivalent") in
          let (__g'', _) = I.conDecBlock (I.sgnLookup l) in
          let _ =
            convSub
              (__g, (T.embedSub s11), (T.embedSub s22), (T.revCoerceCtx __g'')) in
          let _ =
            convSub
              (__g, (T.embedSub s11), (T.embedSub s), (T.revCoerceCtx __g'')) in
          convSub (__g, s1, s2, __g')
      | (__g, Dot (Prg (__P1), s1), Dot (Prg (__P2), s2), Decl
         (__g', PDec (_, F, _, _))) ->
          let _ = isValue __P1 in
          let _ = isValue __P2 in
          let _ = convValue (__g, __P1, __P2, F) in convSub (__g, s1, s2, __g')
      | (__g, Dot (Idx k1, s1), Dot (Exp (M2), s2), Decl
         (__g', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv ((I.Root ((I.BVar k1), I.Nil)), M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __g), (M2, A)) in
          convSub (__g, s1, s2, __g')
      | (__g, Dot (Exp (M1), s1), Dot (Idx k2, s2), Decl
         (__g', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv (M1, (I.Root ((I.BVar k2), I.Nil))) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __g), (M1, A)) in
          convSub (__g, s1, s2, __g')
      | (__g, Dot (Idx k1, s1), Dot (Prg (__P2), s2), Decl
         (__g', PDec (_, F, _, _))) ->
          let _ = isValue __P2 in
          let _ = convValue (__g, (T.Var k1), __P2, F) in convSub (__g, s1, s2, __g')
      | (__g, Dot (Prg (__P1), s1), Dot (Idx k2, s2), Decl
         (__g', PDec (_, F, _, _))) ->
          let _ = isValue __P1 in
          let _ = convValue (__g, __P1, (T.Var k2), F) in convSub (__g, s1, s2, __g')
    let rec convValue (__g, __P1, __P2, F) = ()
    let rec checkFor =
      function
      | (Psi, (T.True, _)) -> ()
      | (Psi, (All (((PDec (_, __F1, _, _) as __d), _), __F2), t)) ->
          (checkFor (Psi, (__F1, t));
           checkFor ((I.Decl (Psi, __d)), (__F2, (T.dot1 t))))
      | (Psi, (All (((UDec (__d) as __d'), _), F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (__d, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, __d')), (F, (T.dot1 t))))
      | (Psi, (Ex ((__d, _), F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (__d, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, (T.UDec __d))), (F, (T.dot1 t))))
      | (Psi, (And (__F1, __F2), t)) ->
          (checkFor (Psi, (__F1, t)); checkFor (Psi, (__F2, t)))
      | (Psi, (FClo (F, t'), t)) -> checkFor (Psi, (F, (T.comp (t', t))))
      | (Psi, (World (W, F), t)) -> checkFor (Psi, (F, t))
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (Psi, UDec (__d)) ->
          (checkCtx Psi; TypeCheck.checkDec ((T.coerceCtx Psi), (__d, I.id)))
      | Decl (Psi, PDec (_, F, _, _)) ->
          (checkCtx Psi; checkFor (Psi, (F, T.id)))
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (__g, __d), Shift k, I.Null) ->
          if k > 0
          then checkSub (__g, (T.Shift (k - 1)), I.Null)
          else raise (Error "Sub is not well typed!")
      | (__g, Shift k, __g') ->
          checkSub (__g, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), __g')
      | (__g, Dot (Idx k, s'), Decl (__g', UDec (Dec (_, A)))) ->
          let _ = checkSub (__g, s', __g') in
          let UDec (Dec (_, A')) = T.ctxDec (__g, k) in
          if Conv.conv ((A', I.id), (A, (T.coerceSub s')))
          then ()
          else raise (Error "Sub isn't well typed!")
      | (__g, Dot (Idx k, s'), Decl (__g', UDec (BDec (l, (_, s))))) ->
          let _ = checkSub (__g, s', __g') in
          let UDec (BDec (l1, (_, s1))) = T.ctxDec (__g, k) in
          if l <> l1
          then raise (Error "Sub isn't well typed!")
          else
            if Conv.convSub ((I.comp (s, (T.coerceSub s'))), s1)
            then ()
            else raise (Error "Sub isn't well typed!")
      | (__g, Dot (Idx k, s), Decl (__g', PDec (_, __F', _, _))) ->
          let _ = checkSub (__g, s, __g') in
          let PDec (_, __F1, _, _) = T.ctxDec (__g, k) in
          convFor (__g, (__F1, T.id), (__F', s))
      | (__g, Dot (Exp (M), s), Decl (__g', UDec (Dec (_, A)))) ->
          let _ = checkSub (__g, s, __g') in
          TypeCheck.typeCheck
            ((T.coerceCtx __g), (M, (I.EClo (A, (T.coerceSub s)))))
      | (Psi, Dot (Prg (P), t), Decl (Psi', PDec (_, __F', _, _))) ->
          let _ = chatter 4 (function | () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let _ = isValue P in checkPrg (Psi, (P, (__F', t)))
      | (Psi, Dot (Block (B), t), Decl (Psi', UDec (BDec (l2, (c, s2))))) ->
          let _ = chatter 4 (function | () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let (__g, __l) = I.constBlock c in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi'), s2, __g) in
          checkBlock (Psi, (B, (c, (I.comp (s2, (T.coerceSub t))))))
      | (Psi, Dot _, I.Null) -> raise (Error "Sub is not well typed")
    let rec checkBlock =
      function
      | (Psi, (Bidx v, (c2, s2))) ->
          let UDec (BDec (l1, (c1, s1))) = T.ctxDec (Psi, v) in
          if c1 <> c2
          then raise (Error "Sub isn't well typed!")
          else
            if Conv.convSub (s2, s1)
            then ()
            else raise (Error "Sub isn't well typed!")
      | (Psi, (Inst (UL), (c2, s2))) ->
          let (__g, __l) = I.constBlock c2 in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi), s2, __g) in
          checkInst (Psi, UL, (1, __l, s2))
    let rec checkInst =
      function
      | (Psi, nil, (_, nil, _)) -> ()
      | (Psi, (__u)::UL, (n, (__d)::__l, s2)) ->
          let __g = T.coerceCtx Psi in
          let Dec (_, __v) = I.decSub (__d, s2) in
          let _ = TypeCheck.typeCheck (__g, (__u, __v)) in
          checkInst (Psi, UL, ((n + 1), __l, (I.dot1 s2)))
    let rec isValue =
      function
      | Var _ -> ()
      | PClo (Lam _, _) -> ()
      | PairExp (M, P) -> isValue P
      | PairBlock _ -> ()
      | PairPrg (__P1, __P2) -> (isValue __P1; isValue __P2)
      | T.Unit -> ()
      | Rec _ -> ()
      | Const lemma ->
          (match T.lemmaLookup lemma with
           | ForDec _ -> raise (Error "Lemma isn't a value")
           | ValDec (_, P, _) -> isValue P)
      | _ -> raise (Error "P isn't Value!")
    let rec check (Psi, (P, F)) = checkPrg (Psi, (P, (F, T.id)))
    (* no other cases can occur *)
    (*     inferCon (Psi, (H, t)) = (__F', t')

       Invariant:
       If   Psi  |- t : Psi1
       and  Psi1 |- H : F
       then Psi  |- __F'[t'] == F[t]
    *)
    (* inferSpine (Psi, (S, t1), (F, t2)) = (__F', t')

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- S : __F' > __F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for
       and  Psi  |- __F'[t1] == F[t2]
       then Psi  |- __F''[t1] == __F'[t']
    *)
    (* Blocks T.Inst, and T.LVar excluded for now *)
    (* checkPrg (Psi, P, F) = ()

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- P : __F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff __F'[t1] == F[id]
    *)
    (* Psi |- let xx :: __F1 = __P1 in __P2 : __F2' *)
    (* Psi |- t : Psi' *)
    (* Psi' |- __F2 for *)
    (* Psi |- __F2' = __F2[t] *)
    (* Psi |- __F1 :: for *)
    (* Psi |- __P1 :: __F1' *)
    (* Psi, __d |- __P2 :: (__F2' [^]) *)
    (* Psi' |- __F2' :: for *)
    (* Psi, __d |- t o ^ :: Psi' *)
    (* Psi |- __F1 == __F1' for *)
    (* __d'' == __d *)
    (* don't forget to check if the worlds match up --cs Mon Apr 21 01:51:58 2003 *)
    (* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : __F'
       and  Psi |- __F' for
       then checkCases returns () iff Psi |- __F' == F [t2] formula
    *)
    (* Psi' |- t' :: Psi *)
    (* convFor (Psi, (__F1, t1), (__F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- __F1 for
    *)
    (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
    (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
    (* checkConv doesn't need context __g?? -- Yu Liao *)
    (* checkSub (Psi, t, Psi') = ()

       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised
    *)
    (* Psi |- t : Psi' *)
    (* Psi' |- s2 : Some variables of c *)
    (* Psi |- s2 : __g *)
    (* Psi |- s2 : __g *)
    (* Invariant:

      If   Psi |- s2 : Psi'    Psi' |-  Bn ... Bm
      and  Psi |- s : [cn :An ... cm:Am]
      and  Ai == Bi n<= i<=m
      then checkInst returns () otherwise an exception is raised.
   *)
    (*  remove later!
    and isValue (T.Lam _) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (__P1, __P2)) = (isValue __P1; isValue __P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) =  could lemma be a VALUE? -- Yu Liao *)
    (* ABP 1/23/03 *)
    let checkPrg = function | (Psi, (P, F)) -> checkPrg (Psi, (P, (F, T.id)))
    let checkSub = checkSub
    let checkFor = function | (Psi, F) -> checkFor (Psi, (F, T.id))
    let checkCtx = checkCtx
  end ;;
