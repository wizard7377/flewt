
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
          let G = T.coerceCtx Psi in
          let _ = TypeCheck.typeCheck (G, (M, (I.EClo (A, (T.coerceSub t))))) in
          let _ = chatter 4 (function | () -> "]") in
          inferSpine (Psi, S, (F, (T.Dot ((T.Exp M), t))))
      | (Psi, AppBlock (Bidx k, S),
         (All ((UDec (BDec (_, (cid, s))), _), F2), t2)) ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (G', _) = I.conDecBlock (I.sgnLookup cid') in
          let _ =
            if cid <> cid'
            then raise (Error "Block label incompatible")
            else () in
          let s'' = T.coerceSub (T.comp ((T.embedSub s), t2)) in
          let _ = Conv.convSub (s', s'') in
          inferSpine (Psi, S, (F2, (T.Dot ((T.Block (I.Bidx k)), t2))))
      | (Psi, AppPrg (P, S), (All ((PDec (_, F1, _, _), _), F2), t)) ->
          let _ = checkPrg (Psi, (P, (F1, t))) in
          inferSpine (Psi, S, (F2, (T.dot1 t)))
      | (Psi, _, _) -> raise (Error "applied, but not of function type.")
    let rec inferPrg =
      function
      | (Psi, Lam (D, P)) ->
          let F = inferPrg ((I.Decl (Psi, D)), P) in
          T.All ((D, T.Explicit), F)
      | (Psi, New (P)) ->
          let All ((UDec (BDec _ as D), _), F) = inferPrg (Psi, P) in
          TA.raiseF ((I.Decl (I.Null, D)), (F, I.id))
      | (Psi, PairExp (U, P)) ->
          let V = TypeCheck.infer' ((T.coerceCtx Psi), U) in
          let F = inferPrg (Psi, P) in
          T.Ex (((I.Dec (NONE, V)), T.Explicit), F)
      | (Psi, PairBlock (Bidx k, P)) ->
          let D = I.ctxLookup ((T.coerceCtx Psi), k) in
          let F = inferPrg (Psi, P) in T.Ex ((D, T.Explicit), F)
      | (Psi, PairPrg (P1, P2)) ->
          let F1 = inferPrg (Psi, P1) in
          let F2 = inferPrg (Psi, P2) in T.And (F1, F2)
      | (Psi, T.Unit) -> T.True
      | (Psi, Var k) ->
          (match T.ctxDec (Psi, k) with | PDec (_, F', _, _) -> F')
      | (Psi, Const c) -> inferLemma c
      | (Psi, Redex (P, S)) ->
          let F1 = inferPrg (Psi, P) in
          let F2 = inferSpine (Psi, S, (F1, T.id)) in T.forSub F2
      | (Psi, Rec ((PDec (_, F, _, _) as D), P)) ->
          let _ = checkPrg ((I.Decl (Psi, D)), (P, (F, T.id))) in F
      | (Psi, Let ((PDec (_, F1, _, _) as D), P1, P2)) ->
          let _ = checkPrg (Psi, (P1, (F1, T.id))) in
          let F2 = inferPrg ((I.Decl (Psi, D)), P2) in F2
    let rec checkPrg (Psi, (P, Ft)) = checkPrgW (Psi, (P, (T.whnfFor Ft)))
    let rec checkPrgW =
      function
      | (_, (T.Unit, (T.True, _))) ->
          let _ = chatter 4 (function | () -> "[true]") in ()
      | (Psi, (Const lemma, (F, t))) ->
          convFor (Psi, ((inferLemma lemma), T.id), (F, t))
      | (Psi, (Var k, (F, t))) ->
          (match T.ctxDec (Psi, k) with
           | PDec (_, F', _, _) -> convFor (Psi, (F', T.id), (F, t)))
      | (Psi,
         (Lam ((PDec (x, F1, _, _) as D), P),
          (All ((PDec (x', F1', _, _), _), F2), t))) ->
          let _ = chatter 4 (function | () -> "[lam[p]") in
          let _ = convFor (Psi, (F1, T.id), (F1', t)) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg ((I.Decl (Psi, D)), (P, (F2, (T.dot1 t))))
      | (Psi, (Lam (UDec (D), P), (All ((UDec (D'), _), F), t2))) ->
          let _ = chatter 4 (function | () -> "[lam[u]") in
          let _ = Conv.convDec ((D, I.id), (D', (T.coerceSub t2))) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg ((I.Decl (Psi, (T.UDec D))), (P, (F, (T.dot1 t2))))
      | (Psi, (PairExp (M, P), (Ex ((Dec (x, A), _), F2), t))) ->
          let _ = chatter 4 (function | () -> "[pair [e]") in
          let G = T.coerceCtx Psi in
          let _ = TypeCheck.typeCheck (G, (M, (I.EClo (A, (T.coerceSub t))))) in
          let _ = chatter 4 (function | () -> "]") in
          checkPrg (Psi, (P, (F2, (T.Dot ((T.Exp M), t)))))
      | (Psi, (PairBlock (Bidx k, P), (Ex ((BDec (_, (cid, s)), _), F2), t)))
          ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (G', _) = I.conDecBlock (I.sgnLookup cid) in
          let _ =
            if cid' <> cid then raise (Error "Block label mismatch") else () in
          let _ =
            convSub
              (Psi, (T.embedSub s'), (T.comp ((T.embedSub s), t)),
                (T.revCoerceCtx G')) in
          checkPrg (Psi, (P, (F2, (T.Dot ((T.Block (I.Bidx k)), t)))))
      | (Psi, (PairPrg (P1, P2), (And (F1, F2), t))) ->
          let _ = chatter 4 (function | () -> "[and") in
          let _ = checkPrg (Psi, (P1, (F1, t))) in
          let _ = chatter 4 (function | () -> "...") in
          let _ = checkPrg (Psi, (P2, (F2, t))) in
          let _ = chatter 4 (function | () -> "]") in ()
      | (Psi, (Case (Omega), Ft)) -> checkCases (Psi, (Omega, Ft))
      | (Psi, (Rec ((PDec (x, F, _, _) as D), P), (F', t))) ->
          let _ = chatter 4 (function | () -> "[rec") in
          let _ = convFor (Psi, (F, T.id), (F', t)) in
          let _ = chatter 4 (function | () -> "]\n") in
          checkPrg ((I.Decl (Psi, D)), (P, (F', t)))
      | (Psi, (Let ((PDec (_, F1, _, _) as D), P1, P2), (F2, t))) ->
          let _ = chatter 4 (function | () -> "[let") in
          let _ = checkPrg (Psi, (P1, (F1, T.id))) in
          let _ = chatter 4 (function | () -> ".") in
          let _ =
            checkPrg ((I.Decl (Psi, D)), (P2, (F2, (T.comp (t, T.shift))))) in
          let _ = chatter 4 (function | () -> "]\n") in ()
      | (Psi, (New (Lam (UDec (BDec (_, (cid, s)) as D), P) as P'), (F, t)))
          ->
          let _ = chatter 5 (function | () -> "[new1...") in
          let All ((UDec (D''), _), F') = inferPrg (Psi, P') in
          let _ = chatter 5 (function | () -> "][new2...") in
          let F'' = TA.raiseF ((I.Decl (I.Null, D)), (F', I.id)) in
          (convFor (Psi, (F'', T.id), (F, t));
           chatter 5 (function | () -> "]\n"))
      | (Psi, (Redex (P1, S2), (F, t))) ->
          let F' = inferPrg (Psi, P1) in
          checkSpine (Psi, S2, (F', T.id), (F, t))
      | (Psi, (Box (W, P), (World (W', F), t))) ->
          checkPrgW (Psi, (P, (F, t)))
    let rec checkSpine =
      function
      | (Psi, T.Nil, (F, t), (F', t')) -> convFor (Psi, (F, t), (F', t'))
      | (Psi, AppExp (U, S), (All ((UDec (Dec (_, V)), _), F), t), (F', t'))
          ->
          (TypeCheck.typeCheck
             ((T.coerceCtx Psi), (U, (I.EClo (V, (T.coerceSub t)))));
           checkSpine (Psi, S, (F, (T.Dot ((T.Exp U), t))), (F', t')))
      | (Psi, AppPrg (P, S), (All ((PDec (_, F1, _, _), _), F2), t),
         (F', t')) ->
          (checkPrgW (Psi, (P, (F1, t)));
           checkSpine (Psi, S, (F2, (T.Dot (T.Undef, t))), (F', t')))
      | (Psi, AppExp (U, S), (FClo (F, t1), t), (F', t')) ->
          checkSpine
            (Psi, (T.AppExp (U, S)), (F, (T.comp (t1, t))), (F', t'))
    let rec checkCases =
      function
      | (Psi, (Cases nil, (F2, t2))) -> ()
      | (Psi, (Cases ((Psi', t', P)::Omega), (F2, t2))) ->
          let _ = chatter 4 (function | () -> "[case... ") in
          let _ = chatter 4 (function | () -> "sub... ") in
          let _ = checkSub (Psi', t', Psi) in
          let _ = chatter 4 (function | () -> "prg... ") in
          let t2' = T.comp (t2, t') in
          let _ = checkCtx Psi in
          let _ = checkCtx Psi' in
          let _ = chatter 4 (function | () -> "]") in
          let _ = checkPrg (Psi', (P, (F2, t2'))) in
          let _ = chatter 4 (function | () -> "]\n") in
          let _ = checkCases (Psi, ((T.Cases Omega), (F2, t2))) in ()
    let rec inferLemma lemma =
      match T.lemmaLookup lemma with
      | ForDec (_, F) -> F
      | ValDec (_, _, F) -> F
    let rec convFor (Psi, Ft1, Ft2) =
      convForW (Psi, (T.whnfFor Ft1), (T.whnfFor Ft2))
    let rec convForW =
      function
      | (_, (T.True, _), (T.True, _)) -> ()
      | (Psi, (All (((UDec (Dec (_, A1)) as D), _), F1), t1),
         (All ((UDec (Dec (_, A2)), _), F2), t2)) ->
          let G = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((A1, s1), (A2, s2)) in
          let _ =
            TypeCheck.typeCheck (G, ((I.EClo (A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (G, ((I.EClo (A2, s2)), (I.Uni I.Type))) in
          let D' = T.decSub (D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, D')), (F1, (T.dot1 t1)), (F2, (T.dot1 t2))) in
          ()
      | (Psi, (All (((UDec (BDec (_, (l1, s1))) as D), _), F1), t1),
         (All ((UDec (BDec (_, (l2, s2))), _), F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (G', _) = I.conDecBlock (I.sgnLookup l1) in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx G')) in
          let D' = T.decSub (D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, D')), (F1, (T.dot1 t1)), (F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((Dec (_, A1) as D), _), F1), t1),
         (Ex ((Dec (_, A2), _), F2), t2)) ->
          let G = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((A1, s1), (A2, s2)) in
          let _ =
            TypeCheck.typeCheck (G, ((I.EClo (A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (G, ((I.EClo (A2, s2)), (I.Uni I.Type))) in
          let D' = I.decSub (D, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec D'))), (F1, (T.dot1 t1)),
                (F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((BDec (name, (l1, s1)) as D), _), F1), t1),
         (Ex ((BDec (_, (l2, s2)), _), F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (G', _) = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx G')) in
          let D' = I.decSub (D, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec D'))), (F1, (T.dot1 t1)),
                (F2, (T.dot1 t2))) in
          ()
      | (Psi, (And (F1, F1'), t1), (And (F2, F2'), t2)) ->
          let _ = convFor (Psi, (F1, t1), (F2, t2)) in
          let _ = convFor (Psi, (F1', t1), (F2', t2)) in ()
      | (Psi, (All (((PDec (_, F1, _, _) as D), _), F1'), t1),
         (All ((PDec (_, F2, _, _), _), F2'), t2)) ->
          let _ = convFor (Psi, (F1, t1), (F2, t2)) in
          let D' = T.decSub (D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, D')), (F1', (T.dot1 t1)), (F2', (T.dot1 t2))) in
          ()
      | (Psi, (World (W1, F1), t1), (World (W2, F2), t2)) ->
          let _ = convFor (Psi, (F1, t1), (F2, t2)) in ()
      | _ -> raise (Error "Typecheck error")
    let rec convSub =
      function
      | (G, Shift k1, Shift k2, G') ->
          if k1 = k2 then () else raise (Error "Sub not equivalent")
      | (G, Shift k, (Dot _ as s2), G') ->
          convSub (G, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), s2, G')
      | (G, (Dot _ as s1), Shift k, G') ->
          convSub (G, s1, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), G')
      | (G, Dot (Idx k1, s1), Dot (Idx k2, s2), Decl (G', _)) ->
          if k1 = k2
          then convSub (G, s1, s2, G')
          else raise (Error "Sub not equivalent")
      | (G, Dot (Exp (M1), s1), Dot (Exp (M2), s2), Decl
         (G', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv (M1, M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx G), (M1, A)) in
          convSub (G, s1, s2, G')
      | (G, Dot (Block (Bidx v1), s1), Dot (Block (Bidx v2), s2), Decl
         (G', UDec (BDec (_, (l, s))))) ->
          let UDec (BDec (_, (l1, s11))) = T.ctxDec (G, v1) in
          let UDec (BDec (_, (l2, s22))) = T.ctxDec (G, v2) in
          let _ = if l1 = l2 then () else raise (Error "Sub not equivalent") in
          let _ = if l1 = l then () else raise (Error "Sub not equivalent") in
          let (G'', _) = I.conDecBlock (I.sgnLookup l) in
          let _ =
            convSub
              (G, (T.embedSub s11), (T.embedSub s22), (T.revCoerceCtx G'')) in
          let _ =
            convSub
              (G, (T.embedSub s11), (T.embedSub s), (T.revCoerceCtx G'')) in
          convSub (G, s1, s2, G')
      | (G, Dot (Prg (P1), s1), Dot (Prg (P2), s2), Decl
         (G', PDec (_, F, _, _))) ->
          let _ = isValue P1 in
          let _ = isValue P2 in
          let _ = convValue (G, P1, P2, F) in convSub (G, s1, s2, G')
      | (G, Dot (Idx k1, s1), Dot (Exp (M2), s2), Decl
         (G', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv ((I.Root ((I.BVar k1), I.Nil)), M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx G), (M2, A)) in
          convSub (G, s1, s2, G')
      | (G, Dot (Exp (M1), s1), Dot (Idx k2, s2), Decl
         (G', UDec (Dec (_, A)))) ->
          let _ = TypeCheck.checkConv (M1, (I.Root ((I.BVar k2), I.Nil))) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx G), (M1, A)) in
          convSub (G, s1, s2, G')
      | (G, Dot (Idx k1, s1), Dot (Prg (P2), s2), Decl
         (G', PDec (_, F, _, _))) ->
          let _ = isValue P2 in
          let _ = convValue (G, (T.Var k1), P2, F) in convSub (G, s1, s2, G')
      | (G, Dot (Prg (P1), s1), Dot (Idx k2, s2), Decl
         (G', PDec (_, F, _, _))) ->
          let _ = isValue P1 in
          let _ = convValue (G, P1, (T.Var k2), F) in convSub (G, s1, s2, G')
    let rec convValue (G, P1, P2, F) = ()
    let rec checkFor =
      function
      | (Psi, (T.True, _)) -> ()
      | (Psi, (All (((PDec (_, F1, _, _) as D), _), F2), t)) ->
          (checkFor (Psi, (F1, t));
           checkFor ((I.Decl (Psi, D)), (F2, (T.dot1 t))))
      | (Psi, (All (((UDec (D) as D'), _), F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (D, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, D')), (F, (T.dot1 t))))
      | (Psi, (Ex ((D, _), F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (D, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, (T.UDec D))), (F, (T.dot1 t))))
      | (Psi, (And (F1, F2), t)) ->
          (checkFor (Psi, (F1, t)); checkFor (Psi, (F2, t)))
      | (Psi, (FClo (F, t'), t)) -> checkFor (Psi, (F, (T.comp (t', t))))
      | (Psi, (World (W, F), t)) -> checkFor (Psi, (F, t))
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (Psi, UDec (D)) ->
          (checkCtx Psi; TypeCheck.checkDec ((T.coerceCtx Psi), (D, I.id)))
      | Decl (Psi, PDec (_, F, _, _)) ->
          (checkCtx Psi; checkFor (Psi, (F, T.id)))
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (G, D), Shift k, I.Null) ->
          if k > 0
          then checkSub (G, (T.Shift (k - 1)), I.Null)
          else raise (Error "Sub is not well typed!")
      | (G, Shift k, G') ->
          checkSub (G, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), G')
      | (G, Dot (Idx k, s'), Decl (G', UDec (Dec (_, A)))) ->
          let _ = checkSub (G, s', G') in
          let UDec (Dec (_, A')) = T.ctxDec (G, k) in
          if Conv.conv ((A', I.id), (A, (T.coerceSub s')))
          then ()
          else raise (Error "Sub isn't well typed!")
      | (G, Dot (Idx k, s'), Decl (G', UDec (BDec (l, (_, s))))) ->
          let _ = checkSub (G, s', G') in
          let UDec (BDec (l1, (_, s1))) = T.ctxDec (G, k) in
          if l <> l1
          then raise (Error "Sub isn't well typed!")
          else
            if Conv.convSub ((I.comp (s, (T.coerceSub s'))), s1)
            then ()
            else raise (Error "Sub isn't well typed!")
      | (G, Dot (Idx k, s), Decl (G', PDec (_, F', _, _))) ->
          let _ = checkSub (G, s, G') in
          let PDec (_, F1, _, _) = T.ctxDec (G, k) in
          convFor (G, (F1, T.id), (F', s))
      | (G, Dot (Exp (M), s), Decl (G', UDec (Dec (_, A)))) ->
          let _ = checkSub (G, s, G') in
          TypeCheck.typeCheck
            ((T.coerceCtx G), (M, (I.EClo (A, (T.coerceSub s)))))
      | (Psi, Dot (Prg (P), t), Decl (Psi', PDec (_, F', _, _))) ->
          let _ = chatter 4 (function | () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let _ = isValue P in checkPrg (Psi, (P, (F', t)))
      | (Psi, Dot (Block (B), t), Decl (Psi', UDec (BDec (l2, (c, s2))))) ->
          let _ = chatter 4 (function | () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let (G, L) = I.constBlock c in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi'), s2, G) in
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
          let (G, L) = I.constBlock c2 in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi), s2, G) in
          checkInst (Psi, UL, (1, L, s2))
    let rec checkInst =
      function
      | (Psi, nil, (_, nil, _)) -> ()
      | (Psi, (U)::UL, (n, (D)::L, s2)) ->
          let G = T.coerceCtx Psi in
          let Dec (_, V) = I.decSub (D, s2) in
          let _ = TypeCheck.typeCheck (G, (U, V)) in
          checkInst (Psi, UL, ((n + 1), L, (I.dot1 s2)))
    let rec isValue =
      function
      | Var _ -> ()
      | PClo (Lam _, _) -> ()
      | PairExp (M, P) -> isValue P
      | PairBlock _ -> ()
      | PairPrg (P1, P2) -> (isValue P1; isValue P2)
      | T.Unit -> ()
      | Rec _ -> ()
      | Const lemma ->
          (match T.lemmaLookup lemma with
           | ForDec _ -> raise (Error "Lemma isn't a value")
           | ValDec (_, P, _) -> isValue P)
      | _ -> raise (Error "P isn't Value!")
    let rec check (Psi, (P, F)) = checkPrg (Psi, (P, (F, T.id)))
    (* no other cases can occur *)
    (*     inferCon (Psi, (H, t)) = (F', t')

       Invariant:
       If   Psi  |- t : Psi1
       and  Psi1 |- H : F
       then Psi  |- F'[t'] == F[t]
    *)
    (* inferSpine (Psi, (S, t1), (F, t2)) = (F', t')

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- S : F' > F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)
    (* Blocks T.Inst, and T.LVar excluded for now *)
    (* checkPrg (Psi, P, F) = ()

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff F'[t1] == F[id]
    *)
    (* Psi |- let xx :: F1 = P1 in P2 : F2' *)
    (* Psi |- t : Psi' *)
    (* Psi' |- F2 for *)
    (* Psi |- F2' = F2[t] *)
    (* Psi |- F1 :: for *)
    (* Psi |- P1 :: F1' *)
    (* Psi, D |- P2 :: (F2' [^]) *)
    (* Psi' |- F2' :: for *)
    (* Psi, D |- t o ^ :: Psi' *)
    (* Psi |- F1 == F1' for *)
    (* D'' == D *)
    (* don't forget to check if the worlds match up --cs Mon Apr 21 01:51:58 2003 *)
    (* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : F'
       and  Psi |- F' for
       then checkCases returns () iff Psi |- F' == F [t2] formula
    *)
    (* Psi' |- t' :: Psi *)
    (* convFor (Psi, (F1, t1), (F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- F1 for
    *)
    (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
    (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
    (* checkConv doesn't need context G?? -- Yu Liao *)
    (* checkSub (Psi, t, Psi') = ()

       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised
    *)
    (* Psi |- t : Psi' *)
    (* Psi' |- s2 : SOME variables of c *)
    (* Psi |- s2 : G *)
    (* Psi |- s2 : G *)
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
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) =  could lemma be a VALUE? -- Yu Liao *)
    (* ABP 1/23/03 *)
    let checkPrg = function | (Psi, (P, F)) -> checkPrg (Psi, (P, (F, T.id)))
    let checkSub = checkSub
    let checkFor = function | (Psi, F) -> checkFor (Psi, (F, T.id))
    let checkCtx = checkCtx
  end ;;
