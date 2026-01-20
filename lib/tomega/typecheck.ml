
module type TOMEGATYPECHECK  =
  sig
    exception Error of string 
    val checkCtx : Tomega.__Dec IntSyn.__Ctx -> unit
    val checkFor : Tomega.__Dec IntSyn.__Ctx -> Tomega.__For -> unit
    val checkPrg :
      Tomega.__Dec IntSyn.__Ctx -> (Tomega.__Prg * Tomega.__For) -> unit
    val checkSub :
      Tomega.__Dec IntSyn.__Ctx ->
        Tomega.__Sub -> Tomega.__Dec IntSyn.__Ctx -> unit
  end;;




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
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module S = Subordinate
    module TA = TomegaAbstract
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec normalizeHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const lemma, t) -> T.Const lemma
      | (Var k, t) -> (match T.varSub (k, t) with | Idx k' -> T.Var k')
    let rec inferSpine (Psi) (__S) (Ft) =
      inferSpineW (Psi, __S, (T.whnfFor Ft))
    let rec inferSpineW __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (Psi, T.Nil, (__F, t)) -> (__F, t)
      | (Psi, AppExp (__M, __S), (All ((UDec (Dec (_, __A)), _), __F), t)) ->
          let _ = chatter 4 (fun () -> "[appExp") in
          let __G = T.coerceCtx Psi in
          let _ =
            TypeCheck.typeCheck (__G, (__M, (I.EClo (__A, (T.coerceSub t))))) in
          let _ = chatter 4 (fun () -> "]") in
          inferSpine (Psi, __S, (__F, (T.Dot ((T.Exp __M), t))))
      | (Psi, AppBlock (Bidx k, __S),
         (All ((UDec (BDec (_, (cid, s))), _), __F2), t2)) ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (__G', _) = I.conDecBlock (I.sgnLookup cid') in
          let _ =
            if cid <> cid'
            then raise (Error "Block label incompatible")
            else () in
          let s'' = T.coerceSub (T.comp ((T.embedSub s), t2)) in
          let _ = Conv.convSub (s', s'') in
          inferSpine (Psi, __S, (__F2, (T.Dot ((T.Block (I.Bidx k)), t2))))
      | (Psi, AppPrg (__P, __S), (All ((PDec (_, __F1, _, _), _), __F2), t))
          ->
          let _ = checkPrg (Psi, (__P, (__F1, t))) in
          inferSpine (Psi, __S, (__F2, (T.dot1 t)))
      | (Psi, _, _) -> raise (Error "applied, but not of function type.")
    let rec inferPrg __5__ __6__ =
      match (__5__, __6__) with
      | (Psi, Lam (__D, __P)) ->
          let __F = inferPrg ((I.Decl (Psi, __D)), __P) in
          T.All ((__D, T.Explicit), __F)
      | (Psi, New (__P)) ->
          let All ((UDec (BDec _ as D), _), __F) = inferPrg (Psi, __P) in
          TA.raiseF ((I.Decl (I.Null, __D)), (__F, I.id))
      | (Psi, PairExp (__U, __P)) ->
          let __V = TypeCheck.infer' ((T.coerceCtx Psi), __U) in
          let __F = inferPrg (Psi, __P) in
          T.Ex (((I.Dec (None, __V)), T.Explicit), __F)
      | (Psi, PairBlock (Bidx k, __P)) ->
          let __D = I.ctxLookup ((T.coerceCtx Psi), k) in
          let __F = inferPrg (Psi, __P) in T.Ex ((__D, T.Explicit), __F)
      | (Psi, PairPrg (__P1, __P2)) ->
          let __F1 = inferPrg (Psi, __P1) in
          let __F2 = inferPrg (Psi, __P2) in T.And (__F1, __F2)
      | (Psi, T.Unit) -> T.True
      | (Psi, Var k) ->
          (match T.ctxDec (Psi, k) with | PDec (_, __F', _, _) -> __F')
      | (Psi, Const c) -> inferLemma c
      | (Psi, Redex (__P, __S)) ->
          let __F1 = inferPrg (Psi, __P) in
          let __F2 = inferSpine (Psi, __S, (__F1, T.id)) in T.forSub __F2
      | (Psi, Rec ((PDec (_, __F, _, _) as D), __P)) ->
          let _ = checkPrg ((I.Decl (Psi, __D)), (__P, (__F, T.id))) in __F
      | (Psi, Let ((PDec (_, __F1, _, _) as D), __P1, __P2)) ->
          let _ = checkPrg (Psi, (__P1, (__F1, T.id))) in
          let __F2 = inferPrg ((I.Decl (Psi, __D)), __P2) in __F2(* Blocks T.Inst, and T.LVar excluded for now *)
    let rec checkPrg (Psi) (__P, Ft) = checkPrgW (Psi, (__P, (T.whnfFor Ft)))
    let rec checkPrgW __7__ __8__ =
      match (__7__, __8__) with
      | (_, (T.Unit, (T.True, _))) ->
          let _ = chatter 4 (fun () -> "[true]") in ()
      | (Psi, (Const lemma, (__F, t))) ->
          convFor (Psi, ((inferLemma lemma), T.id), (__F, t))
      | (Psi, (Var k, (__F, t))) ->
          (match T.ctxDec (Psi, k) with
           | PDec (_, __F', _, _) -> convFor (Psi, (__F', T.id), (__F, t)))
      | (Psi,
         (Lam ((PDec (x, __F1, _, _) as D), __P),
          (All ((PDec (x', F1', _, _), _), __F2), t))) ->
          let _ = chatter 4 (fun () -> "[lam[p]") in
          let _ = convFor (Psi, (__F1, T.id), (F1', t)) in
          let _ = chatter 4 (fun () -> "]") in
          checkPrg ((I.Decl (Psi, __D)), (__P, (__F2, (T.dot1 t))))
      | (Psi, (Lam (UDec (__D), __P), (All ((UDec (__D'), _), __F), t2))) ->
          let _ = chatter 4 (fun () -> "[lam[u]") in
          let _ = Conv.convDec ((__D, I.id), (__D', (T.coerceSub t2))) in
          let _ = chatter 4 (fun () -> "]") in
          checkPrg ((I.Decl (Psi, (T.UDec __D))), (__P, (__F, (T.dot1 t2))))
      | (Psi, (PairExp (__M, __P), (Ex ((Dec (x, __A), _), __F2), t))) ->
          let _ = chatter 4 (fun () -> "[pair [e]") in
          let __G = T.coerceCtx Psi in
          let _ =
            TypeCheck.typeCheck (__G, (__M, (I.EClo (__A, (T.coerceSub t))))) in
          let _ = chatter 4 (fun () -> "]") in
          checkPrg (Psi, (__P, (__F2, (T.Dot ((T.Exp __M), t)))))
      | (Psi,
         (PairBlock (Bidx k, __P), (Ex ((BDec (_, (cid, s)), _), __F2), t)))
          ->
          let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
          let (__G', _) = I.conDecBlock (I.sgnLookup cid) in
          let _ =
            if cid' <> cid then raise (Error "Block label mismatch") else () in
          let _ =
            convSub
              (Psi, (T.embedSub s'), (T.comp ((T.embedSub s), t)),
                (T.revCoerceCtx __G')) in
          checkPrg (Psi, (__P, (__F2, (T.Dot ((T.Block (I.Bidx k)), t)))))
      | (Psi, (PairPrg (__P1, __P2), (And (__F1, __F2), t))) ->
          let _ = chatter 4 (fun () -> "[and") in
          let _ = checkPrg (Psi, (__P1, (__F1, t))) in
          let _ = chatter 4 (fun () -> "...") in
          let _ = checkPrg (Psi, (__P2, (__F2, t))) in
          let _ = chatter 4 (fun () -> "]") in ()
      | (Psi, (Case (Omega), Ft)) -> checkCases (Psi, (Omega, Ft))
      | (Psi, (Rec ((PDec (x, __F, _, _) as D), __P), (__F', t))) ->
          let _ = chatter 4 (fun () -> "[rec") in
          let _ = convFor (Psi, (__F, T.id), (__F', t)) in
          let _ = chatter 4 (fun () -> "]\n") in
          checkPrg ((I.Decl (Psi, __D)), (__P, (__F', t)))
      | (Psi, (Let ((PDec (_, __F1, _, _) as D), __P1, __P2), (__F2, t))) ->
          let _ = chatter 4 (fun () -> "[let") in
          let _ = checkPrg (Psi, (__P1, (__F1, T.id))) in
          let _ = chatter 4 (fun () -> ".") in
          let _ =
            checkPrg
              ((I.Decl (Psi, __D)), (__P2, (__F2, (T.comp (t, T.shift))))) in
          let _ = chatter 4 (fun () -> "]\n") in ((())
            (* Psi |- F1 == F1' for *))
      | (Psi,
         (New (Lam (UDec (BDec (_, (cid, s)) as D), __P) as P'), (__F, t)))
          ->
          let _ = chatter 5 (fun () -> "[new1...") in
          let All ((UDec (D''), _), __F') = inferPrg (Psi, __P') in
          let _ = chatter 5 (fun () -> "][new2...") in
          let F'' = TA.raiseF ((I.Decl (I.Null, __D)), (__F', I.id)) in
          (((convFor (Psi, (F'', T.id), (__F, t));
             chatter 5 (fun () -> "]\n")))
            (* D'' == D *))
      | (Psi, (Redex (__P1, __S2), (__F, t))) ->
          let __F' = inferPrg (Psi, __P1) in
          checkSpine (Psi, __S2, (__F', T.id), (__F, t))
      | (Psi, (Box (__W, __P), (World (__W', __F), t))) ->
          checkPrgW (Psi, (__P, (__F, t)))(* Psi, D |- t o ^ :: Psi' *)
      (* Psi' |- F2' :: for *)(* Psi, D |- P2 :: (F2' [^]) *)
      (* Psi |- P1 :: F1' *)(* Psi |- F1 :: for *)
      (* Psi |- F2' = F2[t] *)(* Psi' |- F2 for *)
      (* Psi |- t : Psi' *)(* Psi |- let xx :: F1 = P1 in P2 : F2' *)
    let rec checkSpine __9__ __10__ __11__ __12__ =
      match (__9__, __10__, __11__, __12__) with
      | (Psi, T.Nil, (__F, t), (__F', t')) ->
          convFor (Psi, (__F, t), (__F', t'))
      | (Psi, AppExp (__U, __S), (All ((UDec (Dec (_, __V)), _), __F), t),
         (__F', t')) ->
          (TypeCheck.typeCheck
             ((T.coerceCtx Psi), (__U, (I.EClo (__V, (T.coerceSub t)))));
           checkSpine (Psi, __S, (__F, (T.Dot ((T.Exp __U), t))), (__F', t')))
      | (Psi, AppPrg (__P, __S), (All ((PDec (_, __F1, _, _), _), __F2), t),
         (__F', t')) ->
          (checkPrgW (Psi, (__P, (__F1, t)));
           checkSpine (Psi, __S, (__F2, (T.Dot (T.Undef, t))), (__F', t')))
      | (Psi, AppExp (__U, __S), (FClo (__F, t1), t), (__F', t')) ->
          checkSpine
            (Psi, (T.AppExp (__U, __S)), (__F, (T.comp (t1, t))), (__F', t'))
    let rec checkCases __13__ __14__ =
      match (__13__, __14__) with
      | (Psi, (Cases nil, (__F2, t2))) -> ()
      | (Psi, (Cases ((Psi', t', __P)::Omega), (__F2, t2))) ->
          let _ = chatter 4 (fun () -> "[case... ") in
          let _ = chatter 4 (fun () -> "sub... ") in
          let _ = checkSub (Psi', t', Psi) in
          let _ = chatter 4 (fun () -> "prg... ") in
          let t2' = T.comp (t2, t') in
          let _ = checkCtx Psi in
          let _ = checkCtx Psi' in
          let _ = chatter 4 (fun () -> "]") in
          let _ = checkPrg (Psi', (__P, (__F2, t2'))) in
          let _ = chatter 4 (fun () -> "]\n") in
          let _ = checkCases (Psi, ((T.Cases Omega), (__F2, t2))) in ((())
            (* Psi' |- t' :: Psi *))
    let rec inferLemma lemma =
      match T.lemmaLookup lemma with
      | ForDec (_, __F) -> __F
      | ValDec (_, _, __F) -> __F
    let rec convFor (Psi) (Ft1) (Ft2) =
      convForW (Psi, (T.whnfFor Ft1), (T.whnfFor Ft2))
    let rec convForW __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (_, (T.True, _), (T.True, _)) -> ()
      | (Psi, (All (((UDec (Dec (_, __A1)) as D), _), __F1), t1),
         (All ((UDec (Dec (_, __A2)), _), __F2), t2)) ->
          let __G = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((__A1, s1), (__A2, s2)) in
          let _ =
            TypeCheck.typeCheck (__G, ((I.EClo (__A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (__G, ((I.EClo (__A2, s2)), (I.Uni I.Type))) in
          let __D' = T.decSub (__D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __D')), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (All (((UDec (BDec (_, (l1, s1))) as D), _), __F1), t1),
         (All ((UDec (BDec (_, (l2, s2))), _), __F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (__G', _) = I.conDecBlock (I.sgnLookup l1) in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx __G')) in
          let __D' = T.decSub (__D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __D')), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((Dec (_, __A1) as D), _), __F1), t1),
         (Ex ((Dec (_, __A2), _), __F2), t2)) ->
          let __G = T.coerceCtx Psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((__A1, s1), (__A2, s2)) in
          let _ =
            TypeCheck.typeCheck (__G, ((I.EClo (__A1, s1)), (I.Uni I.Type))) in
          let _ =
            TypeCheck.typeCheck (__G, ((I.EClo (__A2, s2)), (I.Uni I.Type))) in
          let __D' = I.decSub (__D, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec __D'))), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (Ex (((BDec (name, (l1, s1)) as D), _), __F1), t1),
         (Ex ((BDec (_, (l2, s2)), _), __F2), t2)) ->
          let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
          let (__G', _) = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          let _ =
            convSub
              (Psi, (T.comp ((T.embedSub s1), t1)),
                (T.comp ((T.embedSub s2), t2)), (T.embedCtx __G')) in
          let __D' = I.decSub (__D, s1) in
          let _ =
            convFor
              ((I.Decl (Psi, (T.UDec __D'))), (__F1, (T.dot1 t1)),
                (__F2, (T.dot1 t2))) in
          ()
      | (Psi, (And (__F1, F1'), t1), (And (__F2, F2'), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in
          let _ = convFor (Psi, (F1', t1), (F2', t2)) in ()
      | (Psi, (All (((PDec (_, __F1, _, _) as D), _), F1'), t1),
         (All ((PDec (_, __F2, _, _), _), F2'), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in
          let __D' = T.decSub (__D, t1) in
          let _ =
            convFor
              ((I.Decl (Psi, __D')), (F1', (T.dot1 t1)), (F2', (T.dot1 t2))) in
          ()
      | (Psi, (World (__W1, __F1), t1), (World (__W2, __F2), t2)) ->
          let _ = convFor (Psi, (__F1, t1), (__F2, t2)) in ((())
            (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *))
      | _ -> raise (Error "Typecheck error")
    let rec convSub __18__ __19__ __20__ __21__ =
      match (__18__, __19__, __20__, __21__) with
      | (__G, Shift k1, Shift k2, __G') ->
          if k1 = k2 then () else raise (Error "Sub not equivalent")
      | (__G, Shift k, (Dot _ as s2), __G') ->
          convSub
            (__G, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), s2, __G')
      | (__G, (Dot _ as s1), Shift k, __G') ->
          convSub
            (__G, s1, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), __G')
      | (__G, Dot (Idx k1, s1), Dot (Idx k2, s2), Decl (__G', _)) ->
          ((if k1 = k2
            then convSub (__G, s1, s2, __G')
            else raise (Error "Sub not equivalent"))
          (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *))
      | (__G, Dot (Exp (__M1), s1), Dot (Exp (__M2), s2), Decl
         (__G', UDec (Dec (_, __A)))) ->
          let _ = TypeCheck.checkConv (__M1, __M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __G), (__M1, __A)) in
          ((convSub (__G, s1, s2, __G'))
            (* checkConv doesn't need context G?? -- Yu Liao *))
      | (__G, Dot (Block (Bidx v1), s1), Dot (Block (Bidx v2), s2), Decl
         (__G', UDec (BDec (_, (l, s))))) ->
          let UDec (BDec (_, (l1, s11))) = T.ctxDec (__G, v1) in
          let UDec (BDec (_, (l2, s22))) = T.ctxDec (__G, v2) in
          let _ = if l1 = l2 then () else raise (Error "Sub not equivalent") in
          let _ = if l1 = l then () else raise (Error "Sub not equivalent") in
          let (G'', _) = I.conDecBlock (I.sgnLookup l) in
          let _ =
            convSub
              (__G, (T.embedSub s11), (T.embedSub s22), (T.revCoerceCtx G'')) in
          let _ =
            convSub
              (__G, (T.embedSub s11), (T.embedSub s), (T.revCoerceCtx G'')) in
          convSub (__G, s1, s2, __G')
      | (__G, Dot (Prg (__P1), s1), Dot (Prg (__P2), s2), Decl
         (__G', PDec (_, __F, _, _))) ->
          let _ = isValue __P1 in
          let _ = isValue __P2 in
          let _ = convValue (__G, __P1, __P2, __F) in
          convSub (__G, s1, s2, __G')
      | (__G, Dot (Idx k1, s1), Dot (Exp (__M2), s2), Decl
         (__G', UDec (Dec (_, __A)))) ->
          let _ = TypeCheck.checkConv ((I.Root ((I.BVar k1), I.Nil)), __M2) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __G), (__M2, __A)) in
          convSub (__G, s1, s2, __G')
      | (__G, Dot (Exp (__M1), s1), Dot (Idx k2, s2), Decl
         (__G', UDec (Dec (_, __A)))) ->
          let _ = TypeCheck.checkConv (__M1, (I.Root ((I.BVar k2), I.Nil))) in
          let _ = TypeCheck.typeCheck ((T.coerceCtx __G), (__M1, __A)) in
          convSub (__G, s1, s2, __G')
      | (__G, Dot (Idx k1, s1), Dot (Prg (__P2), s2), Decl
         (__G', PDec (_, __F, _, _))) ->
          let _ = isValue __P2 in
          let _ = convValue (__G, (T.Var k1), __P2, __F) in
          convSub (__G, s1, s2, __G')
      | (__G, Dot (Prg (__P1), s1), Dot (Idx k2, s2), Decl
         (__G', PDec (_, __F, _, _))) ->
          let _ = isValue __P1 in
          let _ = convValue (__G, __P1, (T.Var k2), __F) in
          convSub (__G, s1, s2, __G')
    let rec convValue (__G) (__P1) (__P2) (__F) = ()
    let rec checkFor __22__ __23__ =
      match (__22__, __23__) with
      | (Psi, (T.True, _)) -> ()
      | (Psi, (All (((PDec (_, __F1, _, _) as D), _), __F2), t)) ->
          (checkFor (Psi, (__F1, t));
           checkFor ((I.Decl (Psi, __D)), (__F2, (T.dot1 t))))
      | (Psi, (All (((UDec (__D) as D'), _), __F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (__D, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, __D')), (__F, (T.dot1 t))))
      | (Psi, (Ex ((__D, _), __F), t)) ->
          (TypeCheck.checkDec ((T.coerceCtx Psi), (__D, (T.coerceSub t)));
           checkFor ((I.Decl (Psi, (T.UDec __D))), (__F, (T.dot1 t))))
      | (Psi, (And (__F1, __F2), t)) ->
          (checkFor (Psi, (__F1, t)); checkFor (Psi, (__F2, t)))
      | (Psi, (FClo (__F, t'), t)) -> checkFor (Psi, (__F, (T.comp (t', t))))
      | (Psi, (World (__W, __F), t)) -> checkFor (Psi, (__F, t))
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (Psi, UDec (__D)) ->
          (checkCtx Psi; TypeCheck.checkDec ((T.coerceCtx Psi), (__D, I.id)))
      | Decl (Psi, PDec (_, __F, _, _)) ->
          (checkCtx Psi; checkFor (Psi, (__F, T.id)))
    let rec checkSub __24__ __25__ __26__ =
      match (__24__, __25__, __26__) with
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (__G, __D), Shift k, I.Null) ->
          if k > 0
          then checkSub (__G, (T.Shift (k - 1)), I.Null)
          else raise (Error "Sub is not well typed!")
      | (__G, Shift k, __G') ->
          checkSub (__G, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), __G')
      | (__G, Dot (Idx k, s'), Decl (__G', UDec (Dec (_, __A)))) ->
          let _ = checkSub (__G, s', __G') in
          let UDec (Dec (_, __A')) = T.ctxDec (__G, k) in
          if Conv.conv ((__A', I.id), (__A, (T.coerceSub s')))
          then ()
          else raise (Error "Sub isn't well typed!")
      | (__G, Dot (Idx k, s'), Decl (__G', UDec (BDec (l, (_, s))))) ->
          let _ = checkSub (__G, s', __G') in
          let UDec (BDec (l1, (_, s1))) = T.ctxDec (__G, k) in
          if l <> l1
          then raise (Error "Sub isn't well typed!")
          else
            if Conv.convSub ((I.comp (s, (T.coerceSub s'))), s1)
            then ()
            else raise (Error "Sub isn't well typed!")
      | (__G, Dot (Idx k, s), Decl (__G', PDec (_, __F', _, _))) ->
          let _ = checkSub (__G, s, __G') in
          let PDec (_, __F1, _, _) = T.ctxDec (__G, k) in
          convFor (__G, (__F1, T.id), (__F', s))
      | (__G, Dot (Exp (__M), s), Decl (__G', UDec (Dec (_, __A)))) ->
          let _ = checkSub (__G, s, __G') in
          TypeCheck.typeCheck
            ((T.coerceCtx __G), (__M, (I.EClo (__A, (T.coerceSub s)))))
      | (Psi, Dot (Prg (__P), t), Decl (Psi', PDec (_, __F', _, _))) ->
          let _ = chatter 4 (fun () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let _ = isValue __P in checkPrg (Psi, (__P, (__F', t)))
      | (Psi, Dot (Block (__B), t), Decl (Psi', UDec (BDec (l2, (c, s2)))))
          ->
          let _ = chatter 4 (fun () -> "$") in
          let _ = checkSub (Psi, t, Psi') in
          let (__G, __L) = I.constBlock c in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi'), s2, __G) in
          ((checkBlock (Psi, (__B, (c, (I.comp (s2, (T.coerceSub t)))))))
            (* Psi |- t : Psi' *)(* Psi' |- s2 : Some variables of c *)
            (* Psi |- s2 : G *))
      | (Psi, Dot _, I.Null) -> raise (Error "Sub is not well typed")
    let rec checkBlock __27__ __28__ =
      match (__27__, __28__) with
      | (Psi, (Bidx v, (c2, s2))) ->
          let UDec (BDec (l1, (c1, s1))) = T.ctxDec (Psi, v) in
          if c1 <> c2
          then raise (Error "Sub isn't well typed!")
          else
            if Conv.convSub (s2, s1)
            then ()
            else raise (Error "Sub isn't well typed!")
      | (Psi, (Inst (UL), (c2, s2))) ->
          let (__G, __L) = I.constBlock c2 in
          let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi), s2, __G) in
          ((checkInst (Psi, UL, (1, __L, s2)))
            (* Psi |- s2 : G *))
    let rec checkInst __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (Psi, nil, (_, nil, _)) -> ()
      | (Psi, (__U)::UL, (n, (__D)::__L, s2)) ->
          let __G = T.coerceCtx Psi in
          let Dec (_, __V) = I.decSub (__D, s2) in
          let _ = TypeCheck.typeCheck (__G, (__U, __V)) in
          checkInst (Psi, UL, ((n + 1), __L, (I.dot1 s2)))
    let rec isValue =
      function
      | Var _ -> ()
      | PClo (Lam _, _) -> ()
      | PairExp (__M, __P) -> isValue __P
      | PairBlock _ -> ()
      | PairPrg (__P1, __P2) -> (isValue __P1; isValue __P2)
      | T.Unit -> ()
      | Rec _ -> ()
      | Const lemma ->
          (match T.lemmaLookup lemma with
           | ForDec _ -> raise (Error "Lemma isn't a value")
           | ValDec (_, __P, _) -> isValue __P)
      | _ -> raise (Error "P isn't Value!")
    let rec check (Psi) (__P, __F) = checkPrg (Psi, (__P, (__F, T.id)))
    let checkPrg (Psi) (__P, __F) = checkPrg (Psi, (__P, (__F, T.id)))
    let checkSub = checkSub
    let checkFor (Psi) (__F) = checkFor (Psi, (__F, T.id))
    let checkCtx = checkCtx
  end ;;
