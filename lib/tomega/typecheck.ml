module type TOMEGATYPECHECK  =
  sig
    exception Error of string 
    val checkCtx : Tomega.dec_ IntSyn.ctx_ -> unit
    val checkFor : (Tomega.dec_ IntSyn.ctx_ * Tomega.for_) -> unit
    val checkPrg :
      (Tomega.dec_ IntSyn.ctx_ * (Tomega.prg_ * Tomega.for_)) -> unit
    val checkSub :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.sub_ * Tomega.dec_ IntSyn.ctx_) ->
        unit
  end


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
      if !Global.chatter >= chlev then begin print (f ()) end
      else begin () end
  let rec normalizeHead =
    begin function
    | (Const lemma, t) -> T.Const lemma
    | (Var k, t) ->
        (begin match T.varSub (k, t) with | Idx k' -> T.Var k' end) end
let rec inferSpine (Psi, s_, Ft) = inferSpineW (Psi, s_, (T.whnfFor Ft))
let rec inferSpineW =
  begin function
  | (Psi, T.Nil, (f_, t)) -> (f_, t)
  | (Psi, AppExp (m_, s_), (All ((UDec (Dec (_, a_)), _), f_), t)) ->
      let _ = chatter 4 (begin function | () -> "[appExp" end) in
    let g_ = T.coerceCtx Psi in
    let _ = TypeCheck.typeCheck (g_, (m_, (I.EClo (a_, (T.coerceSub t))))) in
    let _ = chatter 4 (begin function | () -> "]" end) in
    inferSpine (Psi, s_, (f_, (T.Dot ((T.Exp m_), t))))
  | (Psi, AppBlock (Bidx k, s_),
     (All ((UDec (BDec (_, (cid, s))), _), f2_), t2)) ->
      let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
      let (g'_, _) = I.conDecBlock (I.sgnLookup cid') in
      let _ =
        if cid <> cid'
        then begin raise (Error "Block label incompatible") end
        else begin () end in
      let s'' = T.coerceSub (T.comp ((T.embedSub s), t2)) in
      let _ = Conv.convSub (s', s'') in
      inferSpine (Psi, s_, (f2_, (T.Dot ((T.Block (I.Bidx k)), t2))))
| (Psi, AppPrg (p_, s_), (All ((PDec (_, f1_, _, _), _), f2_), t)) ->
    let _ = checkPrg (Psi, (p_, (f1_, t))) in
    inferSpine (Psi, s_, (f2_, (T.dot1 t)))
| (Psi, _, _) -> raise (Error "applied, but not of function type.") end
let rec inferPrg =
  begin function
  | (Psi, Lam (d_, p_)) ->
      let f_ = inferPrg ((I.Decl (Psi, d_)), p_) in
      T.All ((d_, T.Explicit), f_)
  | (Psi, New (p_)) ->
      let All ((UDec (BDec _ as d_), _), f_) = inferPrg (Psi, p_) in
      TA.raiseF ((I.Decl (I.Null, d_)), (f_, I.id))
  | (Psi, PairExp (u_, p_)) ->
      let v_ = TypeCheck.infer' ((T.coerceCtx Psi), u_) in
      let f_ = inferPrg (Psi, p_) in
      T.Ex (((I.Dec (None, v_)), T.Explicit), f_)
  | (Psi, PairBlock (Bidx k, p_)) ->
      let d_ = I.ctxLookup ((T.coerceCtx Psi), k) in
      let f_ = inferPrg (Psi, p_) in T.Ex ((d_, T.Explicit), f_)
  | (Psi, PairPrg (p1_, p2_)) ->
      let f1_ = inferPrg (Psi, p1_) in
      let f2_ = inferPrg (Psi, p2_) in T.And (f1_, f2_)
  | (Psi, T.Unit) -> T.True
  | (Psi, Var k) ->
      (begin match T.ctxDec (Psi, k) with | PDec (_, f'_, _, _) -> f'_ end)
  | (Psi, Const c) -> inferLemma c
  | (Psi, Redex (p_, s_)) ->
      let f1_ = inferPrg (Psi, p_) in
      let f2_ = inferSpine (Psi, s_, (f1_, T.id)) in T.forSub f2_
  | (Psi, Rec ((PDec (_, f_, _, _) as d_), p_)) ->
      let _ = checkPrg ((I.Decl (Psi, d_)), (p_, (f_, T.id))) in f_
  | (Psi, Let ((PDec (_, f1_, _, _) as d_), p1_, p2_)) ->
      let _ = checkPrg (Psi, (p1_, (f1_, T.id))) in
      let f2_ = inferPrg ((I.Decl (Psi, d_)), p2_) in f2_ end(* Blocks T.Inst, and T.LVar excluded for now *)
let rec checkPrg (Psi, (p_, Ft)) = checkPrgW (Psi, (p_, (T.whnfFor Ft)))
let rec checkPrgW =
  begin function
  | (_, (T.Unit, (T.True, _))) ->
      let _ = chatter 4 (begin function | () -> "[true]" end) in
    ()
  | (Psi, (Const lemma, (f_, t))) ->
      convFor (Psi, ((inferLemma lemma), T.id), (f_, t))
  | (Psi, (Var k, (f_, t))) ->
      (begin match T.ctxDec (Psi, k) with
       | PDec (_, f'_, _, _) -> convFor (Psi, (f'_, T.id), (f_, t)) end)
  | (Psi,
     (Lam ((PDec (x, f1_, _, _) as d_), p_),
      (All ((PDec (x', F1', _, _), _), f2_), t))) ->
      let _ = chatter 4 (begin function | () -> "[lam[p]" end) in
    let _ = convFor (Psi, (f1_, T.id), (F1', t)) in
    let _ = chatter 4 (begin function | () -> "]" end) in
    checkPrg ((I.Decl (Psi, d_)), (p_, (f2_, (T.dot1 t))))
| (Psi, (Lam (UDec (d_), p_), (All ((UDec (d'_), _), f_), t2))) ->
    let _ = chatter 4 (begin function | () -> "[lam[u]" end) in
  let _ = Conv.convDec ((d_, I.id), (d'_, (T.coerceSub t2))) in
  let _ = chatter 4 (begin function | () -> "]" end) in
  checkPrg ((I.Decl (Psi, (T.UDec d_))), (p_, (f_, (T.dot1 t2))))
| (Psi, (PairExp (m_, p_), (Ex ((Dec (x, a_), _), f2_), t))) ->
    let _ = chatter 4 (begin function | () -> "[pair [e]" end) in
  let g_ = T.coerceCtx Psi in
  let _ = TypeCheck.typeCheck (g_, (m_, (I.EClo (a_, (T.coerceSub t))))) in
  let _ = chatter 4 (begin function | () -> "]" end) in
  checkPrg (Psi, (p_, (f2_, (T.Dot ((T.Exp m_), t)))))
| (Psi, (PairBlock (Bidx k, p_), (Ex ((BDec (_, (cid, s)), _), f2_), t))) ->
    let UDec (BDec (_, (cid', s'))) = T.ctxDec (Psi, k) in
    let (g'_, _) = I.conDecBlock (I.sgnLookup cid) in
    let _ =
      if cid' <> cid then begin raise (Error "Block label mismatch") end
      else begin () end in
    let _ =
      convSub
        (Psi, (T.embedSub s'), (T.comp ((T.embedSub s), t)),
          (T.revCoerceCtx g'_)) in
    checkPrg (Psi, (p_, (f2_, (T.Dot ((T.Block (I.Bidx k)), t)))))
| (Psi, (PairPrg (p1_, p2_), (And (f1_, f2_), t))) ->
    let _ = chatter 4 (begin function | () -> "[and" end) in
  let _ = checkPrg (Psi, (p1_, (f1_, t))) in
  let _ = chatter 4 (begin function | () -> "..." end) in
  let _ = checkPrg (Psi, (p2_, (f2_, t))) in
  let _ = chatter 4 (begin function | () -> "]" end) in ()
| (Psi, (Case (Omega), Ft)) -> checkCases (Psi, (Omega, Ft))
| (Psi, (Rec ((PDec (x, f_, _, _) as d_), p_), (f'_, t))) ->
    let _ = chatter 4 (begin function | () -> "[rec" end) in
  let _ = convFor (Psi, (f_, T.id), (f'_, t)) in
  let _ = chatter 4 (begin function | () -> "]\n" end) in
  checkPrg ((I.Decl (Psi, d_)), (p_, (f'_, t)))
| (Psi, (Let ((PDec (_, f1_, _, _) as d_), p1_, p2_), (f2_, t))) ->
    let _ = chatter 4 (begin function | () -> "[let" end) in
  let _ = checkPrg (Psi, (p1_, (f1_, T.id))) in
  let _ = chatter 4 (begin function | () -> "." end) in
  let _ = checkPrg ((I.Decl (Psi, d_)), (p2_, (f2_, (T.comp (t, T.shift))))) in
  let _ = chatter 4 (begin function | () -> "]\n" end) in ((())
    (* Psi |- F1 == F1' for *))
| (Psi, (New (Lam (UDec (BDec (_, (cid, s)) as d_), p_) as p'_), (f_, t))) ->
    let _ = chatter 5 (begin function | () -> "[new1..." end) in
  let All ((UDec (D''), _), f'_) = inferPrg (Psi, p'_) in
  let _ = chatter 5 (begin function | () -> "][new2..." end) in
  let F'' = TA.raiseF ((I.Decl (I.Null, d_)), (f'_, I.id)) in
  (((begin convFor (Psi, (F'', T.id), (f_, t));
     chatter 5 (begin function | () -> "]\n" end) end))
    (* D'' == D *))
| (Psi, (Redex (p1_, s2_), (f_, t))) ->
    let f'_ = inferPrg (Psi, p1_) in
    checkSpine (Psi, s2_, (f'_, T.id), (f_, t))
| (Psi, (Box (w_, p_), (World (w'_, f_), t))) ->
    checkPrgW (Psi, (p_, (f_, t))) end(* Psi, D |- t o ^ :: Psi' *)
(* Psi' |- F2' :: for *)(* Psi, D |- P2 :: (F2' [^]) *)
(* Psi |- P1 :: F1' *)(* Psi |- F1 :: for *)(* Psi |- F2' = F2[t] *)
(* Psi' |- F2 for *)(* Psi |- t : Psi' *)
(* Psi |- let xx :: F1 = P1 in P2 : F2' *)
let rec checkSpine =
  begin function
  | (Psi, T.Nil, (f_, t), (f'_, t')) -> convFor (Psi, (f_, t), (f'_, t'))
  | (Psi, AppExp (u_, s_), (All ((UDec (Dec (_, v_)), _), f_), t), (f'_, t'))
      ->
      (begin TypeCheck.typeCheck
               ((T.coerceCtx Psi), (u_, (I.EClo (v_, (T.coerceSub t)))));
       checkSpine (Psi, s_, (f_, (T.Dot ((T.Exp u_), t))), (f'_, t')) end)
  | (Psi, AppPrg (p_, s_), (All ((PDec (_, f1_, _, _), _), f2_), t),
     (f'_, t')) ->
      (begin checkPrgW (Psi, (p_, (f1_, t)));
       checkSpine (Psi, s_, (f2_, (T.Dot (T.Undef, t))), (f'_, t')) end)
  | (Psi, AppExp (u_, s_), (FClo (f_, t1), t), (f'_, t')) ->
      checkSpine
        (Psi, (T.AppExp (u_, s_)), (f_, (T.comp (t1, t))), (f'_, t')) end
let rec checkCases =
  begin function
  | (Psi, (Cases [], (f2_, t2))) -> ()
  | (Psi, (Cases ((Psi', t', p_)::Omega), (f2_, t2))) ->
      let _ = chatter 4 (begin function | () -> "[case... " end) in
    let _ = chatter 4 (begin function | () -> "sub... " end) in
    let _ = checkSub (Psi', t', Psi) in
    let _ = chatter 4 (begin function | () -> "prg... " end) in
    let t2' = T.comp (t2, t') in
    let _ = checkCtx Psi in
    let _ = checkCtx Psi' in
    let _ = chatter 4 (begin function | () -> "]" end) in
    let _ = checkPrg (Psi', (p_, (f2_, t2'))) in
    let _ = chatter 4 (begin function | () -> "]\n" end) in
    let _ = checkCases (Psi, ((T.Cases Omega), (f2_, t2))) in ((())
      (* Psi' |- t' :: Psi *)) end
let rec inferLemma lemma =
  begin match T.lemmaLookup lemma with
  | ForDec (_, f_) -> f_
  | ValDec (_, _, f_) -> f_ end
let rec convFor (Psi, Ft1, Ft2) =
  convForW (Psi, (T.whnfFor Ft1), (T.whnfFor Ft2))
let rec convForW =
  begin function
  | (_, (T.True, _), (T.True, _)) -> ()
  | (Psi, (All (((UDec (Dec (_, a1_)) as d_), _), f1_), t1),
     (All ((UDec (Dec (_, a2_)), _), f2_), t2)) ->
      let g_ = T.coerceCtx Psi in
      let s1 = T.coerceSub t1 in
      let s2 = T.coerceSub t2 in
      let _ = Conv.conv ((a1_, s1), (a2_, s2)) in
      let _ = TypeCheck.typeCheck (g_, ((I.EClo (a1_, s1)), (I.Uni I.Type))) in
      let _ = TypeCheck.typeCheck (g_, ((I.EClo (a2_, s2)), (I.Uni I.Type))) in
      let d'_ = T.decSub (d_, t1) in
      let _ =
        convFor ((I.Decl (Psi, d'_)), (f1_, (T.dot1 t1)), (f2_, (T.dot1 t2))) in
      ()
  | (Psi, (All (((UDec (BDec (_, (l1, s1))) as d_), _), f1_), t1),
     (All ((UDec (BDec (_, (l2, s2))), _), f2_), t2)) ->
      let _ = if l1 <> l2 then begin raise (Error "Contextblock clash") end
        else begin () end in
let (g'_, _) = I.conDecBlock (I.sgnLookup l1) in
let _ =
  convSub
    (Psi, (T.comp ((T.embedSub s1), t1)), (T.comp ((T.embedSub s2), t2)),
      (T.embedCtx g'_)) in
let d'_ = T.decSub (d_, t1) in
let _ = convFor ((I.Decl (Psi, d'_)), (f1_, (T.dot1 t1)), (f2_, (T.dot1 t2))) in
()
  | (Psi, (Ex (((Dec (_, a1_) as d_), _), f1_), t1),
     (Ex ((Dec (_, a2_), _), f2_), t2)) ->
      let g_ = T.coerceCtx Psi in
      let s1 = T.coerceSub t1 in
      let s2 = T.coerceSub t2 in
      let _ = Conv.conv ((a1_, s1), (a2_, s2)) in
      let _ = TypeCheck.typeCheck (g_, ((I.EClo (a1_, s1)), (I.Uni I.Type))) in
      let _ = TypeCheck.typeCheck (g_, ((I.EClo (a2_, s2)), (I.Uni I.Type))) in
      let d'_ = I.decSub (d_, s1) in
      let _ =
        convFor
          ((I.Decl (Psi, (T.UDec d'_))), (f1_, (T.dot1 t1)),
            (f2_, (T.dot1 t2))) in
      ()
  | (Psi, (Ex (((BDec (name, (l1, s1)) as d_), _), f1_), t1),
     (Ex ((BDec (_, (l2, s2)), _), f2_), t2)) ->
      let _ = if l1 <> l2 then begin raise (Error "Contextblock clash") end
        else begin () end in
let (g'_, _) = I.conDecBlock (I.sgnLookup l1) in
let s1 = T.coerceSub t1 in
let _ =
  convSub
    (Psi, (T.comp ((T.embedSub s1), t1)), (T.comp ((T.embedSub s2), t2)),
      (T.embedCtx g'_)) in
let d'_ = I.decSub (d_, s1) in
let _ =
  convFor
    ((I.Decl (Psi, (T.UDec d'_))), (f1_, (T.dot1 t1)), (f2_, (T.dot1 t2))) in
()
| (Psi, (And (f1_, F1'), t1), (And (f2_, F2'), t2)) ->
    let _ = convFor (Psi, (f1_, t1), (f2_, t2)) in
    let _ = convFor (Psi, (F1', t1), (F2', t2)) in ()
| (Psi, (All (((PDec (_, f1_, _, _) as d_), _), F1'), t1),
   (All ((PDec (_, f2_, _, _), _), F2'), t2)) ->
    let _ = convFor (Psi, (f1_, t1), (f2_, t2)) in
    let d'_ = T.decSub (d_, t1) in
    let _ =
      convFor ((I.Decl (Psi, d'_)), (F1', (T.dot1 t1)), (F2', (T.dot1 t2))) in
    ()
| (Psi, (World (w1_, f1_), t1), (World (w2_, f2_), t2)) ->
    let _ = convFor (Psi, (f1_, t1), (f2_, t2)) in ((())
      (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *))
| _ -> raise (Error "Typecheck error") end
let rec convSub =
  begin function
  | (g_, Shift k1, Shift k2, g'_) -> if k1 = k2 then begin () end
      else begin raise (Error "Sub not equivalent") end
  | (g_, Shift k, (Dot _ as s2), g'_) ->
      convSub (g_, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), s2, g'_)
  | (g_, (Dot _ as s1), Shift k, g'_) ->
      convSub (g_, s1, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), g'_)
  | (g_, Dot (Idx k1, s1), Dot (Idx k2, s2), Decl (g'_, _)) ->
      ((if k1 = k2 then begin convSub (g_, s1, s2, g'_) end
      else begin raise (Error "Sub not equivalent") end)
(* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *))
| (g_, Dot (Exp (m1_), s1), Dot (Exp (m2_), s2), Decl
   (g'_, UDec (Dec (_, a_)))) ->
    let _ = TypeCheck.checkConv (m1_, m2_) in
    let _ = TypeCheck.typeCheck ((T.coerceCtx g_), (m1_, a_)) in
    ((convSub (g_, s1, s2, g'_))
      (* checkConv doesn't need context G?? -- Yu Liao *))
| (g_, Dot (Block (Bidx v1), s1), Dot (Block (Bidx v2), s2), Decl
   (g'_, UDec (BDec (_, (l, s))))) ->
    let UDec (BDec (_, (l1, s11))) = T.ctxDec (g_, v1) in
    let UDec (BDec (_, (l2, s22))) = T.ctxDec (g_, v2) in
    let _ = if l1 = l2 then begin () end
      else begin raise (Error "Sub not equivalent") end in
    let _ = if l1 = l then begin () end
      else begin raise (Error "Sub not equivalent") end in
  let (G'', _) = I.conDecBlock (I.sgnLookup l) in
  let _ =
    convSub (g_, (T.embedSub s11), (T.embedSub s22), (T.revCoerceCtx G'')) in
  let _ =
    convSub (g_, (T.embedSub s11), (T.embedSub s), (T.revCoerceCtx G'')) in
  convSub (g_, s1, s2, g'_)
| (g_, Dot (Prg (p1_), s1), Dot (Prg (p2_), s2), Decl
   (g'_, PDec (_, f_, _, _))) ->
    let _ = isValue p1_ in
    let _ = isValue p2_ in
    let _ = convValue (g_, p1_, p2_, f_) in convSub (g_, s1, s2, g'_)
| (g_, Dot (Idx k1, s1), Dot (Exp (m2_), s2), Decl (g'_, UDec (Dec (_, a_))))
    ->
    let _ = TypeCheck.checkConv ((I.Root ((I.BVar k1), I.Nil)), m2_) in
    let _ = TypeCheck.typeCheck ((T.coerceCtx g_), (m2_, a_)) in
    convSub (g_, s1, s2, g'_)
| (g_, Dot (Exp (m1_), s1), Dot (Idx k2, s2), Decl (g'_, UDec (Dec (_, a_))))
    ->
    let _ = TypeCheck.checkConv (m1_, (I.Root ((I.BVar k2), I.Nil))) in
    let _ = TypeCheck.typeCheck ((T.coerceCtx g_), (m1_, a_)) in
    convSub (g_, s1, s2, g'_)
| (g_, Dot (Idx k1, s1), Dot (Prg (p2_), s2), Decl (g'_, PDec (_, f_, _, _)))
    ->
    let _ = isValue p2_ in
    let _ = convValue (g_, (T.Var k1), p2_, f_) in convSub (g_, s1, s2, g'_)
| (g_, Dot (Prg (p1_), s1), Dot (Idx k2, s2), Decl (g'_, PDec (_, f_, _, _)))
    ->
    let _ = isValue p1_ in
    let _ = convValue (g_, p1_, (T.Var k2), f_) in convSub (g_, s1, s2, g'_) end
let rec convValue (g_, p1_, p2_, f_) = ()
let rec checkFor =
  begin function
  | (Psi, (T.True, _)) -> ()
  | (Psi, (All (((PDec (_, f1_, _, _) as d_), _), f2_), t)) ->
      (begin checkFor (Psi, (f1_, t));
       checkFor ((I.Decl (Psi, d_)), (f2_, (T.dot1 t))) end)
  | (Psi, (All (((UDec (d_) as d'_), _), f_), t)) ->
      (begin TypeCheck.checkDec ((T.coerceCtx Psi), (d_, (T.coerceSub t)));
       checkFor ((I.Decl (Psi, d'_)), (f_, (T.dot1 t))) end)
  | (Psi, (Ex ((d_, _), f_), t)) ->
      (begin TypeCheck.checkDec ((T.coerceCtx Psi), (d_, (T.coerceSub t)));
       checkFor ((I.Decl (Psi, (T.UDec d_))), (f_, (T.dot1 t))) end)
| (Psi, (And (f1_, f2_), t)) ->
    (begin checkFor (Psi, (f1_, t)); checkFor (Psi, (f2_, t)) end)
| (Psi, (FClo (f_, t'), t)) -> checkFor (Psi, (f_, (T.comp (t', t))))
| (Psi, (World (w_, f_), t)) -> checkFor (Psi, (f_, t)) end
let rec checkCtx =
  begin function
  | I.Null -> ()
  | Decl (Psi, UDec (d_)) ->
      (begin checkCtx Psi; TypeCheck.checkDec ((T.coerceCtx Psi), (d_, I.id)) end)
  | Decl (Psi, PDec (_, f_, _, _)) ->
      (begin checkCtx Psi; checkFor (Psi, (f_, T.id)) end) end
let rec checkSub =
  begin function
  | (I.Null, Shift 0, I.Null) -> ()
  | (Decl (g_, d_), Shift k, I.Null) ->
      if k > 0 then begin checkSub (g_, (T.Shift (k - 1)), I.Null) end
      else begin raise (Error "Sub is not well typed!") end
  | (g_, Shift k, g'_) ->
      checkSub (g_, (T.Dot ((T.Idx (k + 1)), (T.Shift (k + 1)))), g'_)
  | (g_, Dot (Idx k, s'), Decl (g'_, UDec (Dec (_, a_)))) ->
      let _ = checkSub (g_, s', g'_) in
      let UDec (Dec (_, a'_)) = T.ctxDec (g_, k) in
      if Conv.conv ((a'_, I.id), (a_, (T.coerceSub s'))) then begin () end
        else begin raise (Error "Sub isn't well typed!") end
| (g_, Dot (Idx k, s'), Decl (g'_, UDec (BDec (l, (_, s))))) ->
    let _ = checkSub (g_, s', g'_) in
    let UDec (BDec (l1, (_, s1))) = T.ctxDec (g_, k) in
    if l <> l1 then begin raise (Error "Sub isn't well typed!") end
      else begin
        if Conv.convSub ((I.comp (s, (T.coerceSub s'))), s1)
        then begin () end
        else begin raise (Error "Sub isn't well typed!") end end
| (g_, Dot (Idx k, s), Decl (g'_, PDec (_, f'_, _, _))) ->
    let _ = checkSub (g_, s, g'_) in
    let PDec (_, f1_, _, _) = T.ctxDec (g_, k) in
    convFor (g_, (f1_, T.id), (f'_, s))
| (g_, Dot (Exp (m_), s), Decl (g'_, UDec (Dec (_, a_)))) ->
    let _ = checkSub (g_, s, g'_) in
    TypeCheck.typeCheck
      ((T.coerceCtx g_), (m_, (I.EClo (a_, (T.coerceSub s)))))
| (Psi, Dot (Prg (p_), t), Decl (Psi', PDec (_, f'_, _, _))) ->
    let _ = chatter 4 (begin function | () -> "$" end) in
  let _ = checkSub (Psi, t, Psi') in
  let _ = isValue p_ in checkPrg (Psi, (p_, (f'_, t)))
| (Psi, Dot (Block (b_), t), Decl (Psi', UDec (BDec (l2, (c, s2))))) ->
    let _ = chatter 4 (begin function | () -> "$" end) in
  let _ = checkSub (Psi, t, Psi') in
  let (g_, l_) = I.constBlock c in
  let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi'), s2, g_) in
  ((checkBlock (Psi, (b_, (c, (I.comp (s2, (T.coerceSub t)))))))
    (* Psi |- t : Psi' *)(* Psi' |- s2 : SOME variables of c *)
    (* Psi |- s2 : G *))
| (Psi, Dot _, I.Null) -> raise (Error "Sub is not well typed") end
let rec checkBlock =
  begin function
  | (Psi, (Bidx v, (c2, s2))) ->
      let UDec (BDec (l1, (c1, s1))) = T.ctxDec (Psi, v) in
      if c1 <> c2 then begin raise (Error "Sub isn't well typed!") end
        else begin if Conv.convSub (s2, s1) then begin () end
          else begin raise (Error "Sub isn't well typed!") end end
| (Psi, (Inst (UL), (c2, s2))) ->
    let (g_, l_) = I.constBlock c2 in
    let _ = TypeCheck.typeCheckSub ((T.coerceCtx Psi), s2, g_) in
    ((checkInst (Psi, UL, (1, l_, s2)))(* Psi |- s2 : G *)) end
let rec checkInst =
  begin function
  | (Psi, [], (_, [], _)) -> ()
  | (Psi, (u_)::UL, (n, (d_)::l_, s2)) ->
      let g_ = T.coerceCtx Psi in
      let Dec (_, v_) = I.decSub (d_, s2) in
      let _ = TypeCheck.typeCheck (g_, (u_, v_)) in
      checkInst (Psi, UL, ((n + 1), l_, (I.dot1 s2))) end
let rec isValue =
  begin function
  | Var _ -> ()
  | PClo (Lam _, _) -> ()
  | PairExp (m_, p_) -> isValue p_
  | PairBlock _ -> ()
  | PairPrg (p1_, p2_) -> (begin isValue p1_; isValue p2_ end) | T.Unit -> ()
  | Rec _ -> ()
  | Const lemma ->
      (begin match T.lemmaLookup lemma with
       | ForDec _ -> raise (Error "Lemma isn't a value")
       | ValDec (_, p_, _) -> isValue p_ end)
  | _ -> raise (Error "P isn't Value!") end
let rec check (Psi, (p_, f_)) = checkPrg (Psi, (p_, (f_, T.id)))
let checkPrg =
  begin function | (Psi, (p_, f_)) -> checkPrg (Psi, (p_, (f_, T.id))) end
let checkSub = checkSub
let checkFor = begin function | (Psi, f_) -> checkFor (Psi, (f_, T.id)) end
let checkCtx = checkCtx end
