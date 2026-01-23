module type OPSEM  =
  sig
    exception NoMatch 
    val evalPrg : Tomega.prg_ -> Tomega.prg_
    val topLevel : Tomega.prg_ -> unit
    val createVarSub :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.dec_ IntSyn.ctx_) -> Tomega.sub_
    val matchSub :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.sub_ * Tomega.sub_) -> unit
  end


module Opsem(Opsem:sig
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Subordinate : SUBORDINATE
                     module TomegaTypeCheck : TOMEGATYPECHECK
                     module TomegaPrint : TOMEGAPRINT
                     module Unify : UNIFY
                   end) : OPSEM =
  struct
    module T = Tomega
    module I = IntSyn
    module S = Subordinate
    module A = Abstract
    exception Error of string 
    exception Abort 
    exception NoMatch 
    let rec matchPrg (Psi, p1_, p2_) =
      matchVal (Psi, (p1_, T.id), (T.normalizePrg (p2_, T.id)))
    let rec matchVal =
      begin function
      | (Psi, (T.Unit, _), T.Unit) -> ()
      | (Psi, (PairPrg (p1_, P1'), t1), PairPrg (p2_, P2')) ->
          (begin matchVal (Psi, (p1_, t1), p2_);
           matchVal (Psi, (P1', t1), P2') end)
      | (Psi, (PairBlock (b1_, p1_), t1), PairBlock (b2_, p2_)) ->
          (begin matchVal (Psi, (p1_, t1), p2_);
           (begin try
                    Unify.unifyBlock
                      ((T.coerceCtx Psi),
                        (I.blockSub (b1_, (T.coerceSub t1))), b2_)
            with | Unify _ -> raise NoMatch end) end)
    | (Psi, (PairExp (u1_, p1_), t1), PairExp (u2_, p2_)) ->
        (begin matchVal (Psi, (p1_, t1), p2_);
         (begin try
                  Unify.unify
                    ((T.coerceCtx Psi), (u1_, (T.coerceSub t1)), (u2_, I.id))
          with | Unify _ -> raise NoMatch end) end)
  | (Psi, (PClo (p_, t1'), t1), Pt) ->
      matchVal (Psi, (p_, (T.comp (t1', t1))), Pt)
  | (Psi, (p'_, t1), PClo (PClo (p_, t2), t3)) ->
      matchVal (Psi, (p'_, t1), (T.PClo (p_, (T.comp (t2, t3)))))
  | (Psi, (p'_, t1), PClo
     (EVar (_, ({ contents = None } as r), _, _, _, _), t2)) ->
      let iw = T.invertSub t2 in
      (((:=) r Some (T.PClo (p'_, (T.comp (t1, iw)))))
        (* ABP -- just make sure this is right *))
  | (Psi, (p'_, t1), EVar (_, ({ contents = None } as r), _, _, _, _)) ->
      (:=) r Some (T.PClo (p'_, t1))
  | (Psi, (v_, t), EVar (d_, ({ contents = Some (p_) } as r), f_, _, _, _))
      -> matchVal (Psi, (v_, t), p_) | _ -> raise NoMatch end(* ABP -- this should never occur, since we normalized it to start *)
(* ABP -- Do we need this? I added it *)(* Added by ABP *)
let rec append =
  begin function
  | (g1_, I.Null) -> g1_
  | (g1_, Decl (g2_, d_)) -> I.Decl ((append (g1_, g2_)), d_) end
let rec raisePrg =
  begin function
  | (Psi, g_, T.Unit) -> T.Unit
  | (Psi, g_, PairPrg (p1_, p2_)) ->
      let P1' = raisePrg (Psi, g_, p1_) in
      let P2' = raisePrg (Psi, g_, p2_) in T.PairPrg (P1', P2')
  | (Psi, g_, PairExp (u_, p_)) ->
      let v_ = TypeCheck.infer' ((append ((T.coerceCtx Psi), g_)), u_) in
      let w = S.weaken (g_, (I.targetFam v_)) in
      let iw = Whnf.invert w in
      let g'_ = Whnf.strengthen (iw, g_) in
      let u'_ = A.raiseTerm (g'_, (I.EClo (u_, iw))) in
      let p'_ = raisePrg (Psi, g_, p_) in ((T.PairExp (u'_, p'_))
        (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)
        (* G  |- w  : G'    *)(* G' |- iw : G     *)
        (* Psi0, G' |- B'' ctx *)) end
let rec evalPrg =
  begin function
  | (Psi, (T.Unit, t)) -> T.Unit
  | (Psi, (PairExp (m_, p_), t)) ->
      T.PairExp ((I.EClo (m_, (T.coerceSub t))), (evalPrg (Psi, (p_, t))))
  | (Psi, (PairBlock (b_, p_), t)) ->
      T.PairBlock
        ((I.blockSub (b_, (T.coerceSub t))), (evalPrg (Psi, (p_, t))))
  | (Psi, (PairPrg (p1_, p2_), t)) ->
      T.PairPrg ((evalPrg (Psi, (p1_, t))), (evalPrg (Psi, (p2_, t))))
  | (Psi, (Redex (p_, s_), t)) ->
      evalRedex (Psi, (evalPrg (Psi, (p_, t))), (s_, t))
  | (Psi, (Var k, t)) ->
      (begin match T.varSub (k, t) with
       | Prg (p_) -> evalPrg (Psi, (p_, T.id)) end)
  | (Psi, (Const lemma, t)) -> evalPrg (Psi, ((T.lemmaDef lemma), t))
  | (Psi, (Lam ((UDec (BDec _) as d_), p_), t)) ->
      let d'_ = T.decSub (d_, t) in
      T.Lam (d'_, (evalPrg ((I.Decl (Psi, d'_)), (p_, (T.dot1 t)))))
  | (Psi, (Lam (d_, p_), t)) ->
      T.Lam ((T.decSub (d_, t)), (T.PClo (p_, (T.dot1 t))))
  | (Psi, ((Rec (d_, p_) as p'_), t)) ->
      evalPrg (Psi, (p_, (T.Dot ((T.Prg (T.PClo (p'_, t))), t))))
  | (Psi, (PClo (p_, t'), t)) -> evalPrg (Psi, (p_, (T.comp (t', t))))
  | (Psi, (Case (Cases (o_)), t')) -> match_ (Psi, t', (T.Cases (rev o_)))
  | (Psi, (EVar (d_, ({ contents = Some (p_) } as r), f_, _, _, _), t)) ->
      evalPrg (Psi, (p_, t))
  | (Psi, (Let (d_, p1_, p2_), t)) ->
      let v_ = evalPrg (Psi, (p1_, t)) in
      let v'_ = evalPrg (Psi, (p2_, (T.Dot ((T.Prg v_), t)))) in v'_
  | (Psi, (New (Lam (d_, p_)), t)) ->
      let d'_ = T.decSub (d_, t) in
      let UDec (D'') = d'_ in
      let D''' = T.UDec (Names.decName ((T.coerceCtx Psi), D'')) in
      let v_ = evalPrg ((I.Decl (Psi, D''')), (p_, (T.dot1 t))) in
      let b_ = T.coerceCtx (I.Decl (I.Null, D''')) in
      let (g_, t') = T.deblockify b_ in
      let newP = raisePrg (Psi, g_, (T.normalizePrg (v_, t'))) in ((newP)
        (* unnecessary naming, remove later --cs *))
  | (Psi, (Box (w_, p_), t)) -> evalPrg (Psi, (p_, t))
  | (Psi, (Choose (p_), t)) ->
      let rec substToSpine' =
        begin function
        | (Shift n, I.Null, t_) -> t_
        | (Shift n, (Decl _ as g_), t_) ->
            substToSpine'
              ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), g_, t_)
        | (Dot (Exp (u_), s), Decl (g_, v_), t_) ->
            substToSpine' (s, g_, (T.AppExp (u_, t_)))
        | (Dot (Idx n, s), Decl (g_, Dec (_, v_)), t_) ->
            let (us_, _) =
              Whnf.whnfEta (((I.Root ((I.BVar n), I.Nil)), I.id), (v_, I.id)) in
            substToSpine' (s, g_, (T.AppExp ((I.EClo us_), t_))) end(* Eta-expand *) in
    let rec choose =
      begin function
      | (k, I.Null) -> raise Abort
      | (k, Decl (Psi', PDec _)) -> choose ((k + 1), Psi')
      | (k, Decl (Psi', UDec (Dec _))) -> choose ((k + 1), Psi')
      | (k, Decl (Psi', UDec (BDec (_, (l1, s1))))) ->
          let (Gsome, Gpi) = I.constBlock l1 in
          let s_ =
            substToSpine' (s1, Gsome, (T.AppBlock ((I.Bidx k), T.Nil))) in
          (begin try evalPrg (Psi, ((T.Redex ((T.PClo (p_, t)), s_)), T.id))
           with | Abort -> choose ((k + 1), Psi') end) end in
((choose (1, Psi))
  (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
  (* substtospine' (s, G, T) = S @ T
                If   G' |- s : G
                then G' |- S : {{G}} a >> a  for arbitrary a
                    {{G}} erases void declarations in G
              *)) end
(* reverse list O, so it looks at the
           cases in the same order it is printed
           *)
(* this is ugly.
           * don't do reverse *)
let rec match_ =
  begin function
  | (Psi, t1, Cases ((Psi', t2, p_)::c_)) ->
      let t = createVarSub (Psi, Psi') in
      let t' = T.comp (t2, t) in
      (((begin try
                 begin matchSub (Psi, t1, t');
                 evalPrg
                   (Psi, (((p_, t))(*T.normalizeSub*))) end
        with | NoMatch -> match_ (Psi, t1, (T.Cases c_)) end))
      (* val I.Null = Psi *)(* Psi |- t : Psi' *)
      (* Psi' |- t2 . shift(k) : Psi'' *)(* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *))
  | (Psi, t1, Cases []) -> raise Abort end
let rec createVarSub =
  begin function
  | (Psi, I.Null) -> T.Shift (I.ctxLength Psi)
  | (Psi, (Decl (Psi', PDec (name, f_, None, None)) as Psi'')) ->
      let t = createVarSub (Psi, Psi') in
      let t' =
        T.Dot
          ((T.Prg (T.newEVarTC (Psi, (T.forSub (f_, t)), None, None))), t) in
      t'
  | (Psi, Decl (Psi', UDec (Dec (name, v_)))) ->
      let t = createVarSub (Psi, Psi') in
      T.Dot
        ((T.Exp
            (I.EVar
               ((ref None), (T.coerceCtx Psi),
                 (I.EClo (v_, (T.coerceSub t))), (ref [])))), t)
  | (Psi, Decl (Psi', UDec (BDec (name, (cid, s))))) ->
      let t = createVarSub (Psi, Psi') in
      T.Dot
        ((T.Block
            (I.LVar ((ref None), I.id, (cid, (I.comp (s, (T.coerceSub t))))))),
          t) end
let rec matchSub =
  begin function
  | (Psi, _, Shift _) -> ()
  | (Psi, Shift n, (Dot _ as t)) ->
      matchSub (Psi, (T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), t)
  | (Psi, Dot (Exp (u1_), t1), Dot (Exp (u2_), t2)) ->
      (begin matchSub (Psi, t1, t2);
       (begin try Unify.unify ((T.coerceCtx Psi), (u1_, I.id), (u2_, I.id))
        with | Unify s -> raise NoMatch end) end)
  | (Psi, Dot (Exp (u1_), t1), Dot (Idx k, t2)) ->
      (begin matchSub (Psi, t1, t2);
       (begin try
                Unify.unify
                  ((T.coerceCtx Psi), (u1_, I.id),
                    ((I.Root ((I.BVar k), I.Nil)), I.id))
        with | Unify _ -> raise NoMatch end) end)
| (Psi, Dot (Idx k, t1), Dot (Exp (u2_), t2)) ->
    (begin matchSub (Psi, t1, t2);
     (begin try
              Unify.unify
                ((T.coerceCtx Psi), ((I.Root ((I.BVar k), I.Nil)), I.id),
                  (u2_, I.id))
      with | Unify _ -> raise NoMatch end) end)
| (Psi, Dot (Prg (p1_), t1), Dot (Prg (p2_), t2)) ->
    (begin matchSub (Psi, t1, t2); matchPrg (Psi, p1_, p2_) end)
| (Psi, Dot (Prg (p1_), t1), Dot (Idx k, t2)) ->
    (begin matchSub (Psi, t1, t2); matchPrg (Psi, p1_, (T.Var k)) end)
| (Psi, Dot (Idx k, t1), Dot (Prg (p2_), t2)) ->
    (begin matchSub (Psi, t1, t2); matchPrg (Psi, (T.Var k), p2_) end)
| (Psi, Dot (Idx k1, t1), Dot (Idx k2, t2)) ->
    if k1 = k2 then begin matchSub (Psi, t1, t2) end
    else begin raise NoMatch end
| (Psi, Dot (Idx k, t1), Dot (Block (LVar (r, s1, (c, s2))), t2)) ->
    let s1' = Whnf.invert s1 in
    let _ = (:=) r Some (I.blockSub ((I.Bidx k), s1')) in
    matchSub (Psi, t1, t2)
| (Psi, Dot (Block (b_), t1), Dot (Block (LVar (r, s1, (c, s2))), t2)) ->
    let s1' = Whnf.invert s1 in
    let _ = (:=) r Some (I.blockSub (b_, s1')) in matchSub (Psi, t1, t2) end
(* By Invariant *)
let rec evalRedex =
  begin function
  | (Psi, v_, (T.Nil, _)) -> v_
  | (Psi, v_, (SClo (s_, t1), t2)) ->
      evalRedex (Psi, v_, (s_, (T.comp (t1, t2))))
  | (Psi, Lam (UDec (Dec (_, a_)), p'_), (AppExp (u_, s_), t)) ->
      let v_ =
        evalPrg
          (Psi,
            (p'_, (T.Dot ((T.Exp (I.EClo (u_, (T.coerceSub t)))), T.id)))) in
      evalRedex (Psi, v_, (s_, t))
  | (Psi, Lam (UDec _, p'_), (AppBlock (b_, s_), t)) ->
      evalRedex
        (Psi,
          (evalPrg
             (Psi,
               (p'_,
                 (T.Dot ((T.Block (I.blockSub (b_, (T.coerceSub t)))), T.id))))),
          (s_, t))
  | (Psi, Lam (PDec _, p'_), (AppPrg (p_, s_), t)) ->
      let v_ = evalPrg (Psi, (p_, t)) in
      let v'_ = evalPrg (Psi, (p'_, (T.Dot ((T.Prg v_), T.id)))) in
      evalRedex (Psi, v'_, (s_, t)) end
let rec topLevel =
  begin function
  | (Psi, d, (T.Unit, t)) -> ()
  | (Psi, d, (Let (d'_, p1_, Case (cs_)), t)) ->
      let rec printLF arg__0 arg__1 =
        begin match (arg__0, arg__1) with
        | ((_, _, _), 0) -> ()
        | ((g_, Dot (Exp (u_), s'), Decl (g'_, Dec (Some name, v_))), k) ->
            let _ = printLF (g_, s', g'_) (k - 1) in
            print
              (((((("def " ^ name) ^ " = ") ^ (Print.expToString (g_, u_))) ^
                   " : ")
                  ^ (Print.expToString (g_, (I.EClo (v_, s')))))
                 ^ "\n") end in
    let rec match_ (Psi, t1, Cases ((Psi', t2, p_)::c_)) =
      let t = createVarSub (Psi, Psi') in
      let t' = T.comp (t2, t) in
      let m = I.ctxLength Psi' in
      let _ = matchSub (Psi, t1, t') in
      let t'' = t in
      let _ =
        printLF ((T.coerceCtx Psi), (T.coerceSub t''), (T.coerceCtx Psi'))
          (m - d) in
      ((topLevel (Psi, m, (p_, t'')))
        (* Psi |- t : Psi' *)(* Psi' |- t2 . shift(k) : Psi'' *)
        (* T.normalizeSub *)(* Psi |- t'' : Psi' *)) in
    let v_ = evalPrg (Psi, (p1_, t)) in
    let v'_ = match_ (Psi, (T.Dot ((T.Prg v_), t)), cs_) in ((v'_)
      (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *))
  | (Psi, d,
     (Let (d_, Lam ((UDec (BDec (Some name, (cid, s))) as d'_), p1_), p2_),
      t)) ->
      let _ = print (("new " ^ name) ^ "\n") in
      let D'' = T.decSub (d'_, t) in
      let _ = topLevel ((I.Decl (Psi, D'')), (d + 1), (p1_, (T.dot1 t))) in
      ()
  | (Psi, d, (Let (d_, p1_, p2_), t)) ->
      let PDec (Some name, f_, _, _) = d_ in
      let v_ = evalPrg (Psi, (p1_, t)) in
      let _ =
        print
          (((^) (((^) (("val " ^ name) ^ " = ") TomegaPrint.prgToString
                    (Psi, v_))
                   ^ " :: ")
              TomegaPrint.forToString (Psi, f_))
             ^ "\n") in
      let v'_ = topLevel (Psi, (d + 1), (p2_, (T.Dot ((T.Prg v_), t)))) in
      v'_ end(* function definition *)(* new declaration *)
(* lf value definition *)
let evalPrg = begin function | p_ -> evalPrg (I.Null, (p_, T.id)) end
let topLevel = begin function | p_ -> topLevel (I.Null, 0, (p_, T.id)) end
end
