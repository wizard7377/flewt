
module type OPSEM  =
  sig
    exception NoMatch 
    val evalPrg : Tomega.__Prg -> Tomega.__Prg
    val topLevel : Tomega.__Prg -> unit
    val createVarSub :
      Tomega.__Dec IntSyn.__Ctx -> Tomega.__Dec IntSyn.__Ctx -> Tomega.__Sub
    val matchSub :
      Tomega.__Dec IntSyn.__Ctx -> Tomega.__Sub -> Tomega.__Sub -> unit
  end;;




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
    let rec matchPrg (Psi) (__P1) (__P2) =
      matchVal (Psi, (__P1, T.id), (T.normalizePrg (__P2, T.id)))
    let rec matchVal __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Psi, (T.Unit, _), T.Unit) -> ()
      | (Psi, (PairPrg (__P1, P1'), t1), PairPrg (__P2, P2')) ->
          (matchVal (Psi, (__P1, t1), __P2); matchVal (Psi, (P1', t1), P2'))
      | (Psi, (PairBlock (__B1, __P1), t1), PairBlock (__B2, __P2)) ->
          (matchVal (Psi, (__P1, t1), __P2);
           (try
              Unify.unifyBlock
                ((T.coerceCtx Psi), (I.blockSub (__B1, (T.coerceSub t1))),
                  __B2)
            with | Unify _ -> raise NoMatch))
      | (Psi, (PairExp (__U1, __P1), t1), PairExp (__U2, __P2)) ->
          (matchVal (Psi, (__P1, t1), __P2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), (__U1, (T.coerceSub t1)), (__U2, I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, (PClo (__P, t1'), t1), Pt) ->
          matchVal (Psi, (__P, (T.comp (t1', t1))), Pt)
      | (Psi, (__P', t1), PClo (PClo (__P, t2), t3)) ->
          matchVal (Psi, (__P', t1), (T.PClo (__P, (T.comp (t2, t3)))))
      | (Psi, (__P', t1), PClo
         (EVar (_, ({ contents = None } as r), _, _, _, _), t2)) ->
          let iw = T.invertSub t2 in
          (((:=) r Some (T.PClo (__P', (T.comp (t1, iw)))))
            (* ABP -- just make sure this is right *))
      | (Psi, (__P', t1), EVar (_, ({ contents = None } as r), _, _, _, _))
          -> (:=) r Some (T.PClo (__P', t1))
      | (Psi, (__V, t), EVar
         (__D, ({ contents = Some (__P) } as r), __F, _, _, _)) ->
          matchVal (Psi, (__V, t), __P)
      | _ -> raise NoMatch(* ABP -- this should never occur, since we normalized it to start *)
      (* ABP -- Do we need this? I added it *)(* Added by ABP *)
    let rec append __3__ __4__ =
      match (__3__, __4__) with
      | (__G1, I.Null) -> __G1
      | (__G1, Decl (__G2, __D)) -> I.Decl ((append (__G1, __G2)), __D)
    let rec raisePrg __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (Psi, __G, T.Unit) -> T.Unit
      | (Psi, __G, PairPrg (__P1, __P2)) ->
          let P1' = raisePrg (Psi, __G, __P1) in
          let P2' = raisePrg (Psi, __G, __P2) in T.PairPrg (P1', P2')
      | (Psi, __G, PairExp (__U, __P)) ->
          let __V = TypeCheck.infer' ((append ((T.coerceCtx Psi), __G)), __U) in
          let w = S.weaken (__G, (I.targetFam __V)) in
          let iw = Whnf.invert w in
          let __G' = Whnf.strengthen (iw, __G) in
          let __U' = A.raiseTerm (__G', (I.EClo (__U, iw))) in
          let __P' = raisePrg (Psi, __G, __P) in ((T.PairExp (__U', __P'))
            (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)
            (* G  |- w  : G'    *)(* G' |- iw : G     *)
            (* Psi0, G' |- B'' ctx *))
    let rec evalPrg __13__ __14__ =
      match (__13__, __14__) with
      | (Psi, (T.Unit, t)) -> T.Unit
      | (Psi, (PairExp (__M, __P), t)) ->
          T.PairExp
            ((I.EClo (__M, (T.coerceSub t))), (evalPrg (Psi, (__P, t))))
      | (Psi, (PairBlock (__B, __P), t)) ->
          T.PairBlock
            ((I.blockSub (__B, (T.coerceSub t))), (evalPrg (Psi, (__P, t))))
      | (Psi, (PairPrg (__P1, __P2), t)) ->
          T.PairPrg ((evalPrg (Psi, (__P1, t))), (evalPrg (Psi, (__P2, t))))
      | (Psi, (Redex (__P, __S), t)) ->
          evalRedex (Psi, (evalPrg (Psi, (__P, t))), (__S, t))
      | (Psi, (Var k, t)) ->
          (match T.varSub (k, t) with
           | Prg (__P) -> evalPrg (Psi, (__P, T.id)))
      | (Psi, (Const lemma, t)) -> evalPrg (Psi, ((T.lemmaDef lemma), t))
      | (Psi, (Lam ((UDec (BDec _) as D), __P), t)) ->
          let __D' = T.decSub (__D, t) in
          T.Lam (__D', (evalPrg ((I.Decl (Psi, __D')), (__P, (T.dot1 t)))))
      | (Psi, (Lam (__D, __P), t)) ->
          T.Lam ((T.decSub (__D, t)), (T.PClo (__P, (T.dot1 t))))
      | (Psi, ((Rec (__D, __P) as P'), t)) ->
          evalPrg (Psi, (__P, (T.Dot ((T.Prg (T.PClo (__P', t))), t))))
      | (Psi, (PClo (__P, t'), t)) -> evalPrg (Psi, (__P, (T.comp (t', t))))
      | (Psi, (Case (Cases (__O)), t')) ->
          match__ (Psi, t', (T.Cases (rev __O)))
      | (Psi,
         (EVar (__D, ({ contents = Some (__P) } as r), __F, _, _, _), t)) ->
          evalPrg (Psi, (__P, t))
      | (Psi, (Let (__D, __P1, __P2), t)) ->
          let __V = evalPrg (Psi, (__P1, t)) in
          let __V' = evalPrg (Psi, (__P2, (T.Dot ((T.Prg __V), t)))) in __V'
      | (Psi, (New (Lam (__D, __P)), t)) ->
          let __D' = T.decSub (__D, t) in
          let UDec (D'') = __D' in
          let D''' = T.UDec (Names.decName ((T.coerceCtx Psi), D'')) in
          let __V = evalPrg ((I.Decl (Psi, D''')), (__P, (T.dot1 t))) in
          let __B = T.coerceCtx (I.Decl (I.Null, D''')) in
          let (__G, t') = T.deblockify __B in
          let newP = raisePrg (Psi, __G, (T.normalizePrg (__V, t'))) in
          ((newP)
            (* unnecessary naming, remove later --cs *))
      | (Psi, (Box (__W, __P), t)) -> evalPrg (Psi, (__P, t))
      | (Psi, (Choose (__P), t)) ->
          let rec substToSpine' __8__ __9__ __10__ =
            match (__8__, __9__, __10__) with
            | (Shift n, I.Null, __T) -> __T
            | (Shift n, (Decl _ as G), __T) ->
                substToSpine'
                  ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __G, __T)
            | (Dot (Exp (__U), s), Decl (__G, __V), __T) ->
                substToSpine' (s, __G, (T.AppExp (__U, __T)))
            | (Dot (Idx n, s), Decl (__G, Dec (_, __V)), __T) ->
                let (__Us, _) =
                  Whnf.whnfEta
                    (((I.Root ((I.BVar n), I.Nil)), I.id), (__V, I.id)) in
                substToSpine' (s, __G, (T.AppExp ((I.EClo __Us), __T)))
            (* Eta-expand *) in
          let rec choose __11__ __12__ =
            match (__11__, __12__) with
            | (k, I.Null) -> raise Abort
            | (k, Decl (Psi', PDec _)) -> choose ((k + 1), Psi')
            | (k, Decl (Psi', UDec (Dec _))) -> choose ((k + 1), Psi')
            | (k, Decl (Psi', UDec (BDec (_, (l1, s1))))) ->
                let (Gsome, Gpi) = I.constBlock l1 in
                let __S =
                  substToSpine' (s1, Gsome, (T.AppBlock ((I.Bidx k), T.Nil))) in
                (try
                   evalPrg (Psi, ((T.Redex ((T.PClo (__P, t)), __S)), T.id))
                 with | Abort -> choose ((k + 1), Psi')) in
          ((choose (1, Psi))
            (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
            (* substtospine' (s, G, T) = S @ T
                If   G' |- s : G
                then G' |- S : {{G}} a >> a  for arbitrary a
                    {{G}} erases void declarations in G
              *))
      (* reverse list O, so it looks at the
           cases in the same order it is printed
           *)
      (* this is ugly.
           * don't do reverse *)
    let rec match__ __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (Psi, t1, Cases ((Psi', t2, __P)::__C)) ->
          let t = createVarSub (Psi, Psi') in
          let t' = T.comp (t2, t) in
          (((try
               matchSub (Psi, t1, t');
               evalPrg (Psi, (((__P, t))(*T.normalizeSub*)))
             with | NoMatch -> match__ (Psi, t1, (T.Cases __C))))
            (* val I.Null = Psi *)(* Psi |- t : Psi' *)
            (* Psi' |- t2 . shift(k) : Psi'' *)(* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *))
      | (Psi, t1, Cases nil) -> raise Abort
    let rec createVarSub __18__ __19__ =
      match (__18__, __19__) with
      | (Psi, I.Null) -> T.Shift (I.ctxLength Psi)
      | (Psi, (Decl (Psi', PDec (name, __F, None, None)) as Psi'')) ->
          let t = createVarSub (Psi, Psi') in
          let t' =
            T.Dot
              ((T.Prg (T.newEVarTC (Psi, (T.forSub (__F, t)), None, None))),
                t) in
          t'
      | (Psi, Decl (Psi', UDec (Dec (name, __V)))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Exp
                (I.EVar
                   ((ref None), (T.coerceCtx Psi),
                     (I.EClo (__V, (T.coerceSub t))), (ref [])))), t)
      | (Psi, Decl (Psi', UDec (BDec (name, (cid, s))))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Block
                (I.LVar
                   ((ref None), I.id, (cid, (I.comp (s, (T.coerceSub t))))))),
              t)
    let rec matchSub __20__ __21__ __22__ =
      match (__20__, __21__, __22__) with
      | (Psi, _, Shift _) -> ()
      | (Psi, Shift n, (Dot _ as t)) ->
          matchSub (Psi, (T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), t)
      | (Psi, Dot (Exp (__U1), t1), Dot (Exp (__U2), t2)) ->
          (matchSub (Psi, t1, t2);
           (try Unify.unify ((T.coerceCtx Psi), (__U1, I.id), (__U2, I.id))
            with | Unify s -> raise NoMatch))
      | (Psi, Dot (Exp (__U1), t1), Dot (Idx k, t2)) ->
          (matchSub (Psi, t1, t2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), (__U1, I.id),
                  ((I.Root ((I.BVar k), I.Nil)), I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, Dot (Idx k, t1), Dot (Exp (__U2), t2)) ->
          (matchSub (Psi, t1, t2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), ((I.Root ((I.BVar k), I.Nil)), I.id),
                  (__U2, I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, Dot (Prg (__P1), t1), Dot (Prg (__P2), t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, __P1, __P2))
      | (Psi, Dot (Prg (__P1), t1), Dot (Idx k, t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, __P1, (T.Var k)))
      | (Psi, Dot (Idx k, t1), Dot (Prg (__P2), t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, (T.Var k), __P2))
      | (Psi, Dot (Idx k1, t1), Dot (Idx k2, t2)) ->
          if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch
      | (Psi, Dot (Idx k, t1), Dot (Block (LVar (r, s1, (c, s2))), t2)) ->
          let s1' = Whnf.invert s1 in
          let _ = (:=) r Some (I.blockSub ((I.Bidx k), s1')) in
          matchSub (Psi, t1, t2)
      | (Psi, Dot (Block (__B), t1), Dot (Block (LVar (r, s1, (c, s2))), t2))
          ->
          let s1' = Whnf.invert s1 in
          let _ = (:=) r Some (I.blockSub (__B, s1')) in
          matchSub (Psi, t1, t2)(* By Invariant *)
    let rec evalRedex __23__ __24__ __25__ =
      match (__23__, __24__, __25__) with
      | (Psi, __V, (T.Nil, _)) -> __V
      | (Psi, __V, (SClo (__S, t1), t2)) ->
          evalRedex (Psi, __V, (__S, (T.comp (t1, t2))))
      | (Psi, Lam (UDec (Dec (_, __A)), __P'), (AppExp (__U, __S), t)) ->
          let __V =
            evalPrg
              (Psi,
                (__P',
                  (T.Dot ((T.Exp (I.EClo (__U, (T.coerceSub t)))), T.id)))) in
          evalRedex (Psi, __V, (__S, t))
      | (Psi, Lam (UDec _, __P'), (AppBlock (__B, __S), t)) ->
          evalRedex
            (Psi,
              (evalPrg
                 (Psi,
                   (__P',
                     (T.Dot
                        ((T.Block (I.blockSub (__B, (T.coerceSub t)))), T.id))))),
              (__S, t))
      | (Psi, Lam (PDec _, __P'), (AppPrg (__P, __S), t)) ->
          let __V = evalPrg (Psi, (__P, t)) in
          let __V' = evalPrg (Psi, (__P', (T.Dot ((T.Prg __V), T.id)))) in
          evalRedex (Psi, __V', (__S, t))
    let rec topLevel __30__ __31__ __32__ =
      match (__30__, __31__, __32__) with
      | (Psi, d, (T.Unit, t)) -> ()
      | (Psi, d, (Let (__D', __P1, Case (__Cs)), t)) ->
          let rec printLF __26__ __27__ __28__ __29__ =
            match (__26__, __27__, __28__, __29__) with
            | (_, _, _, 0) -> ()
            | (__G, Dot (Exp (__U), s'), Decl (__G', Dec (Some name, __V)),
               k) ->
                let _ = printLF (__G, s', __G') (k - 1) in
                print
                  (((((("def " ^ name) ^ " = ") ^
                        (Print.expToString (__G, __U)))
                       ^ " : ")
                      ^ (Print.expToString (__G, (I.EClo (__V, s')))))
                     ^ "\n") in
          let rec match__ (Psi) t1 (Cases ((Psi', t2, __P)::__C)) =
            let t = createVarSub (Psi, Psi') in
            let t' = T.comp (t2, t) in
            let m = I.ctxLength Psi' in
            let _ = matchSub (Psi, t1, t') in
            let t'' = t in
            let _ =
              printLF
                ((T.coerceCtx Psi), (T.coerceSub t''), (T.coerceCtx Psi'))
                (m - d) in
            ((topLevel (Psi, m, (__P, t'')))
              (* Psi |- t : Psi' *)(* Psi' |- t2 . shift(k) : Psi'' *)
              (* T.normalizeSub *)(* Psi |- t'' : Psi' *)) in
          let __V = evalPrg (Psi, (__P1, t)) in
          let __V' = match__ (Psi, (T.Dot ((T.Prg __V), t)), __Cs) in ((__V')
            (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *))
      | (Psi, d,
         (Let
          (__D, Lam ((UDec (BDec (Some name, (cid, s))) as D'), __P1), __P2),
          t)) ->
          let _ = print (("new " ^ name) ^ "\n") in
          let D'' = T.decSub (__D', t) in
          let _ = topLevel ((I.Decl (Psi, D'')), (d + 1), (__P1, (T.dot1 t))) in
          ()
      | (Psi, d, (Let (__D, __P1, __P2), t)) ->
          let PDec (Some name, __F, _, _) = __D in
          let __V = evalPrg (Psi, (__P1, t)) in
          let _ =
            print
              (((^) (((^) (("val " ^ name) ^ " = ") TomegaPrint.prgToString
                        (Psi, __V))
                       ^ " :: ")
                  TomegaPrint.forToString (Psi, __F))
                 ^ "\n") in
          let __V' =
            topLevel (Psi, (d + 1), (__P2, (T.Dot ((T.Prg __V), t)))) in
          __V'(* function definition *)(* new declaration *)
      (* lf value definition *)
    let evalPrg (__P) = evalPrg (I.Null, (__P, T.id))
    let topLevel (__P) = topLevel (I.Null, 0, (__P, T.id))
  end ;;
