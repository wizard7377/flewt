
module type OPSEM  =
  sig
    exception NoMatch (*! structure Tomega : TOMEGA !*)
    (*! structure IntSyn : INTSYN !*)(* Author: Carsten Schuermann *)
    (* Operational Semantics for Delphin *)
    val evalPrg : Tomega.__Prg -> Tomega.__Prg
    val topLevel : Tomega.__Prg -> unit
    val createVarSub :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Dec IntSyn.__Ctx) -> Tomega.__Sub
    val matchSub :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Sub * Tomega.__Sub) -> unit
  end;;




module Opsem(Opsem:sig
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Subordinate : SUBORDINATE
                     module TomegaTypeCheck : TOMEGATYPECHECK
                     module TomegaPrint : TOMEGAPRINT
                     module Unify :
                     ((UNIFY)(* Internal syntax for functional proof term calculus *)
                     (* Author: Carsten Schuermann, Adam Poswolsky *))
                   end) : OPSEM =
  struct
    module T = Tomega
    module I = IntSyn
    module S = Subordinate
    module A = Abstract
    exception Error of string 
    exception Abort 
    exception NoMatch (*  local -- removed ABP 1/19/03 *)
    let rec matchPrg
      (((Psi)(*
 matchPrg is used to see if two values can be 'unified' for
   purpose of matching case

 matchPrg (Psi, P1, P2) = ()

    Invariant:
    If P1 has no EVARs and P2 possibly does.
    and Psi  |- P1 :: F
    and Psi |- P1 value
    and Psi |- P2 :: F
    and Psi |- P2 value
     then if Psi |- P1 == P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)),
       P1, P2)
      = matchVal (Psi, (P1, T.id), (T.normalizePrg (P2, T.id)))
    let rec matchVal =
      function
      | (((Psi)(* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)),
         (T.Unit, _), T.Unit) -> ()
      | (Psi, (PairPrg (P1, P1'), t1), PairPrg (P2, P2')) ->
          (matchVal (Psi, (P1, t1), P2); matchVal (Psi, (P1', t1), P2'))
      | (Psi, (PairBlock (B1, P1), t1), PairBlock (B2, P2)) ->
          (matchVal (Psi, (P1, t1), P2);
           (try
              Unify.unifyBlock
                ((T.coerceCtx Psi), (I.blockSub (B1, (T.coerceSub t1))), B2)
            with | Unify _ -> raise NoMatch))
      | (Psi, (PairExp (u1, P1), t1), PairExp (u2, P2)) ->
          (matchVal (Psi, (P1, t1), P2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), (u1, (T.coerceSub t1)), (u2, I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, (PClo (P, t1'), t1), Pt) ->
          matchVal (Psi, (P, (T.comp (t1', t1))), Pt)
      | (((Psi)(* Added by ABP *)), (P', t1), PClo
         (PClo (P, t2), t3)) ->
          matchVal
            (((Psi)
              (* ABP -- Do we need this? I added it *)),
              (P', t1), (T.PClo (P, (T.comp (t2, t3)))))
      | (Psi, (P', t1), PClo (EVar (_, (ref (NONE) as r), _, _, _, _), t2))
          ->
          let iw = T.invertSub t2 in
          (:=) r ((SOME)
            (* ABP -- just make sure this is right *))
            (T.PClo (P', (T.comp (t1, iw))))
      | (Psi, (P', t1), EVar (_, (ref (NONE) as r), _, _, _, _)) ->
          (:=) r SOME (T.PClo (P', t1))
      | (Psi, (V, t), EVar (D, (ref (SOME (P)) as r), F, _, _, _)) ->
          matchVal
            (((Psi)
              (* ABP -- this should never occur, since we normalized it to start *)),
              (V, t), P)
      | _ -> raise NoMatch
    let rec append =
      function
      | (G1, I.Null) -> G1
      | (G1, Decl (G2, D)) -> I.Decl ((append (G1, G2)), D)
    let rec raisePrg =
      function
      | (((Psi)(* raisePrg is used in handling of NEW construct
   raisePrg (g, P, F) = (P', F'))

       Invariant:
       If   Psi, g |- P in F
       and  Psi |- g : blockctx
       then Psi |- P' in F'
       and  P = raise (g, P')   (using subordination)
       and  F = raise (g, F')   (using subordination)
*)),
         g, T.Unit) -> T.Unit
      | (Psi, g, PairPrg (P1, P2)) ->
          let P1' = raisePrg (Psi, g, P1) in
          let P2' = raisePrg (Psi, g, P2) in T.PairPrg (P1', P2')
      | (Psi, g, PairExp (U, P)) ->
          let V = TypeCheck.infer' ((append ((T.coerceCtx Psi), g)), U) in
          let ((w)(* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *))
            = S.weaken (g, (I.targetFam V)) in
          let ((iw)(* g  |- w  : g'    *)) = Whnf.invert w in
          let ((g')(* g' |- iw : g     *)) =
            Whnf.strengthen (iw, g) in
          let ((U')(* Psi0, g' |- B'' ctx *)) =
            A.raiseTerm (g', (I.EClo (U, iw))) in
          let P' = raisePrg (Psi, g, P) in T.PairExp (U', P')
    let rec evalPrg =
      function
      | (((Psi)(* evalPrg (Psi, (P, t)) = V

       Invariant:
       If   Psi' |- P :: F
       and  Psi |- t :: Psi'
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- P[t] evalsto V
       and  Psi |- F[t] == F'
    *)),
         (T.Unit, t)) -> T.Unit
      | (Psi, (PairExp (M, P), t)) ->
          T.PairExp ((I.EClo (M, (T.coerceSub t))), (evalPrg (Psi, (P, t))))
      | (Psi, (PairBlock (B, P), t)) ->
          T.PairBlock
            ((I.blockSub (B, (T.coerceSub t))), (evalPrg (Psi, (P, t))))
      | (Psi, (PairPrg (P1, P2), t)) ->
          T.PairPrg ((evalPrg (Psi, (P1, t))), (evalPrg (Psi, (P2, t))))
      | (Psi, (Redex (P, S), t)) ->
          evalRedex (Psi, (evalPrg (Psi, (P, t))), (S, t))
      | (Psi, (Var k, t)) ->
          (match T.varSub (k, t) with | Prg (P) -> evalPrg (Psi, (P, T.id)))
      | (Psi, (Const lemma, t)) -> evalPrg (Psi, ((T.lemmaDef lemma), t))
      | (Psi, (Lam ((UDec (BDec _) as D), P), t)) ->
          let D' = T.decSub (D, t) in
          T.Lam (D', (evalPrg ((I.Decl (Psi, D')), (P, (T.dot1 t)))))
      | (Psi, (Lam (D, P), t)) ->
          T.Lam ((T.decSub (D, t)), (T.PClo (P, (T.dot1 t))))
      | (Psi, ((Rec (D, P) as P'), t)) ->
          evalPrg (Psi, (P, (T.Dot ((T.Prg (T.PClo (P', t))), t))))
      | (Psi, (PClo (P, t'), t)) -> evalPrg (Psi, (P, (T.comp (t', t))))
      | (Psi, (Case (Cases (O)), t')) ->
          match__
            (((Psi)
              (* this is ugly.
           * don't do reverse *)
              (* reverse list O, so it looks at the
           cases in the same order it is printed
           *)),
              t', (T.Cases (rev O)))
      | (Psi, (EVar (D, (ref (SOME (P)) as r), F, _, _, _), t)) ->
          evalPrg (Psi, (P, t))
      | (Psi, (Let (D, P1, P2), t)) ->
          let V = evalPrg (Psi, (P1, t)) in
          let V' = evalPrg (Psi, (P2, (T.Dot ((T.Prg V), t)))) in V'
      | (Psi, (New (Lam (D, P)), t)) ->
          let D' = T.decSub (D, t) in
          let UDec (D'') = D' in
          let D''' = T.UDec (Names.decName ((T.coerceCtx Psi), D'')) in
          let ((V)(* unnecessary naming, remove later --cs *))
            = evalPrg ((I.Decl (Psi, D''')), (P, (T.dot1 t))) in
          let B = T.coerceCtx (I.Decl (I.Null, D''')) in
          let (g, t') = T.deblockify B in
          let newP = raisePrg (Psi, g, (T.normalizePrg (V, t'))) in newP
      | (Psi, (Box (W, P), t)) -> evalPrg (Psi, (P, t))
      | (Psi, (Choose (P), t)) ->
          let substToSpine' =
            function
            | (Shift
               ((n)(* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
               (* substtospine' (s, g, T) = S @ T
                If   g' |- s : g
                then g' |- S : {{g}} a >> a  for arbitrary a
                    {{g}} erases void declarations in g
              *)),
               I.Null, T) -> T
            | (Shift n, (Decl _ as g), T) ->
                substToSpine'
                  ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), g, T)
            | (Dot (Exp (U), s), Decl (g, V), T) ->
                substToSpine' (s, g, (T.AppExp (U, T)))
            | (Dot (Idx n, s), Decl (g, Dec (_, V)), T) ->
                let (((Us)(* Eta-expand *)), _) =
                  Whnf.whnfEta
                    (((I.Root ((I.BVar n), I.Nil)), I.id), (V, I.id)) in
                substToSpine' (s, g, (T.AppExp ((I.EClo Us), T))) in
          let choose =
            function
            | (k, I.Null) -> raise Abort
            | (k, Decl (Psi', PDec _)) -> choose ((k + 1), Psi')
            | (k, Decl (Psi', UDec (Dec _))) -> choose ((k + 1), Psi')
            | (k, Decl (Psi', UDec (BDec (_, (l1, s1))))) ->
                let (Gsome, Gpi) = I.constBlock l1 in
                let S =
                  substToSpine' (s1, Gsome, (T.AppBlock ((I.Bidx k), T.Nil))) in
                (try evalPrg (Psi, ((T.Redex ((T.PClo (P, t)), S)), T.id))
                 with | Abort -> choose ((k + 1), Psi')) in
          choose (1, Psi)
    let rec match__ =
      function
      | (((Psi)(* other cases should not occur -cs *)
         (* match is used to handle Case statements
  match (Psi, t1, O) = V

       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
            otherwise exception NoMatch is raised.
    *)),
         t1, Cases ((Psi', t2, P)::C)) ->
          let ((t)(* val I.Null = Psi *)) =
            createVarSub (Psi, Psi') in
          let ((t')(* Psi |- t : Psi' *)(* Psi' |- t2 . shift(k) : Psi'' *))
            = T.comp (t2, t) in
          (try matchSub (Psi, t1, t'); evalPrg (Psi, (P, t))
           with
           | NoMatch ->
               match__
                 (((Psi)
                   (* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *)
                   (*T.normalizeSub*)), t1, (T.Cases C)))
      | (Psi, t1, Cases nil) -> raise Abort
    let rec createVarSub =
      function
      | (((Psi)(* What do you want to do if it doesn't match anything *)
         (* can't happen when total function - ABP *)
         (* | match (Psi, t1, T.Cases Nil) = raise Domain  *)(* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)),
         I.Null) -> T.Shift (I.ctxLength Psi)
      | (Psi, (Decl (Psi', PDec (name, F, NONE, NONE)) as Psi'')) ->
          let t = createVarSub (Psi, Psi') in
          let t' =
            T.Dot
              ((T.Prg (T.newEVarTC (Psi, (T.forSub (F, t)), NONE, NONE))), t) in
          t'
      | (Psi, Decl (Psi', UDec (Dec (name, V)))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Exp
                (I.EVar
                   ((ref NONE), (T.coerceCtx Psi),
                     (I.EClo (V, (T.coerceSub t))), (ref [])))), t)
      | (Psi, Decl (Psi', UDec (BDec (name, (cid, s))))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Block
                (I.LVar
                   ((ref NONE), I.id, (cid, (I.comp (s, (T.coerceSub t))))))),
              t)
    let rec matchSub =
      function
      | (((Psi)(* matchSub (t1, t2) = ()

       Invariant:
       If   Psi  |- t1 :: Psi'
       and  Psi  |- t2 :: Psi'
       and  Psi  |- t1 == t2 :: Psi'
       and  |- Psi ctx [block]
       then function returns ()
            otherwise exception NoMatch is raised
    *)),
         _, Shift _) -> ()
      | (((Psi)(* By Invariant *)), Shift n, (Dot _ as t))
          -> matchSub (Psi, (T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), t)
      | (Psi, Dot (Exp (u1), t1), Dot (Exp (u2), t2)) ->
          (matchSub (Psi, t1, t2);
           (try Unify.unify ((T.coerceCtx Psi), (u1, I.id), (u2, I.id))
            with | Unify s -> raise NoMatch))
      | (Psi, Dot (Exp (u1), t1), Dot (Idx k, t2)) ->
          (matchSub (Psi, t1, t2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), (u1, I.id),
                  ((I.Root ((I.BVar k), I.Nil)), I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, Dot (Idx k, t1), Dot (Exp (u2), t2)) ->
          (matchSub (Psi, t1, t2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), ((I.Root ((I.BVar k), I.Nil)), I.id),
                  (u2, I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, Dot (Prg (P1), t1), Dot (Prg (P2), t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, P1, P2))
      | (Psi, Dot (Prg (P1), t1), Dot (Idx k, t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, P1, (T.Var k)))
      | (Psi, Dot (Idx k, t1), Dot (Prg (P2), t2)) ->
          (matchSub (Psi, t1, t2); matchPrg (Psi, (T.Var k), P2))
      | (Psi, Dot (Idx k1, t1), Dot (Idx k2, t2)) ->
          if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch
      | (Psi, Dot (Idx k, t1), Dot (Block (LVar (r, s1, (c, s2))), t2)) ->
          let s1' = Whnf.invert s1 in
          let _ = (:=) r SOME (I.blockSub ((I.Bidx k), s1')) in
          matchSub (Psi, t1, t2)
      | (Psi, Dot (Block (B), t1), Dot (Block (LVar (r, s1, (c, s2))), t2))
          ->
          let s1' = Whnf.invert s1 in
          let _ = (:=) r SOME (I.blockSub (B, s1')) in matchSub (Psi, t1, t2)
    let rec evalRedex =
      function
      | (((Psi)(* evalRedex (Psi, V, (S, t)) = V'

       Invariant:
       If   Psi  |- V :: F1
       and  Psi' |- S :: F2 > F3
       and  Psi  |- t :: Psi'
       and  Psi' |- F1 == F2[t]
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- V . (S[t]) evalsto V''
       then Psi |- V' == V'' : F3[t]
    *)),
         V, (T.Nil, _)) -> V
      | (Psi, V, (SClo (S, t1), t2)) ->
          evalRedex (Psi, V, (S, (T.comp (t1, t2))))
      | (Psi, Lam (UDec (Dec (_, A)), P'), (AppExp (U, S), t)) ->
          let V =
            evalPrg
              (Psi,
                (P', (T.Dot ((T.Exp (I.EClo (U, (T.coerceSub t)))), T.id)))) in
          evalRedex (Psi, V, (S, t))
      | (Psi, Lam (UDec _, P'), (AppBlock (B, S), t)) ->
          evalRedex
            (Psi,
              (evalPrg
                 (Psi,
                   (P',
                     (T.Dot
                        ((T.Block (I.blockSub (B, (T.coerceSub t)))), T.id))))),
              (S, t))
      | (Psi, Lam (PDec _, P'), (AppPrg (P, S), t)) ->
          let V = evalPrg (Psi, (P, t)) in
          let V' = evalPrg (Psi, (P', (T.Dot ((T.Prg V), T.id)))) in
          evalRedex (Psi, V', (S, t))
    let rec topLevel =
      function
      | (((Psi)(* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)),
         d, (T.Unit, t)) -> ()
      | (Psi, d, (Let (D', P1, Case (Cs)), t)) ->
          let printLF arg__0 arg__1 =
            match (arg__0, arg__1) with
            | ((((_)(* lf value definition *)(* printLF (g, s, g') k = ()
             Invariant:
             g |- s : g'
          *)),
                _, _),
               0) -> ()
            | ((g, Dot (Exp (U), s'), Decl (g', Dec (SOME name, V))), k) ->
                let _ = printLF (g, s', g') (k - 1) in
                print
                  (((((("def " ^ name) ^ " = ") ^ (Print.expToString (g, U)))
                       ^ " : ")
                      ^ (Print.expToString (g, (I.EClo (V, s')))))
                     ^ "\n") in
          let match__ (Psi, t1, Cases ((Psi', t2, P)::C)) =
            let t = createVarSub (Psi, Psi') in
            let ((t')(* Psi |- t : Psi' *)(* Psi' |- t2 . shift(k) : Psi'' *))
              = T.comp (t2, t) in
            let m = I.ctxLength Psi' in
            let _ = matchSub (Psi, t1, t') in
            let t'' = ((t)(* T.normalizeSub *)) in
            let ((_)(* Psi |- t'' : Psi' *)) =
              printLF
                ((T.coerceCtx Psi), (T.coerceSub t''), (T.coerceCtx Psi'))
                (m - d) in
            topLevel (Psi, m, (P, t'')) in
          let V = evalPrg (Psi, (P1, t)) in
          let V' = match__ (Psi, (T.Dot ((T.Prg V), t)), Cs) in V'
      | (Psi, d,
         (Let (D, Lam ((UDec (BDec (SOME name, (cid, s))) as D'), P1), P2),
          t)) ->
          let ((_)(* new declaration *)) =
            print (("new " ^ name) ^ "\n") in
          let D'' = T.decSub (D', t) in
          let _ = topLevel ((I.Decl (Psi, D'')), (d + 1), (P1, (T.dot1 t))) in
          ()
      | (Psi, d, (Let (D, P1, P2), t)) ->
          let PDec
            (SOME ((name)(* function definition *)), F, _,
             _)
            = D in
          let V = evalPrg (Psi, (P1, t)) in
          let _ =
            print
              (((^) (((^) (("val " ^ name) ^ " = ") TomegaPrint.prgToString
                        (Psi, V))
                       ^ " :: ")
                  TomegaPrint.forToString (Psi, F))
                 ^ "\n") in
          let V' = topLevel (Psi, (d + 1), (P2, (T.Dot ((T.Prg V), t)))) in
          V'
    let ((evalPrg)(* in -- removed local *)) =
      function | P -> evalPrg (I.Null, (P, T.id))
    let topLevel = function | P -> topLevel (I.Null, 0, (P, T.id))
  end ;;
