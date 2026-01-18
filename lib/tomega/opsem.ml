
(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)
module type OPSEM  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    exception NoMatch 
    val evalPrg : Tomega.__Prg -> Tomega.__Prg
    val topLevel : Tomega.__Prg -> unit
    val createVarSub :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Dec IntSyn.__Ctx) -> Tomega.__Sub
    val matchSub :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Sub * Tomega.__Sub) -> unit
  end;;




(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann, Adam Poswolsky *)
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
    (*  local -- removed ABP 1/19/03 *)
    exception NoMatch 
    (*
 matchPrg is used to see if two values can be 'unified' for
   purpose of matching case

 matchPrg (Psi, __P1, __P2) = ()

    Invariant:
    If __P1 has no EVARs and __P2 possibly does.
    and Psi  |- __P1 :: F
    and Psi |- __P1 value
    and Psi |- __P2 :: F
    and Psi |- __P2 value
     then if Psi |- __P1 == __P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)
    let rec matchPrg (Psi, __P1, __P2) =
      matchVal (Psi, (__P1, T.id), (T.normalizePrg (__P2, T.id)))
    let rec matchVal =
      function
      | (Psi, (T.Unit, _), T.Unit) -> ()
      | (Psi, (PairPrg (__P1, __P1'), t1), PairPrg (__P2, __P2')) ->
          (matchVal (Psi, (__P1, t1), __P2); matchVal (Psi, (__P1', t1), __P2'))
      | (Psi, (PairBlock (B1, __P1), t1), PairBlock (B2, __P2)) ->
          (matchVal (Psi, (__P1, t1), __P2);
           (try
              Unify.unifyBlock
                ((T.coerceCtx Psi), (I.blockSub (B1, (T.coerceSub t1))), B2)
            with | Unify _ -> raise NoMatch))
      | (Psi, (PairExp (__U1, __P1), t1), PairExp (__U2, __P2)) ->
          (matchVal (Psi, (__P1, t1), __P2);
           (try
              Unify.unify
                ((T.coerceCtx Psi), (__U1, (T.coerceSub t1)), (__U2, I.id))
            with | Unify _ -> raise NoMatch))
      | (Psi, (PClo (P, t1'), t1), Pt) ->
          matchVal (Psi, (P, (T.comp (t1', t1))), Pt)
      | (Psi, (__P', t1), PClo (PClo (P, t2), t3)) ->
          matchVal (Psi, (__P', t1), (T.PClo (P, (T.comp (t2, t3)))))
      | (Psi, (__P', t1), PClo (EVar (_, (ref (None) as r), _, _, _, _), t2))
          ->
          let iw = T.invertSub t2 in
          (((:=) r Some (T.PClo (__P', (T.comp (t1, iw)))))
            (* ABP -- just make sure this is right *))
      | (Psi, (__P', t1), EVar (_, (ref (None) as r), _, _, _, _)) ->
          (:=) r Some (T.PClo (__P', t1))
      | (Psi, (__v, t), EVar (__d, (ref (Some (P)) as r), F, _, _, _)) ->
          matchVal (Psi, (__v, t), P)
      | _ -> raise NoMatch(* ABP -- this should never occur, since we normalized it to start *)
      (* ABP -- Do we need this? I added it *)(* Added by ABP *)
    let rec append =
      function
      | (G1, I.Null) -> G1
      | (G1, Decl (G2, __d)) -> I.Decl ((append (G1, G2)), __d)
    let rec raisePrg =
      function
      | (Psi, __g, T.Unit) -> T.Unit
      | (Psi, __g, PairPrg (__P1, __P2)) ->
          let __P1' = raisePrg (Psi, __g, __P1) in
          let __P2' = raisePrg (Psi, __g, __P2) in T.PairPrg (__P1', __P2')
      | (Psi, __g, PairExp (__u, P)) ->
          let __v = TypeCheck.infer' ((append ((T.coerceCtx Psi), __g)), __u) in
          let w = S.weaken (__g, (I.targetFam __v)) in
          let iw = Whnf.invert w in
          let __g' = Whnf.strengthen (iw, __g) in
          let __u' = A.raiseTerm (__g', (I.EClo (__u, iw))) in
          let __P' = raisePrg (Psi, __g, P) in ((T.PairExp (__u', __P'))
            (* this is a real time sink, it would be much better if we did not have to
      compute the type information of __u,
      more thought is required
   *)
            (* __g  |- w  : __g'    *)(* __g' |- iw : __g     *)
            (* Psi0, __g' |- B'' ctx *))
    let rec evalPrg =
      function
      | (Psi, (T.Unit, t)) -> T.Unit
      | (Psi, (PairExp (M, P), t)) ->
          T.PairExp ((I.EClo (M, (T.coerceSub t))), (evalPrg (Psi, (P, t))))
      | (Psi, (PairBlock (B, P), t)) ->
          T.PairBlock
            ((I.blockSub (B, (T.coerceSub t))), (evalPrg (Psi, (P, t))))
      | (Psi, (PairPrg (__P1, __P2), t)) ->
          T.PairPrg ((evalPrg (Psi, (__P1, t))), (evalPrg (Psi, (__P2, t))))
      | (Psi, (Redex (P, S), t)) ->
          evalRedex (Psi, (evalPrg (Psi, (P, t))), (S, t))
      | (Psi, (Var k, t)) ->
          (match T.varSub (k, t) with | Prg (P) -> evalPrg (Psi, (P, T.id)))
      | (Psi, (Const lemma, t)) -> evalPrg (Psi, ((T.lemmaDef lemma), t))
      | (Psi, (Lam ((UDec (BDec _) as __d), P), t)) ->
          let __d' = T.decSub (__d, t) in
          T.Lam (__d', (evalPrg ((I.Decl (Psi, __d')), (P, (T.dot1 t)))))
      | (Psi, (Lam (__d, P), t)) ->
          T.Lam ((T.decSub (__d, t)), (T.PClo (P, (T.dot1 t))))
      | (Psi, ((Rec (__d, P) as __P'), t)) ->
          evalPrg (Psi, (P, (T.Dot ((T.Prg (T.PClo (__P', t))), t))))
      | (Psi, (PClo (P, t'), t)) -> evalPrg (Psi, (P, (T.comp (t', t))))
      | (Psi, (Case (Cases (O)), t')) -> match__ (Psi, t', (T.Cases (rev O)))
      | (Psi, (EVar (__d, (ref (Some (P)) as r), F, _, _, _), t)) ->
          evalPrg (Psi, (P, t))
      | (Psi, (Let (__d, __P1, __P2), t)) ->
          let __v = evalPrg (Psi, (__P1, t)) in
          let __v' = evalPrg (Psi, (__P2, (T.Dot ((T.Prg __v), t)))) in __v'
      | (Psi, (New (Lam (__d, P)), t)) ->
          let __d' = T.decSub (__d, t) in
          let UDec (__d'') = __d' in
          let __d''' = T.UDec (Names.decName ((T.coerceCtx Psi), __d'')) in
          let __v = evalPrg ((I.Decl (Psi, __d''')), (P, (T.dot1 t))) in
          let B = T.coerceCtx (I.Decl (I.Null, __d''')) in
          let (__g, t') = T.deblockify B in
          let newP = raisePrg (Psi, __g, (T.normalizePrg (__v, t'))) in ((newP)
            (* unnecessary naming, remove later --cs *))
      | (Psi, (Box (W, P), t)) -> evalPrg (Psi, (P, t))
      | (Psi, (Choose (P), t)) ->
          let rec substToSpine' =
            function
            | (Shift n, I.Null, T) -> T
            | (Shift n, (Decl _ as __g), T) ->
                substToSpine'
                  ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __g, T)
            | (Dot (Exp (__u), s), Decl (__g, __v), T) ->
                substToSpine' (s, __g, (T.AppExp (__u, T)))
            | (Dot (Idx n, s), Decl (__g, Dec (_, __v)), T) ->
                let (__Us, _) =
                  Whnf.whnfEta
                    (((I.Root ((I.BVar n), I.Nil)), I.id), (__v, I.id)) in
                substToSpine' (s, __g, (T.AppExp ((I.EClo __Us), T)))(* Eta-expand *) in
          let rec choose =
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
          ((choose (1, Psi))
            (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
            (* substtospine' (s, __g, T) = S @ T
                If   __g' |- s : __g
                then __g' |- S : {{__g}} a >> a  for arbitrary a
                    {{__g}} erases void declarations in __g
              *))
      (* reverse list O, so it looks at the
           cases in the same order it is printed
           *)
      (* this is ugly.
           * don't do reverse *)
    let rec match__ =
      function
      | (Psi, t1, Cases ((Psi', t2, P)::C)) ->
          let t = createVarSub (Psi, Psi') in
          let t' = T.comp (t2, t) in
          (((try
               matchSub (Psi, t1, t');
               evalPrg (Psi, (((P, t))(*T.normalizeSub*)))
             with | NoMatch -> match__ (Psi, t1, (T.Cases C))))
            (* val I.Null = Psi *)(* Psi |- t : Psi' *)
            (* Psi' |- t2 . shift(k) : Psi'' *)(* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *))
      | (Psi, t1, Cases nil) -> raise Abort
    let rec createVarSub =
      function
      | (Psi, I.Null) -> T.Shift (I.ctxLength Psi)
      | (Psi, (Decl (Psi', PDec (name, F, None, None)) as Psi'')) ->
          let t = createVarSub (Psi, Psi') in
          let t' =
            T.Dot
              ((T.Prg (T.newEVarTC (Psi, (T.forSub (F, t)), None, None))), t) in
          t'
      | (Psi, Decl (Psi', UDec (Dec (name, __v)))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Exp
                (I.EVar
                   ((ref None), (T.coerceCtx Psi),
                     (I.EClo (__v, (T.coerceSub t))), (ref [])))), t)
      | (Psi, Decl (Psi', UDec (BDec (name, (cid, s))))) ->
          let t = createVarSub (Psi, Psi') in
          T.Dot
            ((T.Block
                (I.LVar
                   ((ref None), I.id, (cid, (I.comp (s, (T.coerceSub t))))))),
              t)
    let rec matchSub =
      function
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
      | (Psi, Dot (Block (B), t1), Dot (Block (LVar (r, s1, (c, s2))), t2))
          ->
          let s1' = Whnf.invert s1 in
          let _ = (:=) r Some (I.blockSub (B, s1')) in matchSub (Psi, t1, t2)
      (* By Invariant *)
    let rec evalRedex =
      function
      | (Psi, __v, (T.Nil, _)) -> __v
      | (Psi, __v, (SClo (S, t1), t2)) ->
          evalRedex (Psi, __v, (S, (T.comp (t1, t2))))
      | (Psi, Lam (UDec (Dec (_, A)), __P'), (AppExp (__u, S), t)) ->
          let __v =
            evalPrg
              (Psi,
                (__P', (T.Dot ((T.Exp (I.EClo (__u, (T.coerceSub t)))), T.id)))) in
          evalRedex (Psi, __v, (S, t))
      | (Psi, Lam (UDec _, __P'), (AppBlock (B, S), t)) ->
          evalRedex
            (Psi,
              (evalPrg
                 (Psi,
                   (__P',
                     (T.Dot
                        ((T.Block (I.blockSub (B, (T.coerceSub t)))), T.id))))),
              (S, t))
      | (Psi, Lam (PDec _, __P'), (AppPrg (P, S), t)) ->
          let __v = evalPrg (Psi, (P, t)) in
          let __v' = evalPrg (Psi, (__P', (T.Dot ((T.Prg __v), T.id)))) in
          evalRedex (Psi, __v', (S, t))
    (* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)
    let rec topLevel =
      function
      | (Psi, d, (T.Unit, t)) -> ()
      | (Psi, d, (Let (__d', __P1, Case (__Cs)), t)) ->
          let rec printLF arg__0 arg__1 =
            match (arg__0, arg__1) with
            | ((_, _, _), 0) -> ()
            | ((__g, Dot (Exp (__u), s'), Decl (__g', Dec (Some name, __v))), k) ->
                let _ = printLF (__g, s', __g') (k - 1) in
                print
                  (((((("def " ^ name) ^ " = ") ^ (Print.expToString (__g, __u)))
                       ^ " : ")
                      ^ (Print.expToString (__g, (I.EClo (__v, s')))))
                     ^ "\n") in
          let rec match__ (Psi, t1, Cases ((Psi', t2, P)::C)) =
            let t = createVarSub (Psi, Psi') in
            let t' = T.comp (t2, t) in
            let m = I.ctxLength Psi' in
            let _ = matchSub (Psi, t1, t') in
            let t'' = t in
            let _ =
              printLF
                ((T.coerceCtx Psi), (T.coerceSub t''), (T.coerceCtx Psi'))
                (m - d) in
            ((topLevel (Psi, m, (P, t'')))
              (* Psi |- t : Psi' *)(* Psi' |- t2 . shift(k) : Psi'' *)
              (* T.normalizeSub *)(* Psi |- t'' : Psi' *)) in
          let __v = evalPrg (Psi, (__P1, t)) in
          let __v' = match__ (Psi, (T.Dot ((T.Prg __v), t)), __Cs) in ((__v')
            (* printLF (__g, s, __g') k = ()
             Invariant:
             __g |- s : __g'
          *))
      | (Psi, d,
         (Let (__d, Lam ((UDec (BDec (Some name, (cid, s))) as __d'), __P1), __P2),
          t)) ->
          let _ = print (("new " ^ name) ^ "\n") in
          let __d'' = T.decSub (__d', t) in
          let _ = topLevel ((I.Decl (Psi, __d'')), (d + 1), (__P1, (T.dot1 t))) in
          ()
      | (Psi, d, (Let (__d, __P1, __P2), t)) ->
          let PDec (Some name, F, _, _) = __d in
          let __v = evalPrg (Psi, (__P1, t)) in
          let _ =
            print
              (((^) (((^) (("val " ^ name) ^ " = ") TomegaPrint.prgToString
                        (Psi, __v))
                       ^ " :: ")
                  TomegaPrint.forToString (Psi, F))
                 ^ "\n") in
          let __v' = topLevel (Psi, (d + 1), (__P2, (T.Dot ((T.Prg __v), t)))) in
          __v'(* function definition *)(* new declaration *)
      (* lf value definition *)
    (* in -- removed local *)
    let evalPrg = function | P -> evalPrg (I.Null, (P, T.id))
    let topLevel = function | P -> topLevel (I.Null, 0, (P, T.id))
  end ;;
