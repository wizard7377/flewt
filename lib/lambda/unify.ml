
module type UNIFY  =
  sig
    type nonrec unifTrail(*! structure IntSyn : INTSYN !*)
    (* Author: Frank Pfenning, Carsten Schuermann *)
    (* Unification *)
    val suspend :
      unit ->
        ((unifTrail)(* suspending and resuming trailing *))
    val resume : unifTrail -> unit
    val reset :
      unit ->
        ((unit)(* trailing of variable instantiation *))
    val mark : unit -> unit
    val unwind : unit -> unit
    val instantiateEVar :
      (IntSyn.__Exp option ref * IntSyn.__Exp * IntSyn.cnstr list) -> unit
    val instantiateLVar :
      (IntSyn.__Block option ref * IntSyn.__Block) -> unit
    val resetAwakenCnstrs : unit -> unit
    val nextCnstr : unit -> IntSyn.cnstr option
    val addConstraint : (IntSyn.cnstr list ref * IntSyn.cnstr) -> unit
    val solveConstraint : IntSyn.cnstr -> unit
    val delay : (IntSyn.eclo * IntSyn.cnstr) -> unit
    val intersection :
      (IntSyn.__Sub * IntSyn.__Sub) ->
        ((IntSyn.__Sub)(* unification *))
    exception Unify of string 
    val unify : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val unifyW :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((unit)(* raises Unify *))
    val unifyBlock :
      (IntSyn.dctx * IntSyn.__Block * IntSyn.__Block) ->
        ((unit)(* raises Unify *))
    val unifySub :
      (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub) ->
        ((unit)(* raises Unify *))
    val invertible :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.__Sub * IntSyn.__Exp option ref) ->
        ((bool)(* raises Unify *))
    val invertSub :
      (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub * IntSyn.__Exp option ref)
        -> IntSyn.__Sub
    val unifiable :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((bool)(* unifiable (g, Us,Us') will instantiate EVars as an effect *))
    val unifiable' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((string)(* unifiable' (g, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *))
          option
  end;;




module Unify(Unify:sig
                     module Whnf : WHNF
                     module Trail :
                     ((TRAIL)(* Unification *)(* Author: Frank Pfenning, Carsten Schuermann *)
                     (* Modified: Roberto Virga *)(*! structure IntSyn' : INTSYN !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*))
                   end) : UNIFY =
  struct
    exception Unify of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    exception NotInvertible 
    open IntSyn
    type __Action =
      | Instantiate of __Exp option ref 
      | InstantiateBlock of __Block option ref 
      | Add of cnstr list ref 
      | Solve of (cnstr * __Cnstr) 
    type __CAction =
      | BindCnstr of (__Cnstr ref * __Cnstr) 
    type __FAction =
      | BindExp of (__Exp option ref * __Exp option) 
      | BindBlock of (__Block option ref * __Block option) 
      | BindAdd of (cnstr list ref * __CAction list) 
      | FSolve of (__Cnstr ref * __Cnstr * __Cnstr) 
    type nonrec unifTrail = __FAction Trail.trail
    let globalTrail = (Trail.trail () : __Action Trail.trail)
    let rec copyCnstr =
      function
      | [] -> []
      | refC::clist -> (::) (BindCnstr (refC, (!refC))) copyCnstr clist
    let rec copy =
      function
      | Instantiate refU -> BindExp (refU, (!refU))
      | InstantiateBlock refB -> BindBlock (refB, (!refB))
      | Add (ref (Cnstrs) as cnstrs) ->
          BindAdd (cnstrs, (copyCnstr (!cnstrs)))
      | Solve (cnstr, Cnstr) -> FSolve (cnstr, Cnstr, (!cnstr))
    let rec resetCnstr =
      function
      | [] -> []
      | (BindCnstr (refC, Cnstr))::L ->
          (refC := Cnstr; refC :: (resetCnstr L))
    let rec reset =
      function
      | BindExp (refU, U) -> (refU := U; Instantiate refU)
      | BindBlock (refB, B) -> (refB := B; InstantiateBlock refB)
      | BindAdd (cnstrs, CActions) ->
          ((:=) cnstrs resetCnstr CActions; Add cnstrs)
      | FSolve (refCnstr, Cnstr, Cnstr') ->
          (refCnstr := Cnstr'; Solve (refCnstr, Cnstr))
    let rec suspend () = Trail.suspend (globalTrail, copy)
    let rec resume trail = Trail.resume (trail, globalTrail, reset)
    let rec undo =
      function
      | Instantiate refU -> refU := NONE
      | InstantiateBlock refB -> refB := NONE
      | Add (ref (cnstr::cnstrL) as cnstrs) -> cnstrs := cnstrL
      | Solve (cnstr, Cnstr) -> cnstr := Cnstr
    let rec reset () = Trail.reset globalTrail
    let rec mark () = Trail.mark globalTrail
    let rec unwind () = Trail.unwind (globalTrail, undo)
    let rec addConstraint (cnstrs, cnstr) =
      (cnstrs := cnstr) :: (!cnstrs); Trail.log (globalTrail, (Add cnstrs))
    let rec solveConstraint (ref (Cnstr) as cnstr) =
      cnstr := Solved; Trail.log (globalTrail, (Solve (cnstr, Cnstr)))
    let rec delayExpW =
      function
      | (((Uni (L) as U), s1), _) -> ()
      | ((Pi ((D, P), U), s), cnstr) ->
          (delayDec ((D, s), cnstr); delayExp ((U, (dot1 s)), cnstr))
      | ((Root (H, S), s), cnstr) ->
          (delayHead (H, cnstr); delaySpine ((S, s), cnstr))
      | ((Lam (D, U), s), cnstr) ->
          (delayDec ((D, s), cnstr); delayExp ((U, (dot1 s)), cnstr))
      | ((EVar (g, r, V, cnstrs), s), cnstr) -> addConstraint (cnstrs, cnstr)
      | ((FgnExp csfe, s), cnstr) ->
          FgnExpStd.App.apply csfe (function | U -> delayExp ((U, s), cnstr))
    let rec delayExp (Us, cnstr) = delayExpW ((Whnf.whnf Us), cnstr)
    let rec delayHead =
      function
      | (FVar (x, V, s'), cnstr) -> delayExp ((V, id), cnstr)
      | (H, _) -> ()
    let rec delaySpine =
      function
      | ((Nil, s), cnstr) -> ()
      | ((App (U, S), s), cnstr) ->
          (delayExp ((U, s), cnstr); delaySpine ((S, s), cnstr))
      | ((SClo (S, s'), s), cnstr) -> delaySpine ((S, (comp (s', s))), cnstr)
    let rec delayDec ((Dec (name, V), s), cnstr) = delayExp ((V, s), cnstr)
    let awakenCnstrs = (ref nil : cnstr list ref)
    let rec resetAwakenCnstrs () = awakenCnstrs := nil
    let rec nextCnstr () =
      match !awakenCnstrs with
      | nil -> NONE
      | cnstr::cnstrL -> (awakenCnstrs := cnstrL; SOME cnstr)
    let rec instantiateEVar (refU, V, cnstrL) =
      (:=) refU SOME V;
      Trail.log (globalTrail, (Instantiate refU));
      (!) ((@) (awakenCnstrs := cnstrL)) awakenCnstrs
    let rec instantiateLVar (refB, B) =
      (:=) refB SOME B; Trail.log (globalTrail, (InstantiateBlock refB))
    let rec intersection =
      function
      | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
          if k1 = k2
          then dot1 (intersection (s1, s2))
          else comp ((intersection (s1, s2)), shift)
      | ((Dot _ as s1), Shift n2) ->
          intersection (s1, (Dot ((Idx (n2 + 1)), (Shift (n2 + 1)))))
      | (Shift n1, (Dot _ as s2)) ->
          intersection ((Dot ((Idx (n1 + 1)), (Shift (n1 + 1)))), s2)
      | (Shift _, Shift _) -> id
    let rec weakenSub =
      function
      | (g, Shift n, ss) ->
          if (<) n ctxLength g
          then weakenSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (g, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (g, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (g, s', ss)))
      | (g, Dot (Undef, s'), ss) -> comp ((weakenSub (g, s', ss)), shift)
    let rec invertExp (g, Us, ss, rOccur) =
      invertExpW (g, (Whnf.whnf Us), ss, rOccur)
    let rec invertExpW =
      function
      | (g, ((Uni _ as U), s), _, _) -> U
      | (g, (Pi ((D, P), V), s), ss, rOccur) ->
          Pi
            (((invertDec (g, (D, s), ss, rOccur)), P),
              (invertExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Lam (D, V), s), ss, rOccur) ->
          Lam
            ((invertDec (g, (D, s), ss, rOccur)),
              (invertExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((invertHead (g, H, ss, rOccur)),
              (invertSpine (g, (S, s), ss, rOccur)))
      | (g, ((EVar (r, GX, V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise NotInvertible
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (g, s, ss) in
               if Whnf.isId w
               then EClo (X, (comp (s, ss)))
               else raise NotInvertible)
            else EClo (X, (invertSub (g, s, ss, rOccur)))
      | (g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | U -> invertExp (g, (U, s), ss, rOccur))
    let rec invertDec (g, (Dec (name, V), s), ss, rOccur) =
      Dec (name, (invertExp (g, (V, s), ss, rOccur)))
    let rec invertSpine =
      function
      | (g, (Nil, s), ss, rOccur) -> Nil
      | (g, (App (U, S), s), ss, rOccur) ->
          App
            ((invertExp (g, (U, s), ss, rOccur)),
              (invertSpine (g, (S, s), ss, rOccur)))
      | (g, (SClo (S, s'), s), ss, rOccur) ->
          invertSpine (g, (S, (comp (s', s))), ss, rOccur)
    let rec invertHead =
      function
      | (g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise NotInvertible
           | Idx k' -> BVar k')
      | (g, (Const _ as H), ss, rOccur) -> H
      | (g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (invertSub (g, t, id, rOccur); H)
      | (g, (Skonst _ as H), ss, rOccur) -> H
      | (g, (Def _ as H), ss, rOccur) -> H
      | (g, FVar (x, V, s'), ss, rOccur) ->
          (invertExp (g, (V, id), id, rOccur); FVar (x, V, (comp (s', ss))))
      | (g, (FgnConst _ as H), ss, rOccur) -> H
    let rec invertSub =
      function
      | (g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength g
          then
            invertSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise NotInvertible
           | Ft -> Dot (Ft, (invertSub (g, s', ss, rOccur))))
      | (g, Dot (Exp (U), s'), ss, rOccur) ->
          Dot
            ((Exp (invertExp (g, (U, id), ss, rOccur))),
              (invertSub (g, s', ss, rOccur)))
    let rec pruneExp (g, Us, ss, rOccur) =
      pruneExpW (g, (Whnf.whnf Us), ss, rOccur)
    let rec pruneExpW =
      function
      | (g, ((Uni _ as U), s), _, _) -> U
      | (g, (Pi ((D, P), V), s), ss, rOccur) ->
          Pi
            (((pruneDec (g, (D, s), ss, rOccur)), P),
              (pruneExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Lam (D, V), s), ss, rOccur) ->
          Lam
            ((pruneDec (g, (D, s), ss, rOccur)),
              (pruneExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((pruneHead (g, H, ss, rOccur)),
              (pruneSpine (g, (S, s), ss, rOccur)))
      | (g, ((EVar (r, GX, V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise (Unify "Variable occurrence")
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (g, s, ss) in
               if Whnf.isId w
               then EClo (X, (comp (s, ss)))
               else
                 (let wi = Whnf.invert w in
                  let V' = pruneExp (GX, (V, id), wi, rOccur) in
                  let GY = pruneCtx (wi, GX, rOccur) in
                  let Y = newEVar (GY, V') in
                  let Yw = EClo (Y, w) in
                  let _ = instantiateEVar (r, Yw, (!cnstrs)) in
                  EClo (Yw, (comp (s, ss)))))
            else
              (try EClo (X, (invertSub (g, s, ss, rOccur)))
               with
               | NotInvertible ->
                   let GY = pruneCtx (ss, g, rOccur) in
                   let V' = pruneExp (g, (V, s), ss, rOccur) in
                   let Y = newEVar (GY, V') in
                   let _ =
                     addConstraint
                       (cnstrs,
                         (ref
                            (Eqn
                               (g, (EClo (X, s)),
                                 (EClo (Y, (Whnf.invert ss))))))) in
                   Y)
      | (g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | U -> pruneExp (g, (U, s), ss, rOccur))
      | (g, ((AVar _ as X), s), ss, rOccur) -> raise (Unify "Left-over AVar")
    let rec pruneDec =
      function
      | (g, (Dec (name, V), s), ss, rOccur) ->
          Dec (name, (pruneExp (g, (V, s), ss, rOccur)))
      | (g, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine =
      function
      | (g, (Nil, s), ss, rOccur) -> Nil
      | (g, (App (U, S), s), ss, rOccur) ->
          App
            ((pruneExp (g, (U, s), ss, rOccur)),
              (pruneSpine (g, (S, s), ss, rOccur)))
      | (g, (SClo (S, s'), s), ss, rOccur) ->
          pruneSpine (g, (S, (comp (s', s))), ss, rOccur)
    let rec pruneHead =
      function
      | (g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Unify "Parameter dependency")
           | Idx k' -> BVar k')
      | (g, (Const _ as H), ss, rOccur) -> H
      | (g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (g, t, id, rOccur); H)
      | (g, (Skonst _ as H), ss, rOccur) -> H
      | (g, (Def _ as H), ss, rOccur) -> H
      | (g, FVar (x, V, s'), ss, rOccur) ->
          (pruneExp (g, (V, id), id, rOccur); FVar (x, V, (comp (s', ss))))
      | (g, (FgnConst _ as H), ss, rOccur) -> H
    let rec pruneSub =
      function
      | (g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength g
          then
            pruneSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Unify "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (g, s', ss, rOccur))))
      | (g, Dot (Exp (U), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (g, (U, id), ss, rOccur))),
              (pruneSub (g, s', ss, rOccur)))
    let rec pruneCtx =
      function
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (g, D), rOccur) ->
          let t' = comp (t, invShift) in
          let D' = pruneDec (g, (D, id), t', rOccur) in
          Decl ((pruneCtx (t', g, rOccur)), D')
      | (Dot (Undef, t), Decl (g, d), rOccur) -> pruneCtx (t, g, rOccur)
      | (Shift n, g, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), g, rOccur)
    let rec unifyExpW =
      function
      | (g, ((FgnExp csfe1, _) as us1), us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (g, (EClo us2)) with
           | Succeed residualL ->
               let execResidual =
                 function
                 | Assign (g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (g, (W, id), ss, r) in
                     instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (g, us1, ((FgnExp csfe2, _) as us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (g, (EClo us1)) with
           | Succeed opL ->
               let execOp =
                 function
                 | Assign (g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (g, (W, id), ss, r) in
                     instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (g, (Uni (L1), _), (Uni (L2), _)) -> ()
      | (g, ((Root (H1, s1), s1) as us1), ((Root (H2, s2), s2) as us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then unifySpine (g, (s1, s1), (s2, s2))
               else raise (Unify "Bound variable clash")
           | (Const c1, Const c2) ->
               if c1 = c2
               then unifySpine (g, (s1, s1), (s2, s2))
               else raise (Unify "Constant clash")
           | (Proj (b1, i1), Proj (b2, i2)) ->
               if i1 = i2
               then
                 (unifyBlock (g, b1, b2); unifySpine (g, (s1, s1), (s2, s2)))
               else raise (Unify "Global parameter clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then unifySpine (g, (s1, s1), (s2, s2))
               else raise (Unify "Skolem constant clash")
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               if n1 = n2
               then unifySpine (g, (s1, s1), (s2, s2))
               else raise (Unify "Free variable clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then unifySpine (g, (s1, s1), (s2, s2))
               else unifyDefDefW (g, us1, us2)
           | (Def d1, Const c2) ->
               (match defAncestor d1 with
                | Anc (_, _, NONE) ->
                    unifyExpW (g, (Whnf.expandDef us1), us2)
                | Anc (_, _, SOME c1) ->
                    if c1 = c2
                    then unifyExpW (g, (Whnf.expandDef us1), us2)
                    else raise (Unify "Constant clash"))
           | (Const c1, Def d2) ->
               (match defAncestor d2 with
                | Anc (_, _, NONE) ->
                    unifyExpW (g, us1, (Whnf.expandDef us2))
                | Anc (_, _, SOME c2) ->
                    if c1 = c2
                    then unifyExpW (g, us1, (Whnf.expandDef us2))
                    else raise (Unify "Constant clash"))
           | (Def d1, BVar k2) -> raise (Unify "Head mismatch")
           | (BVar k1, Def d2) -> raise (Unify "Head mismatch")
           | (Def d1, _) -> unifyExpW (g, (Whnf.expandDef us1), us2)
           | (_, Def d2) -> unifyExpW (g, us1, (Whnf.expandDef us2))
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else raise (Unify "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else unifyExp (g, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               unifyExp (g, (W1, s1), us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               unifyExp (g, us1, (W2, s2))
           | _ -> raise (Unify "Head mismatch"))
      | (g, (Pi ((D1, _), u1), s1), (Pi ((D2, _), u2), s2)) ->
          (unifyDec (g, (D1, s1), (D2, s2));
           unifyExp
             ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)),
               (u2, (dot1 s2))))
      | (g, ((Pi (_, _), _) as us1), ((Root (Def _, _), _) as us2)) ->
          unifyExpW (g, us1, (Whnf.expandDef us2))
      | (g, ((Root (Def _, _), _) as us1), ((Pi (_, _), _) as us2)) ->
          unifyExpW (g, (Whnf.expandDef us1), us2)
      | (g, (Lam (D1, u1), s1), (Lam (D2, u2), s2)) ->
          unifyExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)), (u2, (dot1 s2)))
      | (g, (Lam (D1, u1), s1), (u2, s2)) ->
          unifyExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)),
              ((Redex
                  ((EClo (u2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (g, (u1, s1), (Lam (D2, u2), s2)) ->
          unifyExp
            ((Decl (g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (u1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (u2, (dot1 s2)))
      | (g, (((EVar (r1, G1, V1, cnstrs1) as u1), s1) as us1),
         (((EVar (r2, G2, V2, cnstrs2) as u2), s2) as us2)) ->
          if r1 = r2
          then
            (if Whnf.isPatSub s1
             then
               (if Whnf.isPatSub s2
                then
                  let s' = intersection (s1, s2) in
                  (if Whnf.isId s'
                   then ()
                   else
                     (let ss' = Whnf.invert s' in
                      let V1' = EClo (V1, ss') in
                      let G1' = Whnf.strengthen (ss', G1) in
                      instantiateEVar
                        (r1, (EClo ((newEVar (G1', V1')), s')), (!cnstrs1))))
                else
                  addConstraint
                    (cnstrs2, (ref (Eqn (g, (EClo us2), (EClo us1))))))
             else
               addConstraint
                 (cnstrs1, (ref (Eqn (g, (EClo us1), (EClo us2))))))
          else
            if Whnf.isPatSub s1
            then
              (let ss1 = Whnf.invert s1 in
               let u2' = pruneExp (g, us2, ss1, r1) in
               instantiateEVar (r1, u2', (!cnstrs1)))
            else
              if Whnf.isPatSub s2
              then
                (let ss2 = Whnf.invert s2 in
                 let u1' = pruneExp (g, us1, ss2, r2) in
                 instantiateEVar (r2, u1', (!cnstrs2)))
              else
                (let cnstr = ref (Eqn (g, (EClo us1), (EClo us2))) in
                 addConstraint (cnstrs1, cnstr))
      | (g, ((EVar (r, GX, V, cnstrs), s) as us1), ((u2, s2) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let u2' = pruneExp (g, us2, ss, r) in
            instantiateEVar (r, u2', (!cnstrs))
          else
            addConstraint (cnstrs, (ref (Eqn (g, (EClo us1), (EClo us2)))))
      | (g, ((u1, s1) as us1), ((EVar (r, GX, V, cnstrs), s) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let u1' = pruneExp (g, us1, ss, r) in
            instantiateEVar (r, u1', (!cnstrs))
          else
            addConstraint (cnstrs, (ref (Eqn (g, (EClo us1), (EClo us2)))))
      | (g, us1, us2) -> raise (Unify "Expression clash")
    let rec unifyExp (g, ((E1, s1) as us1), ((E2, s2) as us2)) =
      unifyExpW (g, (Whnf.whnf us1), (Whnf.whnf us2))
    let rec unifyDefDefW
      (g, ((Root (Def d1, s1), s1) as us1), ((Root (Def d2, s2), s2) as us2))
      =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (SOME c1, SOME c2) ->
            if c1 <> c2
            then raise (Unify "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      match Int.compare (h1, h2) with
      | EQUAL -> unifyExpW (g, (Whnf.expandDef us1), (Whnf.expandDef us2))
      | LESS -> unifyExpW (g, us1, (Whnf.expandDef us2))
      | GREATER -> unifyExpW (g, (Whnf.expandDef us1), us2)
    let rec unifySpine =
      function
      | (g, (Nil, _), (Nil, _)) -> ()
      | (g, (SClo (s1, s1'), s1), Ss) ->
          unifySpine (g, (s1, (comp (s1', s1))), Ss)
      | (g, Ss, (SClo (s2, s2'), s2)) ->
          unifySpine (g, Ss, (s2, (comp (s2', s2))))
      | (g, (App (u1, s1), s1), (App (u2, s2), s2)) ->
          (unifyExp (g, (u1, s1), (u2, s2));
           unifySpine (g, (s1, s1), (s2, s2)))
    let rec unifyDec (g, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
      unifyExp (g, (V1, s1), (V2, s2))
    let rec unifySub =
      function
      | (g, Shift n1, Shift n2) -> ()
      | (g, Shift n, (Dot _ as s2)) ->
          unifySub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (g, (Dot _ as s1), Shift m) ->
          unifySub (g, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (g, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 <> n2
                then raise (Error "SOME variables mismatch")
                else ()
            | (Exp (u1), Exp (u2)) -> unifyExp (g, (u1, id), (u2, id))
            | (Exp (u1), Idx n2) ->
                unifyExp (g, (u1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (u2)) ->
                unifyExp (g, ((Root ((BVar n1), Nil)), id), (u2, id)));
           unifySub (g, s1, s2))
    let rec unifyBlock =
      function
      | (g, LVar (ref (SOME (B1)), s, _), B2) ->
          unifyBlock (g, (blockSub (B1, s)), B2)
      | (g, B1, LVar (ref (SOME (B2)), s, _)) ->
          unifyBlock (g, B1, (blockSub (B2, s)))
      | (g, B1, B2) -> unifyBlockW (g, B1, B2)
    let rec unifyBlockW =
      function
      | (g, LVar (r1, (Shift k1 as s1), (l1, t1)), LVar
         (r2, (Shift k2 as s2), (l2, t2))) ->
          if l1 <> l2
          then raise (Unify "Label clash")
          else
            if r1 = r2
            then ()
            else
              (unifySub (g, (comp (t1, s1)), (comp (t2, s2)));
               if k1 < k2
               then
                 instantiateLVar
                   (r1, (LVar (r2, (Shift (k2 - k1)), (l2, t2))))
               else
                 instantiateLVar
                   (r2, (LVar (r1, (Shift (k1 - k2)), (l1, t1)))))
      | (g, LVar (r1, s1, (l1, t1)), B2) ->
          instantiateLVar (r1, (blockSub (B2, (Whnf.invert s1))))
      | (g, B1, LVar (r2, s2, (l2, t2))) ->
          instantiateLVar (r2, (blockSub (B1, (Whnf.invert s2))))
      | (g, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Unify "Block index clash") else ()
    let rec unify1W (g, us1, us2) =
      unifyExpW (g, us1, us2); awakeCnstr (nextCnstr ())
    let rec unify1 (g, us1, us2) =
      unifyExp (g, us1, us2); awakeCnstr (nextCnstr ())
    let rec awakeCnstr =
      function
      | NONE -> ()
      | SOME (ref (Solved)) -> awakeCnstr (nextCnstr ())
      | SOME (ref (Eqn (g, u1, u2)) as cnstr) ->
          (solveConstraint cnstr; unify1 (g, (u1, id), (u2, id)))
      | SOME (ref (FgnCnstr csfc)) ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Unify "Foreign constraint violated")
    let rec unifyW (g, us1, us2) =
      resetAwakenCnstrs (); unify1W (g, us1, us2)
    let rec unify (g, us1, us2) = resetAwakenCnstrs (); unify1 (g, us1, us2)
    type nonrec unifTrail =
      ((unifTrail)(*
      | unifyBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | unifyBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
      (* Sat Dec  8 11:49:16 2001 -fp !!! *)(* How can the next case arise? *)
      (* -- ABP *)(*      | unifyBlockW (g, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP *)
      (* -- ABP *)(* -- ABP *)(* was: unifySub (g, t1, t2)  Jul 22 2010 *)
      (* Sat Dec  7 22:04:31 2002 -fp *)(* Sat Dec  8 11:47:12 2001 -fp !!! *)
      (* substitutions s1 and s2 were redundant here --- removed *)
      (* not possible because of invariant? -cs *)(*         | (Undef, Undef) =>
           | _ => false *)
      (* by invariant *)(* Thu Dec  6 21:01:09 2001 -fp *)
      (* conjecture: g == Null at all times *)(* unifySub (g, s1, s2) = ()

       Invariant:
       If   g |- s1 : g'
       and  g |- s2 : g'
       then unifySub (g, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of SOME variables
    *)
      (* Nil/App or App/Nil cannot occur by typing invariants *)
      (* unifySpine (g, (s1, s1), (s2, s2)) = ()

       Invariant:
       If   g |- s1 : G1   G1 |- s1 : V1 > W1
       and  g |- s2 : G2   G2 |- s2 : V2 > W2
       and  g |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  g |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. g |- s1 [s1] <I> == s2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
      (* conservative *)(*  unifyExpW (g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
      (* unifyExp (g, (u1, s1), (u2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf
    *)
      (* the cases for EClo or Redex should not occur because of whnf invariant *)
      (* covers most remaining cases *)(* invertExpW (us1, s, r) *)
      (* instantiateEVar (r, EClo (u1, comp(s1, ss)), !cnstrs) *)
      (* invertExpW (us2, s, r) *)(* instantiateEVar (r, EClo (u2, comp(s2, ss)), !cnstrs) *)
      (* invertExpW (us1, s2, ref NONE) *)(* instantiateEVar (r2, EClo (u1, comp(s1, ss2)), !cnstr2) *)
      (* invertExpW (us2, s1, ref NONE) *)(* instantiateEVar (r1, EClo (u2, comp(s2, ss1)), !cnstrs1) *)
      (* invertExp ((V1, id), s', ref NONE) *)(* X[s] = X[s] *)
      (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)(* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
      (* compute ss' directly? *)(* postpone, if s1 or s2 are not patsub *)
      (* same reasoning holds as above *)(* Cannot occur if expressions are eta expanded *)
      (* for rhs:  (u2[s2])[^] 1 = u2 [s2 o ^] 1 = u2 [^ o (1. s2 o ^)] 1
                        = (u2 [^] 1) [1.s2 o ^] *)
      (* ETA: can't occur if eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
      (* we require unique string representation of external constants *)
      (* next two cases for def/fgn, fgn/def *)(* due to strictness! *)
      (* due to strictness! *)(* conservative *)
      (* conservative *)(* four new cases for defined constants *)
      (*  unifyExpW (g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
      (* because of strict *)(* order of calls critical to establish unifySpine invariant *)
      (* s1 = s2 = id by whnf *)(* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
      (* L1 = L2 = type, by invariant *)(* unifyExpW (g, (u1, s1), (u2, s2)) = ()

       Invariant:
       If   g |- s1 : G1   G1 |- u1 : V1    (u1,s1) in whnf
       and  g |- s2 : G2   G2 |- u2 : V2    (u2,s2) in whnf
       and  g |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, u1, s2, u2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. g |- u1 [s1] <I> == u2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
      (* Pruning establishes and maintains this invariant *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* pruneSub (g, Dot (Undef, s), ss, rOccur) is impossible *)
      (* below my raise Unify *)(* must be defined *)
      (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
      (* pruneSub never allows pruning OUTDATED *)(* why g here? -fp !!! *)
      (* perform occurs-check for r only *)(* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* Changed from Null to g Sat Dec  7 21:58:00 2002 -fp *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* so we perform only the occurs-check here as for FVars *)
      (* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
      (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
      (* other cases impossible since (U,s1) whnf *)
      (* this case should never happen! *)(* prune or invert??? *)
      (* val V' = EClo (V, comp (s, ss)) *)(* prune or invert??? *)
      (* shortcuts possible by invariants on g? *)(* val GY = Whnf.strengthen (ss, g) *)
      (* s not patsub *)(* could optimize by checking for identity subst *)
      (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
      (* val GY = Whnf.strengthen (wi, GX) *)(* val V' = EClo (V, wi) *)
      (* = id *)(* prune (g, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       g |- U : V    g' |- s : g  (g' |- U[s] : V[s])
       g'' |- ss : g'
       !!! i would say
       g |- s : g'   g' |- U : V  (g  |- U[s] : V[s])
       g'' |- ss : g

       Effect: prunes EVars in U[s] according to ss
               raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
      (*
    and invertCtx (Shift n, Null, rOccur) = Null
      | invertCtx (Dot (Idx k, t), Decl (g, D), rOccur) =
        let
          val t' = comp (t, invShift)
          val D' = invertDec (g, (D, id), t', rOccur)
        in
          Decl (invertCtx (t', g, rOccur), D')
        end
      | invertCtx (Dot (Undef, t), Decl (g, d), rOccur) =
          invertCtx (t, g, rOccur)
      | invertCtx (Shift n, g, rOccur) =
          invertCtx (Dot (Idx (n+1), Shift (n+1)), g, rOccur)
    *)
      (* invertCtx does not appear to be necessary *)
      (* Pruning establishes and maintains this invariant *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* pruneSub (g, Dot (Undef, s), ss, rOccur) is impossible *)
      (* below my raise NotInvertible *)(* must be defined *)
      (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
      (* pruneSub never allows pruning OUTDATED *)(* why g here? -fp !!! *)
      (* perform occurs-check for r only *)(* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* Changed from Null to g Sat Dec  7 21:58:00 2002 -fp *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* so we perform only the occurs-check here as for FVars *)
      (* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
      (* other cases impossible since (U,s1) whnf *)
      (* invertExp may raise NotInvertible *)(* s not patsub *)
      (* = id *)(* invert (g, (U, s), ss, rOccur) = U[s][ss]

       g |- s : g'   g' |- U : V  (g |- U[s] : V[s])
       g'' |- ss : g

       Effect: raises NotInvertible if U[s][ss] does not exist
               or rOccurs occurs in U[s]
               does NOT prune EVars in U[s] according to ss; fails instead
    *)
      (* no other cases, ss is strsub *)(* w' weaksub *)
      (* ss strsub *)(* weakenSub (G1, s, ss) = w'

       Invariant:
       If    g |- s : G1        s patsub *)
      (* all other cases impossible for pattern substitutions *)
      (* both substitutions are the same number of shifts by invariant *)
      (* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)

       Invariant:
       If   g |- s1 : g'    s1 patsub
       and  g |- s2 : g'    s2 patsub
       then g |- s' : g'' for some g''
       and  s' patsub
    *)
      (* local *)(* Instantiating LVars  *)
      (* Instantiating EVars  *)(* delayDec see delayExp *)
      (* delaySpine ((S, s), cnstr) = ()

       Invariant:
       If   g' |- s : g    g |- S : V > W
       then      g  |- S' : V' > W'
       the constraint cnstr is added to all the rigid EVar occurrences in S[s]
    *)
      (* delayHead (H, s, rOccur) = ()

       Invariant:
       If   g' |- H : V
       and  g' |- s : g         s is a pattern substitution
       then
       the constraint cnstr is added to a total of n rigid EVar occurrences in H[s]
    *)
      (* delayExp ((U, s), cnstr) = ()
       as in delayExpCW, except that the argument may not be in whnf
    *)
      (* no other cases by invariant *)(* s = id *)
      (* delayExpW ((U, s), cnstr) = ()

       Invariant:
       If   g' |- s : g    g |- U : V    (U,s)  in whnf
       then
       the constraint cnstr is added to all the rigid EVar occurrences in U[s]
    *)
      (* Associate a constraint to an expression *)(* ? *))
    let reset = reset
    let mark = mark
    let unwind = unwind
    let suspend = suspend
    let resume = resume
    let delay = delayExp
    let instantiateEVar = instantiateEVar
    let instantiateLVar = instantiateLVar
    let resetAwakenCnstrs = resetAwakenCnstrs
    let nextCnstr = nextCnstr
    let addConstraint = addConstraint
    let solveConstraint = solveConstraint
    let intersection = intersection
    let unifyW = unifyW
    let unify = unify
    let unifySub = unifySub
    let unifyBlock = unifyBlock
    let rec invertible (g, Us, ss, rOccur) =
      try invertExp (g, Us, ss, rOccur); true__
      with | NotInvertible -> false__
    let invertSub = invertSub
    let rec unifiable (g, us1, us2) =
      try unify (g, us1, us2); true__ with | Unify msg -> false__
    let rec unifiable' (g, us1, us2) =
      try unify (g, us1, us2); NONE with | Unify msg -> SOME msg
  end ;;
