
(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type UNIFY  =
  sig
    (*! structure IntSyn : INTSYN !*)
    type nonrec unifTrail
    (* suspending and resuming trailing *)
    val suspend : unit -> unifTrail
    val resume : unifTrail -> unit
    (* trailing of variable instantiation *)
    val reset : unit -> unit
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
    (* unification *)
    val intersection : (IntSyn.__Sub * IntSyn.__Sub) -> IntSyn.__Sub
    exception Unify of string 
    val unify : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    (* raises Unify *)
    val unifyW : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    (* raises Unify *)
    val unifyBlock : (IntSyn.dctx * IntSyn.__Block * IntSyn.__Block) -> unit
    (* raises Unify *)
    val unifySub : (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub) -> unit
    (* raises Unify *)
    val invertible :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.__Sub * IntSyn.__Exp option ref) ->
        bool
    val invertSub :
      (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub * IntSyn.__Exp option ref)
        -> IntSyn.__Sub
    (* unifiable (__g, __Us,__Us') will instantiate EVars as an effect *)
    val unifiable : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    (* unifiable' (__g, __Us,__Us') is like unifiable, but returns None for
     success and Some(msg) for failure *)
    val unifiable' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> string option
  end;;




(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module Unify(Unify:sig
                     (*! structure IntSyn' : INTSYN !*)
                     module Whnf : WHNF
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     module Trail : TRAIL
                   end) : UNIFY =
  struct
    (*! structure IntSyn = IntSyn' !*)
    exception Unify of string 
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
      | (BindCnstr (refC, Cnstr))::__l ->
          (refC := Cnstr; refC :: (resetCnstr __l))
    let rec reset =
      function
      | BindExp (refU, __u) -> (refU := __u; Instantiate refU)
      | BindBlock (refB, B) -> (refB := B; InstantiateBlock refB)
      | BindAdd (cnstrs, CActions) ->
          ((:=) cnstrs resetCnstr CActions; Add cnstrs)
      | FSolve (refCnstr, Cnstr, Cnstr') ->
          (refCnstr := Cnstr'; Solve (refCnstr, Cnstr))
    let rec suspend () = Trail.suspend (globalTrail, copy)
    let rec resume trail = Trail.resume (trail, globalTrail, reset)
    let rec undo =
      function
      | Instantiate refU -> refU := None
      | InstantiateBlock refB -> refB := None
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
      | (((Uni (__l) as __u), s1), _) -> ()
      | ((Pi ((__d, P), __u), s), cnstr) ->
          (delayDec ((__d, s), cnstr); delayExp ((__u, (dot1 s)), cnstr))
      | ((Root (H, S), s), cnstr) ->
          (delayHead (H, cnstr); delaySpine ((S, s), cnstr))
      | ((Lam (__d, __u), s), cnstr) ->
          (delayDec ((__d, s), cnstr); delayExp ((__u, (dot1 s)), cnstr))
      | ((EVar (__g, r, __v, cnstrs), s), cnstr) -> addConstraint (cnstrs, cnstr)
      | ((FgnExp csfe, s), cnstr) ->
          FgnExpStd.App.apply csfe (function | __u -> delayExp ((__u, s), cnstr))
    let rec delayExp (__Us, cnstr) = delayExpW ((Whnf.whnf __Us), cnstr)
    let rec delayHead =
      function
      | (FVar (x, __v, s'), cnstr) -> delayExp ((__v, id), cnstr)
      | (H, _) -> ()
    let rec delaySpine =
      function
      | ((Nil, s), cnstr) -> ()
      | ((App (__u, S), s), cnstr) ->
          (delayExp ((__u, s), cnstr); delaySpine ((S, s), cnstr))
      | ((SClo (S, s'), s), cnstr) -> delaySpine ((S, (comp (s', s))), cnstr)
    let rec delayDec ((Dec (name, __v), s), cnstr) = delayExp ((__v, s), cnstr)
    let awakenCnstrs = (ref nil : cnstr list ref)
    let rec resetAwakenCnstrs () = awakenCnstrs := nil
    let rec nextCnstr () =
      match !awakenCnstrs with
      | nil -> None
      | cnstr::cnstrL -> (awakenCnstrs := cnstrL; Some cnstr)
    let rec instantiateEVar (refU, __v, cnstrL) =
      (:=) refU Some __v;
      Trail.log (globalTrail, (Instantiate refU));
      (!) ((@) (awakenCnstrs := cnstrL)) awakenCnstrs
    let rec instantiateLVar (refB, B) =
      (:=) refB Some B; Trail.log (globalTrail, (InstantiateBlock refB))
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
      | (__g, Shift n, ss) ->
          if (<) n ctxLength __g
          then weakenSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (__g, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (__g, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (__g, s', ss)))
      | (__g, Dot (Undef, s'), ss) -> comp ((weakenSub (__g, s', ss)), shift)
    let rec invertExp (__g, __Us, ss, rOccur) =
      invertExpW (__g, (Whnf.whnf __Us), ss, rOccur)
    let rec invertExpW =
      function
      | (__g, ((Uni _ as __u), s), _, _) -> __u
      | (__g, (Pi ((__d, P), __v), s), ss, rOccur) ->
          Pi
            (((invertDec (__g, (__d, s), ss, rOccur)), P),
              (invertExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Lam (__d, __v), s), ss, rOccur) ->
          Lam
            ((invertDec (__g, (__d, s), ss, rOccur)),
              (invertExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((invertHead (__g, H, ss, rOccur)),
              (invertSpine (__g, (S, s), ss, rOccur)))
      | (__g, ((EVar (r, GX, __v, cnstrs) as x), s), ss, rOccur) ->
          if rOccur = r
          then raise NotInvertible
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (__g, s, ss) in
               if Whnf.isId w
               then EClo (x, (comp (s, ss)))
               else raise NotInvertible)
            else EClo (x, (invertSub (__g, s, ss, rOccur)))
      | (__g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | __u -> invertExp (__g, (__u, s), ss, rOccur))
    let rec invertDec (__g, (Dec (name, __v), s), ss, rOccur) =
      Dec (name, (invertExp (__g, (__v, s), ss, rOccur)))
    let rec invertSpine =
      function
      | (__g, (Nil, s), ss, rOccur) -> Nil
      | (__g, (App (__u, S), s), ss, rOccur) ->
          App
            ((invertExp (__g, (__u, s), ss, rOccur)),
              (invertSpine (__g, (S, s), ss, rOccur)))
      | (__g, (SClo (S, s'), s), ss, rOccur) ->
          invertSpine (__g, (S, (comp (s', s))), ss, rOccur)
    let rec invertHead =
      function
      | (__g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise NotInvertible
           | Idx k' -> BVar k')
      | (__g, (Const _ as H), ss, rOccur) -> H
      | (__g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (invertSub (__g, t, id, rOccur); H)
      | (__g, (Skonst _ as H), ss, rOccur) -> H
      | (__g, (Def _ as H), ss, rOccur) -> H
      | (__g, FVar (x, __v, s'), ss, rOccur) ->
          (invertExp (__g, (__v, id), id, rOccur); FVar (x, __v, (comp (s', ss))))
      | (__g, (FgnConst _ as H), ss, rOccur) -> H
    let rec invertSub =
      function
      | (__g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __g
          then
            invertSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise NotInvertible
           | Ft -> Dot (Ft, (invertSub (__g, s', ss, rOccur))))
      | (__g, Dot (Exp (__u), s'), ss, rOccur) ->
          Dot
            ((Exp (invertExp (__g, (__u, id), ss, rOccur))),
              (invertSub (__g, s', ss, rOccur)))
    let rec pruneExp (__g, __Us, ss, rOccur) =
      pruneExpW (__g, (Whnf.whnf __Us), ss, rOccur)
    let rec pruneExpW =
      function
      | (__g, ((Uni _ as __u), s), _, _) -> __u
      | (__g, (Pi ((__d, P), __v), s), ss, rOccur) ->
          Pi
            (((pruneDec (__g, (__d, s), ss, rOccur)), P),
              (pruneExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Lam (__d, __v), s), ss, rOccur) ->
          Lam
            ((pruneDec (__g, (__d, s), ss, rOccur)),
              (pruneExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((pruneHead (__g, H, ss, rOccur)),
              (pruneSpine (__g, (S, s), ss, rOccur)))
      | (__g, ((EVar (r, GX, __v, cnstrs) as x), s), ss, rOccur) ->
          if rOccur = r
          then raise (Unify "Variable occurrence")
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (__g, s, ss) in
               if Whnf.isId w
               then EClo (x, (comp (s, ss)))
               else
                 (let wi = Whnf.invert w in
                  let __v' = pruneExp (GX, (__v, id), wi, rOccur) in
                  let GY = pruneCtx (wi, GX, rOccur) in
                  let y = newEVar (GY, __v') in
                  let Yw = EClo (y, w) in
                  let _ = instantiateEVar (r, Yw, (!cnstrs)) in
                  EClo (Yw, (comp (s, ss)))))
            else
              (try EClo (x, (invertSub (__g, s, ss, rOccur)))
               with
               | NotInvertible ->
                   let GY = pruneCtx (ss, __g, rOccur) in
                   let __v' = pruneExp (__g, (__v, s), ss, rOccur) in
                   let y = newEVar (GY, __v') in
                   let _ =
                     addConstraint
                       (cnstrs,
                         (ref
                            (Eqn
                               (__g, (EClo (x, s)),
                                 (EClo (y, (Whnf.invert ss))))))) in
                   y)
      | (__g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | __u -> pruneExp (__g, (__u, s), ss, rOccur))
      | (__g, ((AVar _ as x), s), ss, rOccur) -> raise (Unify "Left-over AVar")
    let rec pruneDec =
      function
      | (__g, (Dec (name, __v), s), ss, rOccur) ->
          Dec (name, (pruneExp (__g, (__v, s), ss, rOccur)))
      | (__g, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine =
      function
      | (__g, (Nil, s), ss, rOccur) -> Nil
      | (__g, (App (__u, S), s), ss, rOccur) ->
          App
            ((pruneExp (__g, (__u, s), ss, rOccur)),
              (pruneSpine (__g, (S, s), ss, rOccur)))
      | (__g, (SClo (S, s'), s), ss, rOccur) ->
          pruneSpine (__g, (S, (comp (s', s))), ss, rOccur)
    let rec pruneHead =
      function
      | (__g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Unify "Parameter dependency")
           | Idx k' -> BVar k')
      | (__g, (Const _ as H), ss, rOccur) -> H
      | (__g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (__g, t, id, rOccur); H)
      | (__g, (Skonst _ as H), ss, rOccur) -> H
      | (__g, (Def _ as H), ss, rOccur) -> H
      | (__g, FVar (x, __v, s'), ss, rOccur) ->
          (pruneExp (__g, (__v, id), id, rOccur); FVar (x, __v, (comp (s', ss))))
      | (__g, (FgnConst _ as H), ss, rOccur) -> H
    let rec pruneSub =
      function
      | (__g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __g
          then
            pruneSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Unify "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (__g, s', ss, rOccur))))
      | (__g, Dot (Exp (__u), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (__g, (__u, id), ss, rOccur))),
              (pruneSub (__g, s', ss, rOccur)))
    let rec pruneCtx =
      function
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (__g, __d), rOccur) ->
          let t' = comp (t, invShift) in
          let __d' = pruneDec (__g, (__d, id), t', rOccur) in
          Decl ((pruneCtx (t', __g, rOccur)), __d')
      | (Dot (Undef, t), Decl (__g, d), rOccur) -> pruneCtx (t, __g, rOccur)
      | (Shift n, __g, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __g, rOccur)
    let rec unifyExpW =
      function
      | (__g, ((FgnExp csfe1, _) as us1), us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (__g, (EClo us2)) with
           | Succeed residualL ->
               let rec execResidual =
                 function
                 | Assign (__g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (__g, (W, id), ss, r) in
                     instantiateEVar (r, W', (!cnstrs))
                 | Delay (__u, cnstr) -> delayExp ((__u, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (__g, us1, ((FgnExp csfe2, _) as us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (__g, (EClo us1)) with
           | Succeed opL ->
               let rec execOp =
                 function
                 | Assign (__g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (__g, (W, id), ss, r) in
                     instantiateEVar (r, W', (!cnstrs))
                 | Delay (__u, cnstr) -> delayExp ((__u, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (__g, (Uni (L1), _), (Uni (L2), _)) -> ()
      | (__g, ((Root (H1, S1), s1) as us1), ((Root (H2, S2), s2) as us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then unifySpine (__g, (S1, s1), (S2, s2))
               else raise (Unify "Bound variable clash")
           | (Const c1, Const c2) ->
               if c1 = c2
               then unifySpine (__g, (S1, s1), (S2, s2))
               else raise (Unify "Constant clash")
           | (Proj (b1, i1), Proj (b2, i2)) ->
               if i1 = i2
               then
                 (unifyBlock (__g, b1, b2); unifySpine (__g, (S1, s1), (S2, s2)))
               else raise (Unify "Global parameter clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then unifySpine (__g, (S1, s1), (S2, s2))
               else raise (Unify "Skolem constant clash")
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               if n1 = n2
               then unifySpine (__g, (S1, s1), (S2, s2))
               else raise (Unify "Free variable clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then unifySpine (__g, (S1, s1), (S2, s2))
               else unifyDefDefW (__g, us1, us2)
           | (Def d1, Const c2) ->
               (match defAncestor d1 with
                | Anc (_, _, None) ->
                    unifyExpW (__g, (Whnf.expandDef us1), us2)
                | Anc (_, _, Some c1) ->
                    if c1 = c2
                    then unifyExpW (__g, (Whnf.expandDef us1), us2)
                    else raise (Unify "Constant clash"))
           | (Const c1, Def d2) ->
               (match defAncestor d2 with
                | Anc (_, _, None) ->
                    unifyExpW (__g, us1, (Whnf.expandDef us2))
                | Anc (_, _, Some c2) ->
                    if c1 = c2
                    then unifyExpW (__g, us1, (Whnf.expandDef us2))
                    else raise (Unify "Constant clash"))
           | (Def d1, BVar k2) -> raise (Unify "Head mismatch")
           | (BVar k1, Def d2) -> raise (Unify "Head mismatch")
           | (Def d1, _) -> unifyExpW (__g, (Whnf.expandDef us1), us2)
           | (_, Def d2) -> unifyExpW (__g, us1, (Whnf.expandDef us2))
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else raise (Unify "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, __v, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else unifyExp (__g, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               unifyExp (__g, (W1, s1), us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               unifyExp (__g, us1, (W2, s2))
           | _ -> raise (Unify "Head mismatch"))
      | (__g, (Pi ((D1, _), __U1), s1), (Pi ((D2, _), __U2), s2)) ->
          (unifyDec (__g, (D1, s1), (D2, s2));
           unifyExp
             ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)),
               (__U2, (dot1 s2))))
      | (__g, ((Pi (_, _), _) as us1), ((Root (Def _, _), _) as us2)) ->
          unifyExpW (__g, us1, (Whnf.expandDef us2))
      | (__g, ((Root (Def _, _), _) as us1), ((Pi (_, _), _) as us2)) ->
          unifyExpW (__g, (Whnf.expandDef us1), us2)
      | (__g, (Lam (D1, __U1), s1), (Lam (D2, __U2), s2)) ->
          unifyExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)), (__U2, (dot1 s2)))
      | (__g, (Lam (D1, __U1), s1), (__U2, s2)) ->
          unifyExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (__g, (__U1, s1), (Lam (D2, __U2), s2)) ->
          unifyExp
            ((Decl (__g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)))
      | (__g, (((EVar (r1, G1, V1, cnstrs1) as __U1), s1) as us1),
         (((EVar (r2, G2, V2, cnstrs2) as __U2), s2) as us2)) ->
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
                    (cnstrs2, (ref (Eqn (__g, (EClo us2), (EClo us1))))))
             else
               addConstraint
                 (cnstrs1, (ref (Eqn (__g, (EClo us1), (EClo us2))))))
          else
            if Whnf.isPatSub s1
            then
              (let ss1 = Whnf.invert s1 in
               let __U2' = pruneExp (__g, us2, ss1, r1) in
               instantiateEVar (r1, __U2', (!cnstrs1)))
            else
              if Whnf.isPatSub s2
              then
                (let ss2 = Whnf.invert s2 in
                 let __U1' = pruneExp (__g, us1, ss2, r2) in
                 instantiateEVar (r2, __U1', (!cnstrs2)))
              else
                (let cnstr = ref (Eqn (__g, (EClo us1), (EClo us2))) in
                 addConstraint (cnstrs1, cnstr))
      | (__g, ((EVar (r, GX, __v, cnstrs), s) as us1), ((__U2, s2) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let __U2' = pruneExp (__g, us2, ss, r) in
            instantiateEVar (r, __U2', (!cnstrs))
          else
            addConstraint (cnstrs, (ref (Eqn (__g, (EClo us1), (EClo us2)))))
      | (__g, ((__U1, s1) as us1), ((EVar (r, GX, __v, cnstrs), s) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let __U1' = pruneExp (__g, us1, ss, r) in
            instantiateEVar (r, __U1', (!cnstrs))
          else
            addConstraint (cnstrs, (ref (Eqn (__g, (EClo us1), (EClo us2)))))
      | (__g, us1, us2) -> raise (Unify "Expression clash")
    let rec unifyExp (__g, ((E1, s1) as us1), ((E2, s2) as us2)) =
      unifyExpW (__g, (Whnf.whnf us1), (Whnf.whnf us2))
    let rec unifyDefDefW
      (__g, ((Root (Def d1, S1), s1) as us1), ((Root (Def d2, S2), s2) as us2))
      =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (Some c1, Some c2) ->
            if c1 <> c2
            then raise (Unify "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      match Int.compare (h1, h2) with
      | EQUAL -> unifyExpW (__g, (Whnf.expandDef us1), (Whnf.expandDef us2))
      | LESS -> unifyExpW (__g, us1, (Whnf.expandDef us2))
      | GREATER -> unifyExpW (__g, (Whnf.expandDef us1), us2)
    let rec unifySpine =
      function
      | (__g, (Nil, _), (Nil, _)) -> ()
      | (__g, (SClo (S1, s1'), s1), __Ss) ->
          unifySpine (__g, (S1, (comp (s1', s1))), __Ss)
      | (__g, __Ss, (SClo (S2, s2'), s2)) ->
          unifySpine (__g, __Ss, (S2, (comp (s2', s2))))
      | (__g, (App (__U1, S1), s1), (App (__U2, S2), s2)) ->
          (unifyExp (__g, (__U1, s1), (__U2, s2));
           unifySpine (__g, (S1, s1), (S2, s2)))
    let rec unifyDec (__g, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
      unifyExp (__g, (V1, s1), (V2, s2))
    let rec unifySub =
      function
      | (__g, Shift n1, Shift n2) -> ()
      | (__g, Shift n, (Dot _ as s2)) ->
          unifySub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (__g, (Dot _ as s1), Shift m) ->
          unifySub (__g, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (__g, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 <> n2
                then raise (Error "Some variables mismatch")
                else ()
            | (Exp (__U1), Exp (__U2)) -> unifyExp (__g, (__U1, id), (__U2, id))
            | (Exp (__U1), Idx n2) ->
                unifyExp (__g, (__U1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (__U2)) ->
                unifyExp (__g, ((Root ((BVar n1), Nil)), id), (__U2, id)));
           unifySub (__g, s1, s2))
    let rec unifyBlock =
      function
      | (__g, LVar (ref (Some (B1)), s, _), B2) ->
          unifyBlock (__g, (blockSub (B1, s)), B2)
      | (__g, B1, LVar (ref (Some (B2)), s, _)) ->
          unifyBlock (__g, B1, (blockSub (B2, s)))
      | (__g, B1, B2) -> unifyBlockW (__g, B1, B2)
    let rec unifyBlockW =
      function
      | (__g, LVar (r1, (Shift k1 as s1), (l1, t1)), LVar
         (r2, (Shift k2 as s2), (l2, t2))) ->
          if l1 <> l2
          then raise (Unify "Label clash")
          else
            if r1 = r2
            then ()
            else
              (unifySub (__g, (comp (t1, s1)), (comp (t2, s2)));
               if k1 < k2
               then
                 instantiateLVar
                   (r1, (LVar (r2, (Shift (k2 - k1)), (l2, t2))))
               else
                 instantiateLVar
                   (r2, (LVar (r1, (Shift (k1 - k2)), (l1, t1)))))
      | (__g, LVar (r1, s1, (l1, t1)), B2) ->
          instantiateLVar (r1, (blockSub (B2, (Whnf.invert s1))))
      | (__g, B1, LVar (r2, s2, (l2, t2))) ->
          instantiateLVar (r2, (blockSub (B1, (Whnf.invert s2))))
      | (__g, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Unify "Block index clash") else ()
    let rec unify1W (__g, us1, us2) =
      unifyExpW (__g, us1, us2); awakeCnstr (nextCnstr ())
    let rec unify1 (__g, us1, us2) =
      unifyExp (__g, us1, us2); awakeCnstr (nextCnstr ())
    let rec awakeCnstr =
      function
      | None -> ()
      | Some (ref (Solved)) -> awakeCnstr (nextCnstr ())
      | Some (ref (Eqn (__g, __U1, __U2)) as cnstr) ->
          (solveConstraint cnstr; unify1 (__g, (__U1, id), (__U2, id)))
      | Some (ref (FgnCnstr csfc)) ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Unify "Foreign constraint violated")
    let rec unifyW (__g, us1, us2) =
      resetAwakenCnstrs (); unify1W (__g, us1, us2)
    let rec unify (__g, us1, us2) = resetAwakenCnstrs (); unify1 (__g, us1, us2)
    (* ? *)
    (* Associate a constraint to an expression *)
    (* delayExpW ((__u, s), cnstr) = ()

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v    (__u,s)  in whnf
       then
       the constraint cnstr is added to all the rigid EVar occurrences in __u[s]
    *)
    (* s = id *)
    (* no other cases by invariant *)
    (* delayExp ((__u, s), cnstr) = ()
       as in delayExpCW, except that the argument may not be in whnf
    *)
    (* delayHead (H, s, rOccur) = ()

       Invariant:
       If   __g' |- H : __v
       and  __g' |- s : __g         s is a pattern substitution
       then
       the constraint cnstr is added to a total of n rigid EVar occurrences in H[s]
    *)
    (* delaySpine ((S, s), cnstr) = ()

       Invariant:
       If   __g' |- s : __g    __g |- S : __v > W
       then      __g  |- S' : __v' > W'
       the constraint cnstr is added to all the rigid EVar occurrences in S[s]
    *)
    (* delayDec see delayExp *)
    (* Instantiating EVars  *)
    (* Instantiating LVars  *)
    (* local *)
    (* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)

       Invariant:
       If   __g |- s1 : __g'    s1 patsub
       and  __g |- s2 : __g'    s2 patsub
       then __g |- s' : __g'' for some __g''
       and  s' patsub
    *)
    (* both substitutions are the same number of shifts by invariant *)
    (* all other cases impossible for pattern substitutions *)
    (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    __g |- s : G1        s patsub *)
    (* ss strsub *)
    (* w' weaksub *)
    (* no other cases, ss is strsub *)
    (* invert (__g, (__u, s), ss, rOccur) = __u[s][ss]

       __g |- s : __g'   __g' |- __u : __v  (__g |- __u[s] : __v[s])
       __g'' |- ss : __g

       Effect: raises NotInvertible if __u[s][ss] does not exist
               or rOccurs occurs in __u[s]
               does NOT prune EVars in __u[s] according to ss; fails instead
    *)
    (* = id *)
    (* s not patsub *)
    (* invertExp may raise NotInvertible *)
    (* other cases impossible since (__u,s1) whnf *)
    (* blockSub (B, ss) should always be defined *)
    (* Fri Dec 28 10:03:12 2001 -fp !!! *)
    (* claim: LVar does not need to be pruned since . |- t : Gsome *)
    (* so we perform only the occurs-check here as for FVars *)
    (* Sat Dec  8 13:39:41 2001 -fp !!! *)
    (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
    (* Changed from Null to __g Sat Dec  7 21:58:00 2002 -fp *)
    (* __v does not to be pruned, since . |- __v : type and s' = ^k *)
    (* perform occurs-check for r only *)
    (* why __g here? -fp !!! *)
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    (* must be defined *)
    (* below my raise NotInvertible *)
    (* pruneSub (__g, Dot (Undef, s), ss, rOccur) is impossible *)
    (* By invariant, all EVars x[s] are such that s is defined everywhere *)
    (* Pruning establishes and maintains this invariant *)
    (* invertCtx does not appear to be necessary *)
    (*
    and invertCtx (Shift n, Null, rOccur) = Null
      | invertCtx (Dot (Idx k, t), Decl (__g, __d), rOccur) =
        let
          val t' = comp (t, invShift)
          val __d' = invertDec (__g, (__d, id), t', rOccur)
        in
          Decl (invertCtx (t', __g, rOccur), __d')
        end
      | invertCtx (Dot (Undef, t), Decl (__g, d), rOccur) =
          invertCtx (t, __g, rOccur)
      | invertCtx (Shift n, __g, rOccur) =
          invertCtx (Dot (Idx (n+1), Shift (n+1)), __g, rOccur)
    *)
    (* prune (__g, (__u, s), ss, rOccur) = __u[s][ss]

       !!! looks wrong to me -kw
       __g |- __u : __v    __g' |- s : __g  (__g' |- __u[s] : __v[s])
       __g'' |- ss : __g'
       !!! i would say
       __g |- s : __g'   __g' |- __u : __v  (__g  |- __u[s] : __v[s])
       __g'' |- ss : __g

       Effect: prunes EVars in __u[s] according to ss
               raises Unify if __u[s][ss] does not exist, or rOccur occurs in __u[s]
    *)
    (* = id *)
    (* val __v' = EClo (__v, wi) *)
    (* val GY = Whnf.strengthen (wi, GX) *)
    (* shortcut on GY possible by invariant on GX and __v[s]? -fp *)
    (* could optimize by checking for identity subst *)
    (* s not patsub *)
    (* val GY = Whnf.strengthen (ss, __g) *)
    (* shortcuts possible by invariants on __g? *)
    (* prune or invert??? *)
    (* val __v' = EClo (__v, comp (s, ss)) *)
    (* prune or invert??? *)
    (* this case should never happen! *)
    (* other cases impossible since (__u,s1) whnf *)
    (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
    (* blockSub (B, ss) should always be defined *)
    (* Fri Dec 28 10:03:12 2001 -fp !!! *)
    (* claim: LVar does not need to be pruned since . |- t : Gsome *)
    (* so we perform only the occurs-check here as for FVars *)
    (* Sat Dec  8 13:39:41 2001 -fp !!! *)
    (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
    (* Changed from Null to __g Sat Dec  7 21:58:00 2002 -fp *)
    (* __v does not to be pruned, since . |- __v : type and s' = ^k *)
    (* perform occurs-check for r only *)
    (* why __g here? -fp !!! *)
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    (* must be defined *)
    (* below my raise Unify *)
    (* pruneSub (__g, Dot (Undef, s), ss, rOccur) is impossible *)
    (* By invariant, all EVars x[s] are such that s is defined everywhere *)
    (* Pruning establishes and maintains this invariant *)
    (* unifyExpW (__g, (__U1, s1), (__U2, s2)) = ()

       Invariant:
       If   __g |- s1 : G1   G1 |- __U1 : V1    (__U1,s1) in whnf
       and  __g |- s2 : G2   G2 |- __U2 : V2    (__U2,s2) in whnf
       and  __g |- V1 [s1] = V2 [s2]  : __l    (for some level __l)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, __U1, s2, __U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. __g |- __U1 [s1] <I> == __U2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
    (* L1 = L2 = type, by invariant *)
    (* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
    (* s1 = s2 = id by whnf *)
    (* order of calls critical to establish unifySpine invariant *)
    (* because of strict *)
    (*  unifyExpW (__g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
    (* four new cases for defined constants *)
    (* conservative *)
    (* conservative *)
    (* due to strictness! *)
    (* due to strictness! *)
    (* next two cases for def/fgn, fgn/def *)
    (* we require unique string representation of external constants *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* ETA: can't occur if eta expanded *)
    (* for rhs:  (__U2[s2])[^] 1 = __U2 [s2 o ^] 1 = __U2 [^ o (1. s2 o ^)] 1
                        = (__U2 [^] 1) [1.s2 o ^] *)
    (* Cannot occur if expressions are eta expanded *)
    (* same reasoning holds as above *)
    (* postpone, if s1 or s2 are not patsub *)
    (* compute ss' directly? *)
    (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
    (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
    (* x[s] = x[s] *)
    (* invertExp ((V1, id), s', ref None) *)
    (* instantiateEVar (r1, EClo (__U2, comp(s2, ss1)), !cnstrs1) *)
    (* invertExpW (us2, s1, ref None) *)
    (* instantiateEVar (r2, EClo (__U1, comp(s1, ss2)), !cnstr2) *)
    (* invertExpW (us1, s2, ref None) *)
    (* instantiateEVar (r, EClo (__U2, comp(s2, ss)), !cnstrs) *)
    (* invertExpW (us2, s, r) *)
    (* instantiateEVar (r, EClo (__U1, comp(s1, ss)), !cnstrs) *)
    (* invertExpW (us1, s, r) *)
    (* covers most remaining cases *)
    (* the cases for EClo or Redex should not occur because of whnf invariant *)
    (* unifyExp (__g, (__U1, s1), (__U2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf
    *)
    (*  unifyExpW (__g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
    (* conservative *)
    (* unifySpine (__g, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   __g |- s1 : G1   G1 |- S1 : V1 > W1
       and  __g |- s2 : G2   G2 |- S2 : V2 > W2
       and  __g |- V1 [s1] = V2 [s2]  : __l    (for some level __l)
       and  __g |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. __g |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
    (* Nil/App or App/Nil cannot occur by typing invariants *)
    (* unifySub (__g, s1, s2) = ()

       Invariant:
       If   __g |- s1 : __g'
       and  __g |- s2 : __g'
       then unifySub (__g, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of Some variables
    *)
    (* conjecture: __g == Null at all times *)
    (* Thu Dec  6 21:01:09 2001 -fp *)
    (* by invariant *)
    (*         | (Undef, Undef) =>
           | _ => false *)
    (* not possible because of invariant? -cs *)
    (* substitutions s1 and s2 were redundant here --- removed *)
    (* Sat Dec  8 11:47:12 2001 -fp !!! *)
    (* Sat Dec  7 22:04:31 2002 -fp *)
    (* was: unifySub (__g, t1, t2)  Jul 22 2010 *)
    (* -- ABP *)
    (* -- ABP *)
    (*      | unifyBlockW (__g, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := Some (Bidx (i2 -k1)) ; ())  -- ABP *)
    (* -- ABP *)
    (* How can the next case arise? *)
    (* Sat Dec  8 11:49:16 2001 -fp !!! *)
    (*
      | unifyBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | unifyBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
    type nonrec unifTrail = unifTrail
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
    let rec invertible (__g, __Us, ss, rOccur) =
      try invertExp (__g, __Us, ss, rOccur); true__
      with | NotInvertible -> false__
    let invertSub = invertSub
    let rec unifiable (__g, us1, us2) =
      try unify (__g, us1, us2); true__ with | Unify msg -> false__
    let rec unifiable' (__g, us1, us2) =
      try unify (__g, us1, us2); None with | Unify msg -> Some msg
  end ;;
