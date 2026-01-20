
module type UNIFY  =
  sig
    type nonrec unifTrail
    val suspend : unit -> unifTrail
    val resume : unifTrail -> unit
    val reset : unit -> unit
    val mark : unit -> unit
    val unwind : unit -> unit
    val instantiateEVar :
      IntSyn.__Exp option ref -> IntSyn.__Exp -> IntSyn.cnstr list -> unit
    val instantiateLVar : IntSyn.__Block option ref -> IntSyn.__Block -> unit
    val resetAwakenCnstrs : unit -> unit
    val nextCnstr : unit -> IntSyn.cnstr option
    val addConstraint : IntSyn.cnstr list ref -> IntSyn.cnstr -> unit
    val solveConstraint : IntSyn.cnstr -> unit
    val delay : IntSyn.eclo -> IntSyn.cnstr -> unit
    val intersection : IntSyn.__Sub -> IntSyn.__Sub -> IntSyn.__Sub
    exception Unify of string 
    val unify : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> unit
    val unifyW : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> unit
    val unifyBlock : IntSyn.dctx -> IntSyn.__Block -> IntSyn.__Block -> unit
    val unifySub : IntSyn.dctx -> IntSyn.__Sub -> IntSyn.__Sub -> unit
    val invertible :
      IntSyn.dctx ->
        IntSyn.eclo -> IntSyn.__Sub -> IntSyn.__Exp option ref -> bool
    val invertSub :
      IntSyn.dctx ->
        IntSyn.__Sub ->
          IntSyn.__Sub -> IntSyn.__Exp option ref -> IntSyn.__Sub
    val unifiable : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> bool
    val unifiable' :
      IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> string option
  end;;




module Unify(Unify:sig module Whnf : WHNF module Trail : TRAIL end) : UNIFY =
  struct
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
      | Add ({ contents = Cnstrs } as cnstrs) ->
          BindAdd (cnstrs, (copyCnstr (!cnstrs)))
      | Solve (cnstr, Cnstr) -> FSolve (cnstr, Cnstr, (!cnstr))
    let rec resetCnstr =
      function
      | [] -> []
      | (BindCnstr (refC, Cnstr))::__L ->
          (refC := Cnstr; refC :: (resetCnstr __L))
    let rec reset =
      function
      | BindExp (refU, __U) -> (refU := __U; Instantiate refU)
      | BindBlock (refB, __B) -> (refB := __B; InstantiateBlock refB)
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
      | Add ({ contents = cnstr::cnstrL } as cnstrs) -> cnstrs := cnstrL
      | Solve (cnstr, Cnstr) -> cnstr := Cnstr
    let rec reset () = Trail.reset globalTrail
    let rec mark () = Trail.mark globalTrail
    let rec unwind () = Trail.unwind (globalTrail, undo)
    let rec addConstraint cnstrs cnstr =
      (cnstrs := cnstr) :: (!cnstrs); Trail.log (globalTrail, (Add cnstrs))
    let rec solveConstraint ({ contents = Cnstr } as cnstr) =
      cnstr := Solved; Trail.log (globalTrail, (Solve (cnstr, Cnstr)))
    let rec delayExpW __0__ __1__ =
      match (__0__, __1__) with
      | (((Uni (__L) as U), s1), _) -> ()
      | ((Pi ((__D, __P), __U), s), cnstr) ->
          (delayDec ((__D, s), cnstr); delayExp ((__U, (dot1 s)), cnstr))
      | ((Root (__H, __S), s), cnstr) ->
          (delayHead (__H, cnstr); delaySpine ((__S, s), cnstr))
      | ((Lam (__D, __U), s), cnstr) ->
          (delayDec ((__D, s), cnstr); delayExp ((__U, (dot1 s)), cnstr))
      | ((EVar (__G, r, __V, cnstrs), s), cnstr) ->
          addConstraint (cnstrs, cnstr)
      | ((FgnExp csfe, s), cnstr) ->
          FgnExpStd.App.apply csfe (fun (__U) -> delayExp ((__U, s), cnstr))
      (* s = id *)
    let rec delayExp (__Us) cnstr = delayExpW ((Whnf.whnf __Us), cnstr)
    let rec delayHead __2__ __3__ =
      match (__2__, __3__) with
      | (FVar (x, __V, s'), cnstr) -> delayExp ((__V, id), cnstr)
      | (__H, _) -> ()
    let rec delaySpine __4__ __5__ =
      match (__4__, __5__) with
      | ((Nil, s), cnstr) -> ()
      | ((App (__U, __S), s), cnstr) ->
          (delayExp ((__U, s), cnstr); delaySpine ((__S, s), cnstr))
      | ((SClo (__S, s'), s), cnstr) ->
          delaySpine ((__S, (comp (s', s))), cnstr)
    let rec delayDec (Dec (name, __V), s) cnstr = delayExp ((__V, s), cnstr)
    let awakenCnstrs = (ref nil : cnstr list ref)
    let rec resetAwakenCnstrs () = awakenCnstrs := nil
    let rec nextCnstr () =
      match !awakenCnstrs with
      | nil -> None
      | cnstr::cnstrL -> (awakenCnstrs := cnstrL; Some cnstr)
    let rec instantiateEVar refU (__V) cnstrL =
      (:=) refU Some __V;
      Trail.log (globalTrail, (Instantiate refU));
      (!) ((@) (awakenCnstrs := cnstrL)) awakenCnstrs
    let rec instantiateLVar refB (__B) =
      (:=) refB Some __B; Trail.log (globalTrail, (InstantiateBlock refB))
    let rec intersection __6__ __7__ =
      match (__6__, __7__) with
      | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
          if k1 = k2
          then dot1 (intersection (s1, s2))
          else comp ((intersection (s1, s2)), shift)
      | ((Dot _ as s1), Shift n2) ->
          intersection (s1, (Dot ((Idx (n2 + 1)), (Shift (n2 + 1)))))
      | (Shift n1, (Dot _ as s2)) ->
          intersection ((Dot ((Idx (n1 + 1)), (Shift (n1 + 1)))), s2)
      | (Shift _, Shift _) -> id
    let rec weakenSub __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (__G, Shift n, ss) ->
          if (<) n ctxLength __G
          then weakenSub (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (__G, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (__G, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (__G, s', ss)))
      | (__G, Dot (Undef, s'), ss) -> comp ((weakenSub (__G, s', ss)), shift)
      (* no other cases, ss is strsub *)
    let rec invertExp (__G) (__Us) ss rOccur =
      invertExpW (__G, (Whnf.whnf __Us), ss, rOccur)
    let rec invertExpW __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (__G, ((Uni _ as U), s), _, _) -> __U
      | (__G, (Pi ((__D, __P), __V), s), ss, rOccur) ->
          Pi
            (((invertDec (__G, (__D, s), ss, rOccur)), __P),
              (invertExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (Lam (__D, __V), s), ss, rOccur) ->
          Lam
            ((invertDec (__G, (__D, s), ss, rOccur)),
              (invertExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (((Root (__H, __S), s))(* = id *)), ss,
         rOccur) ->
          Root
            ((invertHead (__G, __H, ss, rOccur)),
              (invertSpine (__G, (__S, s), ss, rOccur)))
      | (__G, ((EVar (r, GX, __V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise NotInvertible
          else
            ((if Whnf.isPatSub s
              then
                (let w = weakenSub (__G, s, ss) in
                 if Whnf.isId w
                 then EClo (__X, (comp (s, ss)))
                 else raise NotInvertible)
              else EClo (__X, (invertSub (__G, s, ss, rOccur))))
            (* s not patsub *)(* invertExp may raise NotInvertible *))
      | (__G, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (fun (__U) -> invertExp (__G, (__U, s), ss, rOccur))
    let rec invertDec (__G) (Dec (name, __V), s) ss rOccur =
      Dec (name, (invertExp (__G, (__V, s), ss, rOccur)))
    let rec invertSpine __15__ __16__ __17__ __18__ =
      match (__15__, __16__, __17__, __18__) with
      | (__G, (Nil, s), ss, rOccur) -> Nil
      | (__G, (App (__U, __S), s), ss, rOccur) ->
          App
            ((invertExp (__G, (__U, s), ss, rOccur)),
              (invertSpine (__G, (__S, s), ss, rOccur)))
      | (__G, (SClo (__S, s'), s), ss, rOccur) ->
          invertSpine (__G, (__S, (comp (s', s))), ss, rOccur)
    let rec invertHead __19__ __20__ __21__ __22__ =
      match (__19__, __20__, __21__, __22__) with
      | (__G, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise NotInvertible
           | Idx k' -> BVar k')
      | (__G, (Const _ as H), ss, rOccur) -> __H
      | (__G, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (__B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__G, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (invertSub (__G, t, id, rOccur); __H)
      | (__G, (Skonst _ as H), ss, rOccur) -> __H
      | (__G, (Def _ as H), ss, rOccur) -> __H
      | (__G, FVar (x, __V, s'), ss, rOccur) ->
          (((invertExp (__G, (__V, id), id, rOccur);
             FVar (x, __V, (comp (s', ss)))))
          (* why G here? -fp !!! *))
      | (__G, (FgnConst _ as H), ss, rOccur) -> __H(* perform occurs-check for r only *)
      (* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* so we perform only the occurs-check here as for FVars *)
      (* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
    let rec invertSub __23__ __24__ __25__ __26__ =
      match (__23__, __24__, __25__, __26__) with
      | (__G, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __G
          then
            invertSub
              (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__G, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise NotInvertible
           | Ft -> Dot (Ft, (invertSub (__G, s', ss, rOccur))))
      | (__G, Dot (Exp (__U), s'), ss, rOccur) ->
          Dot
            ((Exp (invertExp (__G, (__U, id), ss, rOccur))),
              (invertSub (__G, s', ss, rOccur)))(* below my raise NotInvertible *)
      (* must be defined *)
    let rec pruneExp (__G) (__Us) ss rOccur =
      pruneExpW (__G, (Whnf.whnf __Us), ss, rOccur)
    let rec pruneExpW __27__ __28__ __29__ __30__ =
      match (__27__, __28__, __29__, __30__) with
      | (__G, ((Uni _ as U), s), _, _) -> __U
      | (__G, (Pi ((__D, __P), __V), s), ss, rOccur) ->
          Pi
            (((pruneDec (__G, (__D, s), ss, rOccur)), __P),
              (pruneExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (Lam (__D, __V), s), ss, rOccur) ->
          Lam
            ((pruneDec (__G, (__D, s), ss, rOccur)),
              (pruneExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (((Root (__H, __S), s))(* = id *)), ss,
         rOccur) ->
          Root
            ((pruneHead (__G, __H, ss, rOccur)),
              (pruneSpine (__G, (__S, s), ss, rOccur)))
      | (__G, ((EVar (r, GX, __V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise (Unify "Variable occurrence")
          else
            ((if Whnf.isPatSub s
              then
                (let w = weakenSub (__G, s, ss) in
                 if Whnf.isId w
                 then EClo (__X, (comp (s, ss)))
                 else
                   (let wi = Whnf.invert w in
                    let __V' = pruneExp (GX, (__V, id), wi, rOccur) in
                    let GY = pruneCtx (wi, GX, rOccur) in
                    let __Y = newEVar (GY, __V') in
                    let Yw = EClo (__Y, w) in
                    let _ = instantiateEVar (r, Yw, (!cnstrs)) in
                    ((EClo (Yw, (comp (s, ss))))
                      (* val V' = EClo (V, wi) *)(* val GY = Whnf.strengthen (wi, GX) *)
                      (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
                      (* could optimize by checking for identity subst *))))
              else
                (try EClo (__X, (invertSub (__G, s, ss, rOccur)))
                 with
                 | NotInvertible ->
                     let GY = pruneCtx (ss, __G, rOccur) in
                     let __V' = pruneExp (__G, (__V, s), ss, rOccur) in
                     let __Y = newEVar (GY, __V') in
                     let _ =
                       addConstraint
                         (cnstrs,
                           (ref
                              (Eqn
                                 (__G, (EClo (__X, s)),
                                   (EClo (__Y, (Whnf.invert ss))))))) in
                     ((__Y)
                       (* val GY = Whnf.strengthen (ss, G) *)(* shortcuts possible by invariants on G? *)
                       (* prune or invert??? *)(* val V' = EClo (V, comp (s, ss)) *)
                       (* prune or invert??? *))))
            (* s not patsub *))
      | (__G, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (fun (__U) -> pruneExp (__G, (__U, s), ss, rOccur))
      | (__G, ((AVar _ as X), s), ss, rOccur) ->
          raise (Unify "Left-over AVar")(* this case should never happen! *)
    let rec pruneDec __31__ __32__ __33__ __34__ =
      match (__31__, __32__, __33__, __34__) with
      | (__G, (Dec (name, __V), s), ss, rOccur) ->
          Dec (name, (pruneExp (__G, (__V, s), ss, rOccur)))
      | (__G, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine __35__ __36__ __37__ __38__ =
      match (__35__, __36__, __37__, __38__) with
      | (__G, (Nil, s), ss, rOccur) -> Nil
      | (__G, (App (__U, __S), s), ss, rOccur) ->
          App
            ((pruneExp (__G, (__U, s), ss, rOccur)),
              (pruneSpine (__G, (__S, s), ss, rOccur)))
      | (__G, (SClo (__S, s'), s), ss, rOccur) ->
          pruneSpine (__G, (__S, (comp (s', s))), ss, rOccur)
    let rec pruneHead __39__ __40__ __41__ __42__ =
      match (__39__, __40__, __41__, __42__) with
      | (__G, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Unify "Parameter dependency")
           | Idx k' -> BVar k')
      | (__G, (Const _ as H), ss, rOccur) -> __H
      | (__G, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (__B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__G, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (__G, t, id, rOccur); __H)
      | (__G, (Skonst _ as H), ss, rOccur) -> __H
      | (__G, (Def _ as H), ss, rOccur) -> __H
      | (__G, FVar (x, __V, s'), ss, rOccur) ->
          (((pruneExp (__G, (__V, id), id, rOccur);
             FVar (x, __V, (comp (s', ss)))))
          (* why G here? -fp !!! *))
      | (__G, (FgnConst _ as H), ss, rOccur) -> __H(* perform occurs-check for r only *)
      (* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* so we perform only the occurs-check here as for FVars *)
      (* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
    let rec pruneSub __43__ __44__ __45__ __46__ =
      match (__43__, __44__, __45__, __46__) with
      | (__G, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __G
          then
            pruneSub
              (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__G, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Unify "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (__G, s', ss, rOccur))))
      | (__G, Dot (Exp (__U), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (__G, (__U, id), ss, rOccur))),
              (pruneSub (__G, s', ss, rOccur)))(* below my raise Unify *)
      (* must be defined *)
    let rec pruneCtx __47__ __48__ __49__ =
      match (__47__, __48__, __49__) with
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (__G, __D), rOccur) ->
          let t' = comp (t, invShift) in
          let __D' = pruneDec (__G, (__D, id), t', rOccur) in
          Decl ((pruneCtx (t', __G, rOccur)), __D')
      | (Dot (Undef, t), Decl (__G, d), rOccur) -> pruneCtx (t, __G, rOccur)
      | (Shift n, __G, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __G, rOccur)
    let rec unifyExpW __50__ __51__ __52__ =
      match (__50__, __51__, __52__) with
      | (__G, ((FgnExp csfe1, _) as Us1), __Us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (__G, (EClo __Us2)) with
           | Succeed residualL ->
               let rec execResidual =
                 function
                 | Assign (__G, EVar (r, _, _, cnstrs), __W, ss) ->
                     let __W' = pruneExp (__G, (__W, id), ss, r) in
                     instantiateEVar (r, __W', (!cnstrs))
                 | Delay (__U, cnstr) -> delayExp ((__U, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (__G, __Us1, ((FgnExp csfe2, _) as Us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (__G, (EClo __Us1)) with
           | Succeed opL ->
               let rec execOp =
                 function
                 | Assign (__G, EVar (r, _, _, cnstrs), __W, ss) ->
                     let __W' = pruneExp (__G, (__W, id), ss, r) in
                     instantiateEVar (r, __W', (!cnstrs))
                 | Delay (__U, cnstr) -> delayExp ((__U, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Unify "Foreign Expression Mismatch"))
      | (__G, (Uni (__L1), _), (Uni (__L2), _)) -> ()
      | (__G, ((Root (__H1, __S1), s1) as Us1),
         ((Root (__H2, __S2), s2) as Us2)) ->
          (((match (__H1, __H2) with
             | (BVar k1, BVar k2) ->
                 if k1 = k2
                 then unifySpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Unify "Bound variable clash")
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then unifySpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Unify "Constant clash")
             | (Proj (b1, i1), Proj (b2, i2)) ->
                 if i1 = i2
                 then
                   (unifyBlock (__G, b1, b2);
                    unifySpine (__G, (__S1, s1), (__S2, s2)))
                 else raise (Unify "Global parameter clash")
             | (Skonst c1, Skonst c2) ->
                 if c1 = c2
                 then unifySpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Unify "Skolem constant clash")
             | (FVar (n1, _, _), FVar (n2, _, _)) ->
                 if n1 = n2
                 then unifySpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Unify "Free variable clash")
             | (Def d1, Def d2) ->
                 ((if d1 = d2
                   then unifySpine (__G, (__S1, s1), (__S2, s2))
                   else unifyDefDefW (__G, __Us1, __Us2))
                 (* because of strict *)(*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *))
             | (Def d1, Const c2) ->
                 (((match defAncestor d1 with
                    | Anc (_, _, None) ->
                        unifyExpW (__G, (Whnf.expandDef __Us1), __Us2)
                    | Anc (_, _, Some c1) ->
                        if c1 = c2
                        then unifyExpW (__G, (Whnf.expandDef __Us1), __Us2)
                        else raise (Unify "Constant clash")))
                 (* conservative *))
             | (Const c1, Def d2) ->
                 (((match defAncestor d2 with
                    | Anc (_, _, None) ->
                        unifyExpW (__G, __Us1, (Whnf.expandDef __Us2))
                    | Anc (_, _, Some c2) ->
                        if c1 = c2
                        then unifyExpW (__G, __Us1, (Whnf.expandDef __Us2))
                        else raise (Unify "Constant clash")))
                 (* conservative *))
             | (Def d1, BVar k2) -> raise (Unify "Head mismatch")
             | (BVar k1, Def d2) -> raise (Unify "Head mismatch")
             | (Def d1, _) -> unifyExpW (__G, (Whnf.expandDef __Us1), __Us2)
             | (_, Def d2) -> unifyExpW (__G, __Us1, (Whnf.expandDef __Us2))
             | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
                (cs2, ConDec (n2, _, _, _, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then ()
                 else raise (Unify "Foreign Constant clash")
             | (FgnConst (cs1, ConDef (n1, _, _, __W1, _, _, _)), FgnConst
                (cs2, ConDef (n2, _, _, __V, __W2, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then ()
                 else unifyExp (__G, (__W1, s1), (__W2, s2))
             | (FgnConst (_, ConDef (_, _, _, __W1, _, _, _)), _) ->
                 unifyExp (__G, (__W1, s1), __Us2)
             | (_, FgnConst (_, ConDef (_, _, _, __W2, _, _, _))) ->
                 unifyExp (__G, __Us1, (__W2, s2))
             | _ -> raise (Unify "Head mismatch")))
          (* four new cases for defined constants *)
          (* due to strictness! *)(* due to strictness! *)
          (* next two cases for def/fgn, fgn/def *)(* we require unique string representation of external constants *))
      | (__G, (Pi ((__D1, _), __U1), s1), (Pi ((__D2, _), __U2), s2)) ->
          (unifyDec (__G, (__D1, s1), (__D2, s2));
           unifyExp
             ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
               (__U2, (dot1 s2))))
      | (__G, ((Pi (_, _), _) as Us1), ((Root (Def _, _), _) as Us2)) ->
          unifyExpW (__G, __Us1, (Whnf.expandDef __Us2))
      | (__G, ((Root (Def _, _), _) as Us1), ((Pi (_, _), _) as Us2)) ->
          unifyExpW (__G, (Whnf.expandDef __Us1), __Us2)
      | (__G, (Lam (__D1, __U1), s1), (Lam (__D2, __U2), s2)) ->
          unifyExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              (__U2, (dot1 s2)))
      | (__G, (Lam (__D1, __U1), s1), (__U2, s2)) ->
          unifyExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (__G, (__U1, s1), (Lam (__D2, __U2), s2)) ->
          unifyExp
            ((Decl (__G, (decSub (__D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)))
      | (__G, (((EVar (r1, __G1, __V1, cnstrs1) as U1), s1) as Us1),
         (((EVar (r2, __G2, __V2, cnstrs2) as U2), s2) as Us2)) ->
          if r1 = r2
          then
            (if Whnf.isPatSub s1
             then
               (if Whnf.isPatSub s2
                then
                  let s' = intersection (s1, s2) in
                  (((if Whnf.isId s'
                     then ()
                     else
                       (let ss' = Whnf.invert s' in
                        let V1' = EClo (__V1, ss') in
                        let G1' = Whnf.strengthen (ss', __G1) in
                        ((instantiateEVar
                            (r1, (EClo ((newEVar (G1', V1')), s')),
                              (!cnstrs1)))
                          (* invertExp ((V1, id), s', ref None) *)))))
                    (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
                    (* X[s] = X[s] *)(* compute ss' directly? *)
                    (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *))
                else
                  addConstraint
                    (cnstrs2, (ref (Eqn (__G, (EClo __Us2), (EClo __Us1))))))
             else
               addConstraint
                 (cnstrs1, (ref (Eqn (__G, (EClo __Us1), (EClo __Us2))))))
          else
            if Whnf.isPatSub s1
            then
              (let ss1 = Whnf.invert s1 in
               let U2' = pruneExp (__G, __Us2, ss1, r1) in
               ((instantiateEVar (r1, U2', (!cnstrs1)))
                 (* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
                 (* invertExpW (Us2, s1, ref None) *)))
            else
              if Whnf.isPatSub s2
              then
                (let ss2 = Whnf.invert s2 in
                 let U1' = pruneExp (__G, __Us1, ss2, r2) in
                 ((instantiateEVar (r2, U1', (!cnstrs2)))
                   (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
                   (* invertExpW (Us1, s2, ref None) *)))
              else
                (let cnstr = ref (Eqn (__G, (EClo __Us1), (EClo __Us2))) in
                 addConstraint (cnstrs1, cnstr))
      | (__G, ((EVar (r, GX, __V, cnstrs), s) as Us1), ((__U2, s2) as Us2))
          ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let U2' = pruneExp (__G, __Us2, ss, r) in
            ((instantiateEVar (r, U2', (!cnstrs)))
              (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
              (* invertExpW (Us2, s, r) *))
          else
            addConstraint
              (cnstrs, (ref (Eqn (__G, (EClo __Us1), (EClo __Us2)))))
      | (__G, ((__U1, s1) as Us1), ((EVar (r, GX, __V, cnstrs), s) as Us2))
          ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let U1' = pruneExp (__G, __Us1, ss, r) in
            ((instantiateEVar (r, U1', (!cnstrs)))
              (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
              (* invertExpW (Us1, s, r) *))
          else
            addConstraint
              (cnstrs, (ref (Eqn (__G, (EClo __Us1), (EClo __Us2)))))
      | (__G, __Us1, __Us2) -> raise (Unify "Expression clash")(* postpone, if s1 or s2 are not patsub *)
      (* same reasoning holds as above *)(* Cannot occur if expressions are eta expanded *)
      (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
      (* ETA: can't occur if eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
      (* order of calls critical to establish unifySpine invariant *)
      (* s1 = s2 = id by whnf *)(* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
      (* L1 = L2 = type, by invariant *)
    let rec unifyExp (__G) ((__E1, s1) as Us1) ((__E2, s2) as Us2) =
      unifyExpW (__G, (Whnf.whnf __Us1), (Whnf.whnf __Us2))
    let rec unifyDefDefW (__G) ((Root (Def d1, __S1), s1) as Us1)
      ((Root (Def d2, __S2), s2) as Us2) =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (Some c1, Some c2) ->
            if c1 <> c2
            then raise (Unify "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      ((match Int.compare (h1, h2) with
        | EQUAL ->
            unifyExpW (__G, (Whnf.expandDef __Us1), (Whnf.expandDef __Us2))
        | LESS -> unifyExpW (__G, __Us1, (Whnf.expandDef __Us2))
        | GREATER -> unifyExpW (__G, (Whnf.expandDef __Us1), __Us2))
        (* conservative *))(*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
    let rec unifySpine __53__ __54__ __55__ =
      match (__53__, __54__, __55__) with
      | (__G, (Nil, _), (Nil, _)) -> ()
      | (__G, (SClo (__S1, s1'), s1), __Ss) ->
          unifySpine (__G, (__S1, (comp (s1', s1))), __Ss)
      | (__G, __Ss, (SClo (__S2, s2'), s2)) ->
          unifySpine (__G, __Ss, (__S2, (comp (s2', s2))))
      | (__G, (App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (unifyExp (__G, (__U1, s1), (__U2, s2));
           unifySpine (__G, (__S1, s1), (__S2, s2)))
    let rec unifyDec (__G) (Dec (_, __V1), s1) (Dec (_, __V2), s2) =
      unifyExp (__G, (__V1, s1), (__V2, s2))
    let rec unifySub __56__ __57__ __58__ =
      match (__56__, __57__, __58__) with
      | (__G, Shift n1, Shift n2) -> ()
      | (__G, Shift n, (Dot _ as s2)) ->
          unifySub (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (__G, (Dot _ as s1), Shift m) ->
          unifySub (__G, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (__G, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((((match (Ft1, Ft2) with
              | (Idx n1, Idx n2) ->
                  if n1 <> n2
                  then raise (Error "Some variables mismatch")
                  else ()
              | (Exp (__U1), Exp (__U2)) ->
                  unifyExp (__G, (__U1, id), (__U2, id))
              | (Exp (__U1), Idx n2) ->
                  unifyExp (__G, (__U1, id), ((Root ((BVar n2), Nil)), id))
              | (Idx n1, Exp (__U2)) ->
                  unifyExp (__G, ((Root ((BVar n1), Nil)), id), (__U2, id)));
             unifySub (__G, s1, s2)))
          (*         | (Undef, Undef) =>
           | _ => false *)
          (* not possible because of invariant? -cs *))
      (* by invariant *)
    let rec unifyBlock __59__ __60__ __61__ =
      match (__59__, __60__, __61__) with
      | (__G, LVar ({ contents = Some (__B1) }, s, _), __B2) ->
          unifyBlock (__G, (blockSub (__B1, s)), __B2)
      | (__G, __B1, LVar ({ contents = Some (__B2) }, s, _)) ->
          unifyBlock (__G, __B1, (blockSub (__B2, s)))
      | (__G, __B1, __B2) -> unifyBlockW (__G, __B1, __B2)
    let rec unifyBlockW __62__ __63__ __64__ =
      match (__62__, __63__, __64__) with
      | (__G, LVar (r1, (Shift k1 as s1), (l1, t1)), LVar
         (r2, (Shift k2 as s2), (l2, t2))) ->
          if l1 <> l2
          then raise (Unify "Label clash")
          else
            if r1 = r2
            then ()
            else
              (((unifySub (__G, (comp (t1, s1)), (comp (t2, s2)));
                 if k1 < k2
                 then
                   instantiateLVar
                     (r1, (LVar (r2, (Shift (k2 - k1)), (l2, t2))))
                 else
                   instantiateLVar
                     (r2, (LVar (r1, (Shift (k1 - k2)), (l1, t1))))))
              (* Sat Dec  7 22:04:31 2002 -fp *)(* was: unifySub (G, t1, t2)  Jul 22 2010 *))
      | (__G, LVar (r1, s1, (l1, t1)), __B2) ->
          instantiateLVar (r1, (blockSub (__B2, (Whnf.invert s1))))
      | (__G, __B1, LVar (r2, s2, (l2, t2))) ->
          instantiateLVar (r2, (blockSub (__B1, (Whnf.invert s2))))
      | (__G, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Unify "Block index clash") else ()(* Sat Dec  8 11:49:16 2001 -fp !!! *)
      (* How can the next case arise? *)(* -- ABP *)
      (*      | unifyBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := Some (Bidx (i2 -k1)) ; ())  -- ABP *)
      (* -- ABP *)(* -- ABP *)
    let rec unify1W (__G) (__Us1) (__Us2) =
      unifyExpW (__G, __Us1, __Us2); awakeCnstr (nextCnstr ())
    let rec unify1 (__G) (__Us1) (__Us2) =
      unifyExp (__G, __Us1, __Us2); awakeCnstr (nextCnstr ())
    let rec awakeCnstr =
      function
      | None -> ()
      | Some { contents = Solved } -> awakeCnstr (nextCnstr ())
      | Some ({ contents = Eqn (__G, __U1, __U2) } as cnstr) ->
          (solveConstraint cnstr; unify1 (__G, (__U1, id), (__U2, id)))
      | Some { contents = FgnCnstr csfc } ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Unify "Foreign constraint violated")
    let rec unifyW (__G) (__Us1) (__Us2) =
      resetAwakenCnstrs (); unify1W (__G, __Us1, __Us2)
    let rec unify (__G) (__Us1) (__Us2) =
      resetAwakenCnstrs (); unify1 (__G, __Us1, __Us2)
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
    let rec invertible (__G) (__Us) ss rOccur =
      try invertExp (__G, __Us, ss, rOccur); true
      with | NotInvertible -> false
    let invertSub = invertSub
    let rec unifiable (__G) (__Us1) (__Us2) =
      try unify (__G, __Us1, __Us2); true with | Unify msg -> false
    let rec unifiable' (__G) (__Us1) (__Us2) =
      try unify (__G, __Us1, __Us2); None with | Unify msg -> Some msg
  end ;;
