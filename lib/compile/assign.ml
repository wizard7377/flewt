
module type ASSIGN  =
  sig
    val assignable :
      IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> IntSyn.__Cnstr list option
    val solveCnstr : IntSyn.__Cnstr list -> bool
    val unifiable : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> bool
    val instance : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> bool
    val firstConstArg : IntSyn.__Exp -> IntSyn.__Sub -> IntSyn.cid option
  end;;




module Assign(Assign:sig
                       module Whnf : WHNF
                       module Unify : UNIFY
                       module Print : PRINT
                     end) : ASSIGN =
  struct
    exception Assignment of string 
    open IntSyn
    let rec assignExpW __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (__G, (Uni (__L1), _), (Uni (__L2), _), cnstr) -> cnstr
      | (__G, ((Root (__H1, __S1), s1) as Us1),
         ((Root (__H2, __S2), s2) as Us2), cnstr) ->
          (((match (__H1, __H2) with
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then assignSpine (__G, (__S1, s1), (__S2, s2), cnstr)
                 else raise (Assignment "Constant clash")
             | (BVar k1, BVar k2) ->
                 if k1 = k2
                 then assignSpine (__G, (__S1, s1), (__S2, s2), cnstr)
                 else raise (Assignment "Bound variable clash")
             | (Skonst c1, Skonst c2) ->
                 if c1 = c2
                 then assignSpine (__G, (__S1, s1), (__S2, s2), cnstr)
                 else raise (Assignment "Skolem constant clash")
             | (Def d1, Def d2) ->
                 ((if d1 = d2
                   then assignSpine (__G, (__S1, s1), (__S2, s2), cnstr)
                   else
                     assignExp
                       (__G, (Whnf.expandDef __Us1), (Whnf.expandDef __Us2),
                         cnstr))
                 (* because of strict *))
             | (Def d1, _) ->
                 assignExp (__G, (Whnf.expandDef __Us1), __Us2, cnstr)
             | (_, Def d2) ->
                 assignExp (__G, __Us1, (Whnf.expandDef __Us2), cnstr)
             | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
                (cs2, ConDec (n2, _, _, _, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then cnstr
                 else raise (Assignment "Foreign Constant clash")
             | (FgnConst (cs1, ConDef (n1, _, _, __W1, _, _, _)), FgnConst
                (cs2, ConDef (n2, _, _, __V, __W2, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then cnstr
                 else assignExp (__G, (__W1, s1), (__W2, s2), cnstr)
             | (FgnConst (_, ConDef (_, _, _, __W1, _, _, _)), _) ->
                 assignExp (__G, (__W1, s1), __Us2, cnstr)
             | (_, FgnConst (_, ConDef (_, _, _, __W2, _, _, _))) ->
                 assignExp (__G, __Us1, (__W2, s2), cnstr)
             | _ -> raise (Assignment "Head mismatch ")))
          (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
          (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
          (* we require unique string representation of external constants *))
      | (__G, (Lam (__D1, __U1), s1), (Lam (__D2, __U2), s2), cnstr) ->
          assignExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              (__U2, (dot1 s2)), cnstr)
      | (__G, (__U1, s1), (Lam (__D2, __U2), s2), cnstr) ->
          assignExp
            ((Decl (__G, (decSub (__D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)), cnstr)
      | (__G, (Pi (((Dec (_, __V1) as D1), _), __U1), s1),
         (Pi (((Dec (_, __V2) as D2), _), __U2), s2), cnstr) ->
          let cnstr' = assignExp (__G, (__V1, s1), (__V2, s2), cnstr) in
          assignExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              (__U2, (dot1 s2)), cnstr')
      | (__G, ((__U, s1) as Us1), ((EVar (r2, _, _, _), s2) as Us2), cnstr)
          -> ((:=) r2 Some (EClo __Us1); cnstr)
      | (__G, ((__U, s1) as Us1), ((AVar r2, s2) as Us2), cnstr) ->
          ((:=) r2 Some (EClo __Us1); cnstr)
      | (__G, (Lam (__D1, __U1), s1), (__U2, s2), cnstr) ->
          assignExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)), cnstr)
      | (__G, __Us1, ((EClo (__U, s'), s) as Us2), cnstr) ->
          assignExp (__G, __Us1, (__U, (comp (s', s))), cnstr)
      | (__G, ((EVar (r, _, __V, Cnstr), s) as Us1), __Us2, cnstr) ->
          (Eqn (__G, (EClo __Us1), (EClo __Us2))) :: cnstr
      | (__G, ((EClo (__U, s'), s) as Us1), __Us2, cnstr) ->
          assignExp (__G, (__U, (comp (s', s))), __Us2, cnstr)
      | (__G, ((FgnExp (_, fe), _) as Us1), __Us2, cnstr) ->
          (Eqn (__G, (EClo __Us1), (EClo __Us2))) :: cnstr
      | (__G, __Us1, ((FgnExp (_, fe), _) as Us2), cnstr) ->
          (Eqn (__G, (EClo __Us1), (EClo __Us2))) :: cnstr(* by invariant Us2 cannot contain any FgnExp *)
      (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
      (* ETA: can't occur if eta expanded *)(* don't trail, because AVars never survive local scope *)
      (* s2 = id *)(* Tue Apr  2 10:23:19 2002 -bp -fp *)
      (* don't trail, because EVar has been created since most recent choice point *)
      (* s2 = id *)(* same reasoning holds as above *)
      (* Cannot occur if expressions are eta expanded *)
      (* D1[s1] = D2[s2]  by invariant *)(* L1 = L2 by invariant *)
    let rec assignSpine __8__ __9__ __10__ __11__ =
      match (__8__, __9__, __10__, __11__) with
      | (__G, (Nil, _), (Nil, _), cnstr) -> cnstr
      | (__G, (SClo (__S1, s1'), s1), __Ss, cnstr) ->
          assignSpine (__G, (__S1, (comp (s1', s1))), __Ss, cnstr)
      | (__G, __Ss, (SClo (__S2, s2'), s2), cnstr) ->
          assignSpine (__G, __Ss, (__S2, (comp (s2', s2))), cnstr)
      | (__G, (App (__U1, __S1), s1), (App (__U2, __S2), s2), cnstr) ->
          let cnstr' = assignExp (__G, (__U1, s1), (__U2, s2), cnstr) in
          assignSpine (__G, (__S1, s1), (__S2, s2), cnstr')
    let rec assignExp (__G) (__Us1) ((__U2, s2) as Us2) cnstr =
      assignExpW (__G, (Whnf.whnf __Us1), (Whnf.whnf __Us2), cnstr)
    let rec solveCnstr =
      function
      | nil -> true
      | (Eqn (__G, __U1, __U2))::Cnstr ->
          (Unify.unifiable (__G, (__U1, id), (__U2, id))) &&
            (solveCnstr Cnstr)
    let rec printSub =
      function
      | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
      | Dot (Idx n, s) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub s)
      | Dot (Exp (EVar (_, _, _, _)), s) ->
          (print "Exp (EVar _ ). "; printSub s)
      | Dot (Exp (AVar _), s) -> (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (AVar _, _)), s) ->
          (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (_, _)), s) -> (print "Exp (EClo _ ). "; printSub s)
      | Dot (Exp _, s) -> (print "Exp (_ ). "; printSub s)
      | Dot (Undef, s) -> (print "Undef . "; printSub s)
    let rec unifyW __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (__G, ((AVar ({ contents = None } as r) as Xs1), s), __Us2) ->
          (:=) r Some (EClo __Us2)
      | (__G, __Xs1, __Us2) -> Unify.unifyW (__G, __Xs1, __Us2)(* Xs1 should not contain any uninstantiated AVar anymore *)
      (* s = id *)
    let rec unify (__G) (__Xs1) (__Us2) =
      unifyW (__G, (Whnf.whnf __Xs1), (Whnf.whnf __Us2))
    let rec matchW __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (__G, ((AVar ({ contents = None } as r) as Xs1), s), __Us2) ->
          (:=) r Some (EClo __Us2)
      | (__G, __Xs1, __Us2) -> Match.matchW (__G, __Xs1, __Us2)(* Xs1 should not contain any uninstantiated AVar anymore *)
      (* s = id *)
    let rec match__ (__G) (__Xs1) (__Us2) =
      matchW (__G, (Whnf.whnf __Xs1), (Whnf.whnf __Us2))
    let solveCnstr = solveCnstr
    let rec unifiable (__G) (__Us1) (__Us2) =
      try unify (__G, __Us1, __Us2); true with | Unify msg -> false
    let rec instance (__G) (__Us1) (__Us2) =
      try match__ (__G, __Us1, __Us2); true with | Match msg -> false
    let rec assignable (__G) (__Us1) (Uts2) =
      try Some (assignExp (__G, __Us1, Uts2, []))
      with | Assignment msg -> None
    let rec firstConstArg (Root ((Const c as h), __S) as A) s =
      let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
      let rec constExp (__U) s = constExpW (Whnf.whnf (__U, s))
      and constExpW __0__ __1__ =
        match (__0__, __1__) with
        | (Lam (__D, __U), s) -> constExp (__U, s)
        | (Root ((Const cid as H), __S), s) -> Some cid
        | (_, _) -> None in
      let rec ithElem __2__ __3__ =
        match (__2__, __3__) with
        | (k, (App (__U, __S), s)) ->
            if k = i then constExp (__U, s) else ithElem ((k + 1), (__S, s))
        | (k, (IntSyn.Nil, s)) -> None in
      ((ithElem (0, (__S, s)))
        (* #implicit arguments to predicate *)(* other cases cannot occur during compilation *))
  end ;;
