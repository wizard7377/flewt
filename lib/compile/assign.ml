
(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)
module type ASSIGN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* assignable (__Us,ps) assigns the term __u[s] to the 
     linear higher-order pattern p[s]; if successfull it
     returns a list of residual equations that have been postponed *)
    (* EVars and AVars in ps are instantiated as an effect *)
    val assignable :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> IntSyn.__Cnstr list option
    (* solveCnstr solves dynamically residuated equations *)
    val solveCnstr : IntSyn.__Cnstr list -> bool
    (* unifiable solves statically residuated equations *)
    val unifiable : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    (* instance solves statically residuated equations *)
    val instance : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    val firstConstArg : (IntSyn.__Exp * IntSyn.__Sub) -> IntSyn.cid option
  end;;




(* Assignment *)
(* Author: Brigitte Pientka *)
module Assign(Assign:sig
                       (*! structure IntSyn' : INTSYN !*)
                       module Whnf : WHNF
                       module Unify : UNIFY
                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                       (*! sharing Unify.IntSyn = IntSyn' !*)
                       module Print : PRINT
                     end) : ASSIGN =
  struct
    (*! sharing Print.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Assignment of string 
    open IntSyn
    let rec assignExpW =
      function
      | (__g, (Uni (L1), _), (Uni (L2), _), cnstr) -> cnstr
      | (__g, ((Root (H1, S1), s1) as us1), ((Root (H2, S2), s2) as us2),
         cnstr) ->
          (match (H1, H2) with
           | (Const c1, Const c2) ->
               if c1 = c2
               then assignSpine (__g, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Constant clash")
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then assignSpine (__g, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Bound variable clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then assignSpine (__g, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Skolem constant clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then assignSpine (__g, (S1, s1), (S2, s2), cnstr)
               else
                 assignExp
                   (__g, (Whnf.expandDef us1), (Whnf.expandDef us2), cnstr)
           | (Def d1, _) -> assignExp (__g, (Whnf.expandDef us1), us2, cnstr)
           | (_, Def d2) -> assignExp (__g, us1, (Whnf.expandDef us2), cnstr)
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else raise (Assignment "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, __v, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else assignExp (__g, (W1, s1), (W2, s2), cnstr)
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               assignExp (__g, (W1, s1), us2, cnstr)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               assignExp (__g, us1, (W2, s2), cnstr)
           | _ -> raise (Assignment "Head mismatch "))
      | (__g, (Lam (D1, __U1), s1), (Lam (D2, __U2), s2), cnstr) ->
          assignExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)), (__U2, (dot1 s2)),
              cnstr)
      | (__g, (__U1, s1), (Lam (D2, __U2), s2), cnstr) ->
          assignExp
            ((Decl (__g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)), cnstr)
      | (__g, (Pi (((Dec (_, V1) as D1), _), __U1), s1),
         (Pi (((Dec (_, V2) as D2), _), __U2), s2), cnstr) ->
          let cnstr' = assignExp (__g, (V1, s1), (V2, s2), cnstr) in
          assignExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)), (__U2, (dot1 s2)),
              cnstr')
      | (__g, ((__u, s1) as us1), ((EVar (r2, _, _, _), s2) as us2), cnstr) ->
          ((:=) r2 Some (EClo us1); cnstr)
      | (__g, ((__u, s1) as us1), ((AVar r2, s2) as us2), cnstr) ->
          ((:=) r2 Some (EClo us1); cnstr)
      | (__g, (Lam (D1, __U1), s1), (__U2, s2), cnstr) ->
          assignExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)), cnstr)
      | (__g, us1, ((EClo (__u, s'), s) as us2), cnstr) ->
          assignExp (__g, us1, (__u, (comp (s', s))), cnstr)
      | (__g, ((EVar (r, _, __v, Cnstr), s) as us1), us2, cnstr) ->
          (Eqn (__g, (EClo us1), (EClo us2))) :: cnstr
      | (__g, ((EClo (__u, s'), s) as us1), us2, cnstr) ->
          assignExp (__g, (__u, (comp (s', s))), us2, cnstr)
      | (__g, ((FgnExp (_, fe), _) as us1), us2, cnstr) ->
          (Eqn (__g, (EClo us1), (EClo us2))) :: cnstr
      | (__g, us1, ((FgnExp (_, fe), _) as us2), cnstr) ->
          (Eqn (__g, (EClo us1), (EClo us2))) :: cnstr
    let rec assignSpine =
      function
      | (__g, (Nil, _), (Nil, _), cnstr) -> cnstr
      | (__g, (SClo (S1, s1'), s1), __Ss, cnstr) ->
          assignSpine (__g, (S1, (comp (s1', s1))), __Ss, cnstr)
      | (__g, __Ss, (SClo (S2, s2'), s2), cnstr) ->
          assignSpine (__g, __Ss, (S2, (comp (s2', s2))), cnstr)
      | (__g, (App (__U1, S1), s1), (App (__U2, S2), s2), cnstr) ->
          let cnstr' = assignExp (__g, (__U1, s1), (__U2, s2), cnstr) in
          assignSpine (__g, (S1, s1), (S2, s2), cnstr')
    let rec assignExp (__g, us1, ((__U2, s2) as us2), cnstr) =
      assignExpW (__g, (Whnf.whnf us1), (Whnf.whnf us2), cnstr)
    let rec solveCnstr =
      function
      | nil -> true__
      | (Eqn (__g, __U1, __U2))::Cnstr ->
          (Unify.unifiable (__g, (__U1, id), (__U2, id))) && (solveCnstr Cnstr)
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
    let rec unifyW =
      function
      | (__g, ((AVar (ref (None) as r) as Xs1), s), us2) ->
          (:=) r Some (EClo us2)
      | (__g, Xs1, us2) -> Unify.unifyW (__g, Xs1, us2)
    let rec unify (__g, Xs1, us2) =
      unifyW (__g, (Whnf.whnf Xs1), (Whnf.whnf us2))
    let rec matchW =
      function
      | (__g, ((AVar (ref (None) as r) as Xs1), s), us2) ->
          (:=) r Some (EClo us2)
      | (__g, Xs1, us2) -> Match.matchW (__g, Xs1, us2)
    let rec match__ (__g, Xs1, us2) =
      matchW (__g, (Whnf.whnf Xs1), (Whnf.whnf us2))
    (*
     templates
           p ::= Root(n, NIL) | Root(c, SP) | EVar (x, __v) | AVar A |
                 Lam (__d, p)
                   where x is uninstantiated and occurs uniquely
                   any multiple occurrence of x has been renamed to A.

                 any eta-expanded EVar remains an EVar
                 but it may be lowered during whnf (or in the special case here
                 expansion)

          SP ::= p ; SP | NIL

   *)
    (* assignExpW (__g, (__U1, s1), (__U2, s2)) = ()

     invariant:
     __g |- s1 : G1    G1 |- __U1 : V1   (__U1, s1) in whnf
     __g |- s2 : G2    G2 |- __U2 : V2   (__U2, s2) is template
  *)
    (* L1 = L2 by invariant *)
    (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
    (* because of strict *)
    (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
    (* we require unique string representation of external constants *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* Cannot occur if expressions are eta expanded *)
    (* same reasoning holds as above *)
    (* s2 = id *)
    (* don't trail, because EVar has been created since most recent choice point *)
    (* Tue Apr  2 10:23:19 2002 -bp -fp *)
    (* s2 = id *)
    (* don't trail, because AVars never survive local scope *)
    (* ETA: can't occur if eta expanded *)
    (* for rhs:  (__U2[s2])[^] 1 = __U2 [s2 o ^] 1 = __U2 [^ o (1. s2 o ^)] 1
                        = (__U2 [^] 1) [1.s2 o ^] *)
    (* by invariant us2 cannot contain any FgnExp *)
    (* s = id *)
    (* Xs1 should not contain any uninstantiated AVar anymore *)
    (* s = id *)
    (* Xs1 should not contain any uninstantiated AVar anymore *)
    let solveCnstr = solveCnstr
    let rec unifiable (__g, us1, us2) =
      try unify (__g, us1, us2); true__ with | Unify msg -> false__
    let rec instance (__g, us1, us2) =
      try match__ (__g, us1, us2); true__ with | Match msg -> false__
    (*
    fun assign(__g, us1, us2) = assignExp(__g, us1, us2, [])
    *)
    let rec assignable (__g, us1, Uts2) =
      try Some (assignExp (__g, us1, Uts2, [])) with | Assignment msg -> None
    let rec firstConstArg ((Root ((Const c as h), S) as A), s) =
      let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
      let rec constExp (__u, s) = constExpW (Whnf.whnf (__u, s))
      and constExpW =
        function
        | (Lam (__d, __u), s) -> constExp (__u, s)
        | (Root ((Const cid as H), S), s) -> Some cid
        | (_, _) -> None in
      let rec ithElem =
        function
        | (k, (App (__u, S), s)) ->
            if k = i then constExp (__u, s) else ithElem ((k + 1), (S, s))
        | (k, (IntSyn.Nil, s)) -> None in
      ((ithElem (0, (S, s)))
        (* #implicit arguments to predicate *)(* other cases cannot occur during compilation *))
  end ;;
