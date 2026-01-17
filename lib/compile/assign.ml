
module type ASSIGN  =
  sig
    val assignable :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((IntSyn.__Cnstr)(* EVars and AVars in ps are instantiated as an effect *)
          (* assignable (Us,ps) assigns the term U[s] to the 
     linear higher-order pattern p[s]; if successfull it
     returns a list of residual equations that have been postponed *)
          (*! structure IntSyn : INTSYN !*)(* Modified: Brigitte Pientka *)
          (* Author: Larry Greenfield *)(* Assignment *))
          list option
    val solveCnstr :
      IntSyn.__Cnstr list ->
        ((bool)(* solveCnstr solves dynamically residuated equations *))
    val unifiable :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((bool)(* unifiable solves statically residuated equations *))
    val instance :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((bool)(* instance solves statically residuated equations *))
    val firstConstArg : (IntSyn.__Exp * IntSyn.__Sub) -> IntSyn.cid option
  end;;




module Assign(Assign:sig
                       module Whnf : WHNF
                       module Unify : UNIFY
                       module Print :
                       ((PRINT)(* Assignment *)(* Author: Brigitte Pientka *)
                       (*! structure IntSyn' : INTSYN !*)
                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                       (*! sharing Unify.IntSyn = IntSyn' !*))
                     end) : ASSIGN =
  struct
    exception Assignment of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing Print.IntSyn = IntSyn' !*))
      
    open IntSyn
    let rec assignExpW =
      function
      | (g, (Uni (L1), _), (Uni (L2), _), cnstr) -> cnstr
      | (g, ((Root (H1, s1), s1) as us1), ((Root (H2, s2), s2) as us2),
         cnstr) ->
          (match (H1, H2) with
           | (Const c1, Const c2) ->
               if c1 = c2
               then assignSpine (g, (s1, s1), (s2, s2), cnstr)
               else raise (Assignment "Constant clash")
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then assignSpine (g, (s1, s1), (s2, s2), cnstr)
               else raise (Assignment "Bound variable clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then assignSpine (g, (s1, s1), (s2, s2), cnstr)
               else raise (Assignment "Skolem constant clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then assignSpine (g, (s1, s1), (s2, s2), cnstr)
               else
                 assignExp
                   (g, (Whnf.expandDef us1), (Whnf.expandDef us2), cnstr)
           | (Def d1, _) -> assignExp (g, (Whnf.expandDef us1), us2, cnstr)
           | (_, Def d2) -> assignExp (g, us1, (Whnf.expandDef us2), cnstr)
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else raise (Assignment "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else assignExp (g, (W1, s1), (W2, s2), cnstr)
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               assignExp (g, (W1, s1), us2, cnstr)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               assignExp (g, us1, (W2, s2), cnstr)
           | _ -> raise (Assignment "Head mismatch "))
      | (g, (Lam (D1, u1), s1), (Lam (D2, u2), s2), cnstr) ->
          assignExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)), (u2, (dot1 s2)),
              cnstr)
      | (g, (u1, s1), (Lam (D2, u2), s2), cnstr) ->
          assignExp
            ((Decl (g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (u1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (u2, (dot1 s2)), cnstr)
      | (g, (Pi (((Dec (_, V1) as D1), _), u1), s1),
         (Pi (((Dec (_, V2) as D2), _), u2), s2), cnstr) ->
          let cnstr' = assignExp (g, (V1, s1), (V2, s2), cnstr) in
          assignExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)), (u2, (dot1 s2)),
              cnstr')
      | (g, ((U, s1) as us1), ((EVar (r2, _, _, _), s2) as us2), cnstr) ->
          ((:=) r2 SOME (EClo us1); cnstr)
      | (g, ((U, s1) as us1), ((AVar r2, s2) as us2), cnstr) ->
          ((:=) r2 SOME (EClo us1); cnstr)
      | (g, (Lam (D1, u1), s1), (u2, s2), cnstr) ->
          assignExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)),
              ((Redex
                  ((EClo (u2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)), cnstr)
      | (g, us1, ((EClo (U, s'), s) as us2), cnstr) ->
          assignExp (g, us1, (U, (comp (s', s))), cnstr)
      | (g, ((EVar (r, _, V, Cnstr), s) as us1), us2, cnstr) ->
          (Eqn (g, (EClo us1), (EClo us2))) :: cnstr
      | (g, ((EClo (U, s'), s) as us1), us2, cnstr) ->
          assignExp (g, (U, (comp (s', s))), us2, cnstr)
      | (g, ((FgnExp (_, fe), _) as us1), us2, cnstr) ->
          (Eqn (g, (EClo us1), (EClo us2))) :: cnstr
      | (g, us1, ((FgnExp (_, fe), _) as us2), cnstr) ->
          (Eqn (g, (EClo us1), (EClo us2))) :: cnstr
    let rec assignSpine =
      function
      | (g, (Nil, _), (Nil, _), cnstr) -> cnstr
      | (g, (SClo (s1, s1'), s1), Ss, cnstr) ->
          assignSpine (g, (s1, (comp (s1', s1))), Ss, cnstr)
      | (g, Ss, (SClo (s2, s2'), s2), cnstr) ->
          assignSpine (g, Ss, (s2, (comp (s2', s2))), cnstr)
      | (g, (App (u1, s1), s1), (App (u2, s2), s2), cnstr) ->
          let cnstr' = assignExp (g, (u1, s1), (u2, s2), cnstr) in
          assignSpine (g, (s1, s1), (s2, s2), cnstr')
    let rec assignExp (g, us1, ((u2, s2) as us2), cnstr) =
      assignExpW (g, (Whnf.whnf us1), (Whnf.whnf us2), cnstr)
    let rec solveCnstr =
      function
      | nil -> true__
      | (Eqn (g, u1, u2))::Cnstr ->
          (Unify.unifiable (g, (u1, id), (u2, id))) && (solveCnstr Cnstr)
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
      | (g, ((AVar (ref (NONE) as r) as xs1), s), us2) ->
          (:=) r SOME (EClo us2)
      | (g, xs1, us2) -> Unify.unifyW (g, xs1, us2)
    let rec unify (g, xs1, us2) =
      unifyW (g, (Whnf.whnf xs1), (Whnf.whnf us2))
    let rec matchW =
      function
      | (g, ((AVar (ref (NONE) as r) as xs1), s), us2) ->
          (:=) r SOME (EClo us2)
      | (g, xs1, us2) -> Match.matchW (g, xs1, us2)
    let rec match__ (g, xs1, us2) =
      matchW (g, (Whnf.whnf xs1), (Whnf.whnf us2))
    let ((solveCnstr)(*
     templates
           p ::= Root(n, NIL) | Root(c, SP) | EVar (X, V) | AVar A |
                 Lam (D, p)
                   where X is uninstantiated and occurs uniquely
                   any multiple occurrence of X has been renamed to A.

                 any eta-expanded EVar remains an EVar
                 but it may be lowered during whnf (or in the special case here
                 expansion)

          SP ::= p ; SP | NIL

   *)
      (* assignExpW (g, (u1, s1), (u2, s2)) = ()

     invariant:
     g |- s1 : G1    G1 |- u1 : V1   (u1, s1) in whnf
     g |- s2 : G2    G2 |- u2 : V2   (u2, s2) is template
  *)
      (* L1 = L2 by invariant *)(* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
      (* because of strict *)(* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
      (* we require unique string representation of external constants *)
      (* D1[s1] = D2[s2]  by invariant *)(* Cannot occur if expressions are eta expanded *)
      (* same reasoning holds as above *)(* s2 = id *)
      (* don't trail, because EVar has been created since most recent choice point *)
      (* Tue Apr  2 10:23:19 2002 -bp -fp *)(* s2 = id *)
      (* don't trail, because AVars never survive local scope *)
      (* ETA: can't occur if eta expanded *)(* for rhs:  (u2[s2])[^] 1 = u2 [s2 o ^] 1 = u2 [^ o (1. s2 o ^)] 1
                        = (u2 [^] 1) [1.s2 o ^] *)
      (* by invariant us2 cannot contain any FgnExp *)
      (* s = id *)(* xs1 should not contain any uninstantiated AVar anymore *)
      (* s = id *)(* xs1 should not contain any uninstantiated AVar anymore *))
      = solveCnstr
    let rec unifiable (g, us1, us2) =
      try unify (g, us1, us2); true__ with | Unify msg -> false__
    let rec instance (g, us1, us2) =
      try match__ (g, us1, us2); true__ with | Match msg -> false__
    let rec assignable
      (((g)(*
    fun assign(g, us1, us2) = assignExp(g, us1, us2, [])
    *)),
       us1, Uts2)
      = try SOME (assignExp (g, us1, Uts2, [])) with | Assignment msg -> NONE
    let rec firstConstArg ((Root ((Const c as h), S) as A), s) =
      let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
      let constExp
        (((U)(* #implicit arguments to predicate *)), s) =
        constExpW (Whnf.whnf (U, s))
      and constExpW =
        function
        | (Lam (D, U), s) -> constExp (U, s)
        | (Root ((Const cid as H), S), s) -> SOME cid
        | (_, _) -> NONE in
      let ithElem =
        function
        | (((k)(* other cases cannot occur during compilation *)),
           (App (U, S), s)) ->
            if k = i then constExp (U, s) else ithElem ((k + 1), (S, s))
        | (k, (IntSyn.Nil, s)) -> NONE in
      ithElem (0, (S, s))
  end ;;
