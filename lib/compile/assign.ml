
(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)
module type ASSIGN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* assignable (Us,ps) assigns the term U[s] to the 
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
      | (G, (Uni (L1), _), (Uni (L2), _), cnstr) -> cnstr
      | (G, ((Root (H1, S1), s1) as Us1), ((Root (H2, S2), s2) as Us2),
         cnstr) ->
          (match (H1, H2) with
           | (Const c1, Const c2) ->
               if c1 = c2
               then assignSpine (G, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Constant clash")
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then assignSpine (G, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Bound variable clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then assignSpine (G, (S1, s1), (S2, s2), cnstr)
               else raise (Assignment "Skolem constant clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then assignSpine (G, (S1, s1), (S2, s2), cnstr)
               else
                 assignExp
                   (G, (Whnf.expandDef Us1), (Whnf.expandDef Us2), cnstr)
           | (Def d1, _) -> assignExp (G, (Whnf.expandDef Us1), Us2, cnstr)
           | (_, Def d2) -> assignExp (G, Us1, (Whnf.expandDef Us2), cnstr)
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else raise (Assignment "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then cnstr
               else assignExp (G, (W1, s1), (W2, s2), cnstr)
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               assignExp (G, (W1, s1), Us2, cnstr)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               assignExp (G, Us1, (W2, s2), cnstr)
           | _ -> raise (Assignment "Head mismatch "))
      | (G, (Lam (D1, U1), s1), (Lam (D2, U2), s2), cnstr) ->
          assignExp
            ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)), (U2, (dot1 s2)),
              cnstr)
      | (G, (U1, s1), (Lam (D2, U2), s2), cnstr) ->
          assignExp
            ((Decl (G, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (U2, (dot1 s2)), cnstr)
      | (G, (Pi (((Dec (_, V1) as D1), _), U1), s1),
         (Pi (((Dec (_, V2) as D2), _), U2), s2), cnstr) ->
          let cnstr' = assignExp (G, (V1, s1), (V2, s2), cnstr) in
          assignExp
            ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)), (U2, (dot1 s2)),
              cnstr')
      | (G, ((U, s1) as Us1), ((EVar (r2, _, _, _), s2) as Us2), cnstr) ->
          ((:=) r2 SOME (EClo Us1); cnstr)
      | (G, ((U, s1) as Us1), ((AVar r2, s2) as Us2), cnstr) ->
          ((:=) r2 SOME (EClo Us1); cnstr)
      | (G, (Lam (D1, U1), s1), (U2, s2), cnstr) ->
          assignExp
            ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)),
              ((Redex
                  ((EClo (U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)), cnstr)
      | (G, Us1, ((EClo (U, s'), s) as Us2), cnstr) ->
          assignExp (G, Us1, (U, (comp (s', s))), cnstr)
      | (G, ((EVar (r, _, V, Cnstr), s) as Us1), Us2, cnstr) ->
          (Eqn (G, (EClo Us1), (EClo Us2))) :: cnstr
      | (G, ((EClo (U, s'), s) as Us1), Us2, cnstr) ->
          assignExp (G, (U, (comp (s', s))), Us2, cnstr)
      | (G, ((FgnExp (_, fe), _) as Us1), Us2, cnstr) ->
          (Eqn (G, (EClo Us1), (EClo Us2))) :: cnstr
      | (G, Us1, ((FgnExp (_, fe), _) as Us2), cnstr) ->
          (Eqn (G, (EClo Us1), (EClo Us2))) :: cnstr
    let rec assignSpine =
      function
      | (G, (Nil, _), (Nil, _), cnstr) -> cnstr
      | (G, (SClo (S1, s1'), s1), Ss, cnstr) ->
          assignSpine (G, (S1, (comp (s1', s1))), Ss, cnstr)
      | (G, Ss, (SClo (S2, s2'), s2), cnstr) ->
          assignSpine (G, Ss, (S2, (comp (s2', s2))), cnstr)
      | (G, (App (U1, S1), s1), (App (U2, S2), s2), cnstr) ->
          let cnstr' = assignExp (G, (U1, s1), (U2, s2), cnstr) in
          assignSpine (G, (S1, s1), (S2, s2), cnstr')
    let rec assignExp (G, Us1, ((U2, s2) as Us2), cnstr) =
      assignExpW (G, (Whnf.whnf Us1), (Whnf.whnf Us2), cnstr)
    let rec solveCnstr =
      function
      | nil -> true__
      | (Eqn (G, U1, U2))::Cnstr ->
          (Unify.unifiable (G, (U1, id), (U2, id))) && (solveCnstr Cnstr)
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
      | (G, ((AVar (ref (NONE) as r) as Xs1), s), Us2) ->
          (:=) r SOME (EClo Us2)
      | (G, Xs1, Us2) -> Unify.unifyW (G, Xs1, Us2)
    let rec unify (G, Xs1, Us2) =
      unifyW (G, (Whnf.whnf Xs1), (Whnf.whnf Us2))
    let rec matchW =
      function
      | (G, ((AVar (ref (NONE) as r) as Xs1), s), Us2) ->
          (:=) r SOME (EClo Us2)
      | (G, Xs1, Us2) -> Match.matchW (G, Xs1, Us2)
    let rec match__ (G, Xs1, Us2) =
      matchW (G, (Whnf.whnf Xs1), (Whnf.whnf Us2))
    (*
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
    (* assignExpW (G, (U1, s1), (U2, s2)) = ()

     invariant:
     G |- s1 : G1    G1 |- U1 : V1   (U1, s1) in whnf
     G |- s2 : G2    G2 |- U2 : V2   (U2, s2) is template
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
    (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
    (* by invariant Us2 cannot contain any FgnExp *)
    (* s = id *)
    (* Xs1 should not contain any uninstantiated AVar anymore *)
    (* s = id *)
    (* Xs1 should not contain any uninstantiated AVar anymore *)
    let solveCnstr = solveCnstr
    let rec unifiable (G, Us1, Us2) =
      try unify (G, Us1, Us2); true__ with | Unify msg -> false__
    let rec instance (G, Us1, Us2) =
      try match__ (G, Us1, Us2); true__ with | Match msg -> false__
    (*
    fun assign(G, Us1, Us2) = assignExp(G, Us1, Us2, [])
    *)
    let rec assignable (G, Us1, Uts2) =
      try SOME (assignExp (G, Us1, Uts2, [])) with | Assignment msg -> NONE
    let rec firstConstArg ((Root ((Const c as h), S) as A), s) =
      let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
      let rec constExp (U, s) = constExpW (Whnf.whnf (U, s))
      and constExpW =
        function
        | (Lam (D, U), s) -> constExp (U, s)
        | (Root ((Const cid as H), S), s) -> SOME cid
        | (_, _) -> NONE in
      let rec ithElem =
        function
        | (k, (App (U, S), s)) ->
            if k = i then constExp (U, s) else ithElem ((k + 1), (S, s))
        | (k, (IntSyn.Nil, s)) -> NONE in
      ((ithElem (0, (S, s)))
        (* #implicit arguments to predicate *)(* other cases cannot occur during compilation *))
  end ;;
