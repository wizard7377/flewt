
module type TYPECHECK  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Author: Carsten Schuermann *)
      (* Type Checking *)) 
    val check : (IntSyn.__Exp * IntSyn.__Exp) -> unit
    val checkDec : (IntSyn.dctx * (IntSyn.__Dec * IntSyn.__Sub)) -> unit
    val checkConv : (IntSyn.__Exp * IntSyn.__Exp) -> unit
    val infer : IntSyn.__Exp -> IntSyn.__Exp
    val infer' : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
    val typeCheck : (IntSyn.dctx * (IntSyn.__Exp * IntSyn.__Exp)) -> unit
    val typeCheckCtx : IntSyn.dctx -> unit
    val typeCheckSub :
      (IntSyn.dctx * IntSyn.__Sub * IntSyn.dctx) ->
        ((unit)(* val typeCheckSpine : IntSyn.dctx * IntSyn.Spine -> unit *))
  end;;




module TypeCheck(TypeCheck:sig
                             module Conv : CONV
                             module Whnf : WHNF
                             module Names : NAMES
                             module Print :
                             ((PRINT)(* Type Checking *)
                             (* Author: Carsten Schuermann *)(*! structure IntSyn' : INTSYN !*)
                             (*! sharing Conv.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn'  !*)
                             (*! sharing Names.IntSyn = IntSyn' !*))
                           end) : TYPECHECK =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing Print.IntSyn = IntSyn' !*))
      
    module I = IntSyn
    let rec subToString =
      function
      | (g, Dot (Idx n, s)) ->
          (^) ((Int.toString n) ^ ".") subToString (g, s)
      | (g, Dot (Exp (U), s)) ->
          (^) (((^) "(" Print.expToString (g, U)) ^ ").") subToString (g, s)
      | (g, Dot (Block (LVar _ as L), s)) ->
          (^) ((LVarToString (g, L)) ^ ".") subToString (g, s)
      | (g, Shift n) -> (^) "^" Int.toString n
    let rec LVarToString =
      function
      | (g, LVar (ref (SOME (B)), sk, (l, t))) ->
          LVarToString (g, (I.blockSub (B, sk)))
      | (g, LVar (ref (NONE), sk, (cid, t))) ->
          ((^) (((^) "#" I.conDecName (I.sgnLookup cid)) ^ "[") subToString
             (g, t))
            ^ "]"
    let rec checkExp (g, Us, Vs) =
      let Us' = inferExp (g, Us) in
      if Conv.conv (Us', Vs) then () else raise (Error "Type mismatch")
    let rec inferUni (I.Type) = I.Kind
    let rec inferExpW =
      function
      | (g, (Uni (L), _)) -> ((I.Uni (inferUni L)), I.id)
      | (g, (Pi ((D, _), V), s)) ->
          (checkDec (g, (D, s));
           inferExp ((I.Decl (g, (I.decSub (D, s)))), (V, (I.dot1 s))))
      | (g, (Root (C, S), s)) ->
          inferSpine (g, (S, s), (Whnf.whnf ((inferCon (g, C)), I.id)))
      | (g, (Lam (D, U), s)) ->
          (checkDec (g, (D, s));
           ((I.Pi
               (((I.decSub (D, s)), I.Maybe),
                 (I.EClo
                    (inferExp
                       ((I.Decl (g, (I.decSub (D, s)))), (U, (I.dot1 s))))))),
             I.id))
      | (g, (FgnExp csfe, s)) ->
          inferExp (g, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec inferExp (g, Us) = inferExpW (g, (Whnf.whnf Us))
    let rec inferSpine =
      function
      | (g, (I.Nil, _), Vs) -> Vs
      | (g, (SClo (S, s'), s), Vs) ->
          inferSpine (g, (S, (I.comp (s', s))), Vs)
      | (g, (App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) ->
          (checkExp (g, (U, s1), (V1, s2));
           inferSpine
             (g, (S, s1),
               (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s1))), s2))))))
      | (g, ((App _, _) as Ss), ((Root (Def _, _), _) as Vs)) ->
          inferSpine (g, Ss, (Whnf.expandDef Vs))
      | (g, (App (U, S), _), (V, s)) ->
          raise (Error "Expression is applied, but not a function")
    let rec inferCon =
      function
      | (g, BVar k') -> let Dec (_, V) = I.ctxDec (g, k') in V
      | (g, Proj (B, i)) -> let Dec (_, V) = I.blockDec (g, B, i) in V
      | (g, Const c) -> I.constType c
      | (g, Def d) -> I.constType d
      | (g, Skonst c) -> I.constType c
      | (g, FgnConst (cs, conDec)) -> I.conDecType conDec
    let rec typeCheck (g, (U, V)) =
      checkCtx g; checkExp (g, (U, I.id), (V, I.id))
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (g, D), Shift k, I.Null) ->
          if k > 0
          then checkSub (g, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (g', Shift k, g) ->
          checkSub (g', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), g)
      | (g', Dot (Idx k, s'), Decl (g, Dec (_, V2))) ->
          let _ = checkSub (g', s', g) in
          let Dec (_, V1) = I.ctxDec (g', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then ()
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (g', V1))
                         ^ "\n  expected: ")
                    Print.expToString (g', (I.EClo (V2, s')))))
      | (g', Dot (Exp (U), s'), Decl (g, Dec (_, V2))) ->
          let _ = checkSub (g', s', g) in
          let _ = typeCheck (g', (U, (I.EClo (V2, s')))) in ()
      | (g', Dot (Idx w, t), Decl (g, BDec (_, (l, s)))) ->
          let _ = checkSub (g', t, g) in
          let BDec (_, (l', s')) = I.ctxDec (g', w) in
          if l <> l'
          then raise (Error "Incompatible block labels found")
          else
            if Conv.convSub ((I.comp (s, t)), s')
            then ()
            else
              raise
                (Error "Substitution in block declaration not well-typed")
      | (g', Dot (Block (Inst (I)), t), Decl (g, BDec (_, (l, s)))) ->
          let _ = checkSub (g', t, g) in
          let (g, L) = I.constBlock l in
          let _ = checkBlock (g', I, ((I.comp (s, t)), L)) in ()
      | (g', (Dot (_, _) as s), I.Null) ->
          raise
            (Error ((^) ("Long substitution" ^ "\n") subToString (g', s)))
    let rec checkBlock =
      function
      | (g, nil, (_, nil)) -> ()
      | (g, (U)::I, (t, (Dec (_, V))::L)) ->
          (checkExp (g, (U, I.id), (V, t));
           checkBlock (g, I, ((I.Dot ((I.Exp U), t)), L)))
    let rec checkDec =
      function
      | (g, (Dec (_, V), s)) -> checkExp (g, (V, s), ((I.Uni I.Type), I.id))
      | (g, (BDec (_, (c, t)), s)) ->
          let (Gsome, piDecs) = I.constBlock c in
          checkSub (g, (I.comp (t, s)), Gsome)
      | (g, (NDec, _)) -> ()
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (g, D) -> (checkCtx g; checkDec (g, (D, I.id)))
    let rec check (U, V) = checkExp (I.Null, (U, I.id), (V, I.id))
    let rec infer (U) = I.EClo (inferExp (I.Null, (U, I.id)))
    let rec infer' (g, U) = I.EClo (inferExp (g, (U, I.id)))
    let rec checkConv (u1, u2) =
      if Conv.conv ((u1, I.id), (u2, I.id))
      then ()
      else
        raise
          (Error
             ((^) (((^) "Terms not equal\n  left: " Print.expToString
                      (I.Null, u1))
                     ^ "\n  right:")
                Print.expToString (I.Null, u2)))
    let ((check)(* for debugging purposes *)(* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
      (* some well-formedness conditions are assumed for input expressions *)
      (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)
      (* checkExp (g, (U, s1), (V2, s2)) = ()

       Invariant:
       If   g |- s1 : G1
       and  g |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
            G1 |- U : V1
       and  g  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)
      (* impossible: Kind *)(* inferExp (g, (U, s)) = (V', s')

       Invariant:
       If   g  |- s : G1
       then if G1 |- U : V   (U doesn't contain EVAR's, FVAR's)
            then  g  |- s' : g'     g' |- V' : L
            and   g  |- V [s] = V'[s'] : L
            else exception Error is raised.
     *)
      (* no cases for Redex, EVars and EClo's *)(* AK: typecheck a representative -- presumably if one rep checks, they all do *)
      (* inferExp (g, Us) = (V', s')

       Invariant: same as inferExp, argument is not in whnf
    *)
      (* inferSpine (g, (S, s1), (V, s2)) = (V', s')

       Invariant:
       If   g |- s1 : G1
       and  g |- s2 : G2  and  G2 |- V : L ,   (V, s2) in whnf
       and  (S,V  don't contain EVAR's, FVAR's)
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
            then g |- s' : g'    and  g' |- V' : L
            and  g |- V1 [s1]   = V [s2] : L
            and  g |- V1'[s1]   = V' [s'] : L
    *)
      (* g |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             g |- U [s1] : V1 [s2]
             Hence
             g |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             g |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that g |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
      (* V <> (Pi x:V1. V2, s) *)(* inferCon (g, C) = V'

       Invariant:
       If    g |- C : V
       and  (C  doesn't contain FVars)
       then  g' |- V' : L      (for some level L)
       and   g |- V = V' : L
       else exception Error is raised.
    *)
      (* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
      (* no case for FVar *)(* checkSub (G1, s, G2) = ()

       Invariant:
       The function terminates
       iff  G1 |- s : G2
    *)
      (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      (* Front of the substitution cannot be a I.Bidx or LVar *)
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      (* g' |- s' : GSOME *)(* g  |- s  : GSOME *)
      (* g' |- t  : g       (verified below) *)(*
      | checkSub (g', I.Dot (I.Block (I.Bidx _), t), g) =
        raise Error "Unexpected block index in substitution"
      | checkSub (g', I.Dot (I.Block (I.LVar _), t), g) =
        raise Error "Unexpected LVar in substitution after abstraction"
      *)
      (* checkDec (g, (x:V, s)) = B

       Invariant:
       If g |- s : G1
       then B iff g |- V[s] : type
    *)
      (* G1 |- t : GSOME *)(* g  |- s : G1 *))
      = check
    let checkDec = checkDec
    let checkConv = checkConv
    let infer = infer
    let infer' = infer'
    let typeCheck = typeCheck
    let typeCheckCtx = checkCtx
    let typeCheckSub = checkSub
  end ;;




module TypeCheck =
  (Make_TypeCheck)(struct
                     module Conv =
                       ((Conv)(*! structure IntSyn' = IntSyn !*))
                     module Whnf = Whnf
                     module Names = Names
                     module Print = Print
                   end)
module Strict =
  (Make_Strict)(struct
                  module Whnf =
                    ((Whnf)(*! structure IntSyn' = IntSyn !*))
                  module Paths' = Paths
                end);;
