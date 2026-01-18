
(* Type Checking *)
(* Author: Carsten Schuermann *)
module type TYPECHECK  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    val check : (IntSyn.__Exp * IntSyn.__Exp) -> unit
    val checkDec : (IntSyn.dctx * (IntSyn.__Dec * IntSyn.__Sub)) -> unit
    val checkConv : (IntSyn.__Exp * IntSyn.__Exp) -> unit
    val infer : IntSyn.__Exp -> IntSyn.__Exp
    val infer' : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
    val typeCheck : (IntSyn.dctx * (IntSyn.__Exp * IntSyn.__Exp)) -> unit
    val typeCheckCtx : IntSyn.dctx -> unit
    (* val typeCheckSpine : IntSyn.dctx * IntSyn.Spine -> unit *)
    val typeCheckSub : (IntSyn.dctx * IntSyn.__Sub * IntSyn.dctx) -> unit
  end;;




(* Type Checking *)
(* Author: Carsten Schuermann *)
module TypeCheck(TypeCheck:sig
                             (*! structure IntSyn' : INTSYN !*)
                             module Conv : CONV
                             module Whnf : WHNF
                             module Names : NAMES
                             (*! sharing Conv.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn'  !*)
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             module Print : PRINT
                           end) : TYPECHECK =
  struct
    (*! sharing Print.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    module I = IntSyn
    let rec subToString =
      function
      | (G, Dot (Idx n, s)) ->
          (^) ((Int.toString n) ^ ".") subToString (G, s)
      | (G, Dot (Exp (U), s)) ->
          (^) (((^) "(" Print.expToString (G, U)) ^ ").") subToString (G, s)
      | (G, Dot (Block (LVar _ as L), s)) ->
          (^) ((LVarToString (G, L)) ^ ".") subToString (G, s)
      | (G, Shift n) -> (^) "^" Int.toString n
    let rec LVarToString =
      function
      | (G, LVar (ref (SOME (B)), sk, (l, t))) ->
          LVarToString (G, (I.blockSub (B, sk)))
      | (G, LVar (ref (NONE), sk, (cid, t))) ->
          ((^) (((^) "#" I.conDecName (I.sgnLookup cid)) ^ "[") subToString
             (G, t))
            ^ "]"
    let rec checkExp (G, Us, Vs) =
      let Us' = inferExp (G, Us) in
      if Conv.conv (Us', Vs) then () else raise (Error "Type mismatch")
    let rec inferUni (I.Type) = I.Kind
    let rec inferExpW =
      function
      | (G, (Uni (L), _)) -> ((I.Uni (inferUni L)), I.id)
      | (G, (Pi ((D, _), V), s)) ->
          (checkDec (G, (D, s));
           inferExp ((I.Decl (G, (I.decSub (D, s)))), (V, (I.dot1 s))))
      | (G, (Root (C, S), s)) ->
          inferSpine (G, (S, s), (Whnf.whnf ((inferCon (G, C)), I.id)))
      | (G, (Lam (D, U), s)) ->
          (checkDec (G, (D, s));
           ((I.Pi
               (((I.decSub (D, s)), I.Maybe),
                 (I.EClo
                    (inferExp
                       ((I.Decl (G, (I.decSub (D, s)))), (U, (I.dot1 s))))))),
             I.id))
      | (G, (FgnExp csfe, s)) ->
          inferExp (G, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec inferExp (G, Us) = inferExpW (G, (Whnf.whnf Us))
    let rec inferSpine =
      function
      | (G, (I.Nil, _), Vs) -> Vs
      | (G, (SClo (S, s'), s), Vs) ->
          inferSpine (G, (S, (I.comp (s', s))), Vs)
      | (G, (App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) ->
          (checkExp (G, (U, s1), (V1, s2));
           inferSpine
             (G, (S, s1),
               (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s1))), s2))))))
      | (G, ((App _, _) as Ss), ((Root (Def _, _), _) as Vs)) ->
          inferSpine (G, Ss, (Whnf.expandDef Vs))
      | (G, (App (U, S), _), (V, s)) ->
          raise (Error "Expression is applied, but not a function")
    let rec inferCon =
      function
      | (G, BVar k') -> let Dec (_, V) = I.ctxDec (G, k') in V
      | (G, Proj (B, i)) -> let Dec (_, V) = I.blockDec (G, B, i) in V
      | (G, Const c) -> I.constType c
      | (G, Def d) -> I.constType d
      | (G, Skonst c) -> I.constType c
      | (G, FgnConst (cs, conDec)) -> I.conDecType conDec
    let rec typeCheck (G, (U, V)) =
      checkCtx G; checkExp (G, (U, I.id), (V, I.id))
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (G, D), Shift k, I.Null) ->
          if k > 0
          then checkSub (G, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (G', Shift k, G) ->
          checkSub (G', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), G)
      | (G', Dot (Idx k, s'), Decl (G, Dec (_, V2))) ->
          let _ = checkSub (G', s', G) in
          let Dec (_, V1) = I.ctxDec (G', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then ()
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (G', V1))
                         ^ "\n  expected: ")
                    Print.expToString (G', (I.EClo (V2, s')))))
      | (G', Dot (Exp (U), s'), Decl (G, Dec (_, V2))) ->
          let _ = checkSub (G', s', G) in
          let _ = typeCheck (G', (U, (I.EClo (V2, s')))) in ()
      | (G', Dot (Idx w, t), Decl (G, BDec (_, (l, s)))) ->
          let _ = checkSub (G', t, G) in
          let BDec (_, (l', s')) = I.ctxDec (G', w) in
          if l <> l'
          then raise (Error "Incompatible block labels found")
          else
            if Conv.convSub ((I.comp (s, t)), s')
            then ()
            else
              raise
                (Error "Substitution in block declaration not well-typed")
      | (G', Dot (Block (Inst (I)), t), Decl (G, BDec (_, (l, s)))) ->
          let _ = checkSub (G', t, G) in
          let (G, L) = I.constBlock l in
          let _ = checkBlock (G', I, ((I.comp (s, t)), L)) in ()
      | (G', (Dot (_, _) as s), I.Null) ->
          raise
            (Error ((^) ("Long substitution" ^ "\n") subToString (G', s)))
    let rec checkBlock =
      function
      | (G, nil, (_, nil)) -> ()
      | (G, (U)::I, (t, (Dec (_, V))::L)) ->
          (checkExp (G, (U, I.id), (V, t));
           checkBlock (G, I, ((I.Dot ((I.Exp U), t)), L)))
    let rec checkDec =
      function
      | (G, (Dec (_, V), s)) -> checkExp (G, (V, s), ((I.Uni I.Type), I.id))
      | (G, (BDec (_, (c, t)), s)) ->
          let (Gsome, piDecs) = I.constBlock c in
          checkSub (G, (I.comp (t, s)), Gsome)
      | (G, (NDec, _)) -> ()
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (G, D) -> (checkCtx G; checkDec (G, (D, I.id)))
    let rec check (U, V) = checkExp (I.Null, (U, I.id), (V, I.id))
    let rec infer (U) = I.EClo (inferExp (I.Null, (U, I.id)))
    let rec infer' (G, U) = I.EClo (inferExp (G, (U, I.id)))
    let rec checkConv (U1, U2) =
      if Conv.conv ((U1, I.id), (U2, I.id))
      then ()
      else
        raise
          (Error
             ((^) (((^) "Terms not equal\n  left: " Print.expToString
                      (I.Null, U1))
                     ^ "\n  right:")
                Print.expToString (I.Null, U2)))
    (* for debugging purposes *)
    (* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
    (* some well-formedness conditions are assumed for input expressions *)
    (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)
    (* checkExp (G, (U, s1), (V2, s2)) = ()

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
            G1 |- U : V1
       and  G  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)
    (* impossible: Kind *)
    (* inferExp (G, (U, s)) = (V', s')

       Invariant:
       If   G  |- s : G1
       then if G1 |- U : V   (U doesn't contain EVAR's, FVAR's)
            then  G  |- s' : G'     G' |- V' : L
            and   G  |- V [s] = V'[s'] : L
            else exception Error is raised.
     *)
    (* no cases for Redex, EVars and EClo's *)
    (* AK: typecheck a representative -- presumably if one rep checks, they all do *)
    (* inferExp (G, Us) = (V', s')

       Invariant: same as inferExp, argument is not in whnf
    *)
    (* inferSpine (G, (S, s1), (V, s2)) = (V', s')

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2  and  G2 |- V : L ,   (V, s2) in whnf
       and  (S,V  don't contain EVAR's, FVAR's)
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
            then G |- s' : G'    and  G' |- V' : L
            and  G |- V1 [s1]   = V [s2] : L
            and  G |- V1'[s1]   = V' [s'] : L
    *)
    (* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             G |- U [s1] : V1 [s2]
             Hence
             G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             G |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that G |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
    (* V <> (Pi x:V1. V2, s) *)
    (* inferCon (G, C) = V'

       Invariant:
       If    G |- C : V
       and  (C  doesn't contain FVars)
       then  G' |- V' : L      (for some level L)
       and   G |- V = V' : L
       else exception Error is raised.
    *)
    (* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
    (* no case for FVar *)
    (* checkSub (G1, s, G2) = ()

       Invariant:
       The function terminates
       iff  G1 |- s : G2
    *)
    (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
    (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
    (* Front of the substitution cannot be a I.Bidx or LVar *)
    (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
    (* G' |- s' : GSOME *)
    (* G  |- s  : GSOME *)
    (* G' |- t  : G       (verified below) *)
    (*
      | checkSub (G', I.Dot (I.Block (I.Bidx _), t), G) =
        raise Error "Unexpected block index in substitution"
      | checkSub (G', I.Dot (I.Block (I.LVar _), t), G) =
        raise Error "Unexpected LVar in substitution after abstraction"
      *)
    (* checkDec (G, (x:V, s)) = B

       Invariant:
       If G |- s : G1
       then B iff G |- V[s] : type
    *)
    (* G1 |- t : GSOME *)
    (* G  |- s : G1 *)
    let check = check
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
                     (*! structure IntSyn' = IntSyn !*)
                     module Conv = Conv
                     module Whnf = Whnf
                     module Names = Names
                     module Print = Print
                   end)
module Strict =
  (Make_Strict)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  module Whnf = Whnf
                  module Paths' = Paths
                end);;
