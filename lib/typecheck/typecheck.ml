
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
      | (__g, Dot (Idx n, s)) ->
          (^) ((Int.toString n) ^ ".") subToString (__g, s)
      | (__g, Dot (Exp (__u), s)) ->
          (^) (((^) "(" Print.expToString (__g, __u)) ^ ").") subToString (__g, s)
      | (__g, Dot (Block ((LVar _) as __l), s)) ->
          (^) ((LVarToString (__g, __l)) ^ ".") subToString (__g, s)
      | (__g, Shift n) -> (^) "^" Int.toString n
    let rec LVarToString =
      function
      | (__g, LVar ({ contents = Some (B) }, sk, (l, t))) ->
          LVarToString (__g, (I.blockSub (B, sk)))
      | (__g, LVar (ref (None), sk, (cid, t))) ->
          ((^) (((^) "#" I.conDecName (I.sgnLookup cid)) ^ "[") subToString
             (__g, t))
            ^ "]"
    let rec checkExp (__g, __Us, __Vs) =
      let __Us' = inferExp (__g, __Us) in
      if Conv.conv (__Us', __Vs) then () else raise (Error "Type mismatch")
    let rec inferUni (I.Type) = I.Kind
    let rec inferExpW =
      function
      | (__g, (Uni (__l), _)) -> ((I.Uni (inferUni __l)), I.id)
      | (__g, (Pi ((__d, _), __v), s)) ->
          (checkDec (__g, (__d, s));
           inferExp ((I.Decl (__g, (I.decSub (__d, s)))), (__v, (I.dot1 s))))
      | (__g, (Root (C, S), s)) ->
          inferSpine (__g, (S, s), (Whnf.whnf ((inferCon (__g, C)), I.id)))
      | (__g, (Lam (__d, __u), s)) ->
          (checkDec (__g, (__d, s));
           ((I.Pi
               (((I.decSub (__d, s)), I.Maybe),
                 (I.EClo
                    (inferExp
                       ((I.Decl (__g, (I.decSub (__d, s)))), (__u, (I.dot1 s))))))),
             I.id))
      | (__g, (FgnExp csfe, s)) ->
          inferExp (__g, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec inferExp (__g, __Us) = inferExpW (__g, (Whnf.whnf __Us))
    let rec inferSpine =
      function
      | (__g, (I.Nil, _), __Vs) -> __Vs
      | (__g, (SClo (S, s'), s), __Vs) ->
          inferSpine (__g, (S, (I.comp (s', s))), __Vs)
      | (__g, (App (__u, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) ->
          (checkExp (__g, (__u, s1), (V1, s2));
           inferSpine
             (__g, (S, s1),
               (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (__u, s1))), s2))))))
      | (__g, ((App _, _) as __Ss), ((Root (Def _, _), _) as __Vs)) ->
          inferSpine (__g, __Ss, (Whnf.expandDef __Vs))
      | (__g, (App (__u, S), _), (__v, s)) ->
          raise (Error "Expression is applied, but not a function")
    let rec inferCon =
      function
      | (__g, BVar k') -> let Dec (_, __v) = I.ctxDec (__g, k') in __v
      | (__g, Proj (B, i)) -> let Dec (_, __v) = I.blockDec (__g, B, i) in __v
      | (__g, Const c) -> I.constType c
      | (__g, Def d) -> I.constType d
      | (__g, Skonst c) -> I.constType c
      | (__g, FgnConst (cs, conDec)) -> I.conDecType conDec
    let rec typeCheck (__g, (__u, __v)) =
      checkCtx __g; checkExp (__g, (__u, I.id), (__v, I.id))
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (__g, __d), Shift k, I.Null) ->
          if k > 0
          then checkSub (__g, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (__g', Shift k, __g) ->
          checkSub (__g', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __g)
      | (__g', Dot (Idx k, s'), Decl (__g, Dec (_, V2))) ->
          let _ = checkSub (__g', s', __g) in
          let Dec (_, V1) = I.ctxDec (__g', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then ()
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (__g', V1))
                         ^ "\n  expected: ")
                    Print.expToString (__g', (I.EClo (V2, s')))))
      | (__g', Dot (Exp (__u), s'), Decl (__g, Dec (_, V2))) ->
          let _ = checkSub (__g', s', __g) in
          let _ = typeCheck (__g', (__u, (I.EClo (V2, s')))) in ()
      | (__g', Dot (Idx w, t), Decl (__g, BDec (_, (l, s)))) ->
          let _ = checkSub (__g', t, __g) in
          let BDec (_, (l', s')) = I.ctxDec (__g', w) in
          if l <> l'
          then raise (Error "Incompatible block labels found")
          else
            if Conv.convSub ((I.comp (s, t)), s')
            then ()
            else
              raise
                (Error "Substitution in block declaration not well-typed")
      | (__g', Dot (Block (Inst (I)), t), Decl (__g, BDec (_, (l, s)))) ->
          let _ = checkSub (__g', t, __g) in
          let (__g, __l) = I.constBlock l in
          let _ = checkBlock (__g', I, ((I.comp (s, t)), __l)) in ()
      | (__g', (Dot (_, _) as s), I.Null) ->
          raise
            (Error ((^) ("Long substitution" ^ "\n") subToString (__g', s)))
    let rec checkBlock =
      function
      | (__g, nil, (_, nil)) -> ()
      | (__g, (__u)::I, (t, (Dec (_, __v))::__l)) ->
          (checkExp (__g, (__u, I.id), (__v, t));
           checkBlock (__g, I, ((I.Dot ((I.Exp __u), t)), __l)))
    let rec checkDec =
      function
      | (__g, (Dec (_, __v), s)) -> checkExp (__g, (__v, s), ((I.Uni I.Type), I.id))
      | (__g, (BDec (_, (c, t)), s)) ->
          let (Gsome, piDecs) = I.constBlock c in
          checkSub (__g, (I.comp (t, s)), Gsome)
      | (__g, (NDec, _)) -> ()
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (__g, __d) -> (checkCtx __g; checkDec (__g, (__d, I.id)))
    let rec check (__u, __v) = checkExp (I.Null, (__u, I.id), (__v, I.id))
    let rec infer (__u) = I.EClo (inferExp (I.Null, (__u, I.id)))
    let rec infer' (__g, __u) = I.EClo (inferExp (__g, (__u, I.id)))
    let rec checkConv (__U1, __U2) =
      if Conv.conv ((__U1, I.id), (__U2, I.id))
      then ()
      else
        raise
          (Error
             ((^) (((^) "Terms not equal\n  left: " Print.expToString
                      (I.Null, __U1))
                     ^ "\n  right:")
                Print.expToString (I.Null, __U2)))
    (* for debugging purposes *)
    (* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
    (* some well-formedness conditions are assumed for input expressions *)
    (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)
    (* checkExp (__g, (__u, s1), (V2, s2)) = ()

       Invariant:
       If   __g |- s1 : G1
       and  __g |- s2 : G2    G2 |- V2 : __l
       returns () if there is a V1 s.t.
            G1 |- __u : V1
       and  __g  |- V1 [s1] = V2 [s2] : __l
       otherwise exception Error is raised
    *)
    (* impossible: Kind *)
    (* inferExp (__g, (__u, s)) = (__v', s')

       Invariant:
       If   __g  |- s : G1
       then if G1 |- __u : __v   (__u doesn't contain EVAR's, FVAR's)
            then  __g  |- s' : __g'     __g' |- __v' : __l
            and   __g  |- __v [s] = __v'[s'] : __l
            else exception Error is raised.
     *)
    (* no cases for Redex, EVars and EClo's *)
    (* AK: typecheck a representative -- presumably if one rep checks, they all do *)
    (* inferExp (__g, __Us) = (__v', s')

       Invariant: same as inferExp, argument is not in whnf
    *)
    (* inferSpine (__g, (S, s1), (__v, s2)) = (__v', s')

       Invariant:
       If   __g |- s1 : G1
       and  __g |- s2 : G2  and  G2 |- __v : __l ,   (__v, s2) in whnf
       and  (S,__v  don't contain EVAR's, FVAR's)
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
            then __g |- s' : __g'    and  __g' |- __v' : __l
            and  __g |- V1 [s1]   = __v [s2] : __l
            and  __g |- V1'[s1]   = __v' [s'] : __l
    *)
    (* __g |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : __l
             __g |- __u [s1] : V1 [s2]
             Hence
             __g |- S [s1] : V2 [1. s2 o ^1] [__u [s1], id] > __v' [s']
             which is equal to
             __g |- S [s1] : V2 [__u[s1], s2] > __v' [s']

             Note that __g |- __u[s1] : V1 [s2]
             and hence V2 must be under the substitution    __u[s1]: V1, s2
          *)
    (* __v <> (Pi x:V1. V2, s) *)
    (* inferCon (__g, C) = __v'

       Invariant:
       If    __g |- C : __v
       and  (C  doesn't contain FVars)
       then  __g' |- __v' : __l      (for some level __l)
       and   __g |- __v = __v' : __l
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
    (* __g' |- s' : GSome *)
    (* __g  |- s  : GSome *)
    (* __g' |- t  : __g       (verified below) *)
    (*
      | checkSub (__g', I.Dot (I.Block (I.Bidx _), t), __g) =
        raise Error "Unexpected block index in substitution"
      | checkSub (__g', I.Dot (I.Block (I.LVar _), t), __g) =
        raise Error "Unexpected LVar in substitution after abstraction"
      *)
    (* checkDec (__g, (x:__v, s)) = B

       Invariant:
       If __g |- s : G1
       then B iff __g |- __v[s] : type
    *)
    (* G1 |- t : GSome *)
    (* __g  |- s : G1 *)
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
