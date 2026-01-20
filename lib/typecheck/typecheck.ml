
module type TYPECHECK  =
  sig
    exception Error of string 
    val check : IntSyn.__Exp -> IntSyn.__Exp -> unit
    val checkDec : IntSyn.dctx -> (IntSyn.__Dec * IntSyn.__Sub) -> unit
    val checkConv : IntSyn.__Exp -> IntSyn.__Exp -> unit
    val infer : IntSyn.__Exp -> IntSyn.__Exp
    val infer' : IntSyn.dctx -> IntSyn.__Exp -> IntSyn.__Exp
    val typeCheck : IntSyn.dctx -> (IntSyn.__Exp * IntSyn.__Exp) -> unit
    val typeCheckCtx : IntSyn.dctx -> unit
    val typeCheckSub : IntSyn.dctx -> IntSyn.__Sub -> IntSyn.dctx -> unit
  end;;




module TypeCheck(TypeCheck:sig
                             module Conv : CONV
                             module Whnf : WHNF
                             module Names : NAMES
                             module Print : PRINT
                           end) : TYPECHECK =
  struct
    exception Error of string 
    module I = IntSyn
    let rec subToString __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Dot (Idx n, s)) ->
          (^) ((Int.toString n) ^ ".") subToString (__G, s)
      | (__G, Dot (Exp (__U), s)) ->
          (^) (((^) "(" Print.expToString (__G, __U)) ^ ").") subToString
            (__G, s)
      | (__G, Dot (Block (LVar _ as L), s)) ->
          (^) ((LVarToString (__G, __L)) ^ ".") subToString (__G, s)
      | (__G, Shift n) -> (^) "^" Int.toString n
    let rec LVarToString __2__ __3__ =
      match (__2__, __3__) with
      | (__G, LVar ({ contents = Some (__B) }, sk, (l, t))) ->
          LVarToString (__G, (I.blockSub (__B, sk)))
      | (__G, LVar ({ contents = None }, sk, (cid, t))) ->
          ((^) (((^) "#" I.conDecName (I.sgnLookup cid)) ^ "[") subToString
             (__G, t))
            ^ "]"(* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
    let rec checkExp (__G) (__Us) (__Vs) =
      let __Us' = inferExp (__G, __Us) in
      if Conv.conv (__Us', __Vs) then () else raise (Error "Type mismatch")
    let rec inferUni (I.Type) = I.Kind
    let rec inferExpW __4__ __5__ =
      match (__4__, __5__) with
      | (__G, (Uni (__L), _)) -> ((I.Uni (inferUni __L)), I.id)
      | (__G, (Pi ((__D, _), __V), s)) ->
          (checkDec (__G, (__D, s));
           inferExp ((I.Decl (__G, (I.decSub (__D, s)))), (__V, (I.dot1 s))))
      | (__G, (Root (__C, __S), s)) ->
          inferSpine
            (__G, (__S, s), (Whnf.whnf ((inferCon (__G, __C)), I.id)))
      | (__G, (Lam (__D, __U), s)) ->
          (checkDec (__G, (__D, s));
           ((I.Pi
               (((I.decSub (__D, s)), I.Maybe),
                 (I.EClo
                    (inferExp
                       ((I.Decl (__G, (I.decSub (__D, s)))),
                         (__U, (I.dot1 s))))))), I.id))
      | (__G, (FgnExp csfe, s)) ->
          inferExp (__G, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
      (* no cases for Redex, EVars and EClo's *)
    let rec inferExp (__G) (__Us) = inferExpW (__G, (Whnf.whnf __Us))
    let rec inferSpine __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (__G, (I.Nil, _), __Vs) -> __Vs
      | (__G, (SClo (__S, s'), s), __Vs) ->
          inferSpine (__G, (__S, (I.comp (s', s))), __Vs)
      | (__G, (App (__U, __S), s1), (Pi ((Dec (_, __V1), _), __V2), s2)) ->
          (checkExp (__G, (__U, s1), (__V1, s2));
           inferSpine
             (__G, (__S, s1),
               (Whnf.whnf (__V2, (I.Dot ((I.Exp (I.EClo (__U, s1))), s2))))))
      | (__G, ((App _, _) as Ss), ((Root (Def _, _), _) as Vs)) ->
          inferSpine (__G, __Ss, (Whnf.expandDef __Vs))
      | (__G, (App (__U, __S), _), (__V, s)) ->
          raise (Error "Expression is applied, but not a function")(* V <> (Pi x:V1. V2, s) *)
      (* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             G |- U [s1] : V1 [s2]
             Hence
             G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             G |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that G |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
    let rec inferCon __9__ __10__ =
      match (__9__, __10__) with
      | (__G, BVar k') -> let Dec (_, __V) = I.ctxDec (__G, k') in __V
      | (__G, Proj (__B, i)) ->
          let Dec (_, __V) = I.blockDec (__G, __B, i) in __V
      | (__G, Const c) -> I.constType c
      | (__G, Def d) -> I.constType d
      | (__G, Skonst c) -> I.constType c
      | (__G, FgnConst (cs, conDec)) -> I.conDecType conDec(* no case for FVar *)
      (* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
    let rec typeCheck (__G) (__U, __V) =
      checkCtx __G; checkExp (__G, (__U, I.id), (__V, I.id))
    let rec checkSub __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (__G, __D), Shift k, I.Null) ->
          if k > 0
          then checkSub (__G, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (__G', Shift k, __G) ->
          checkSub (__G', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __G)
      | (__G', Dot (Idx k, s'), Decl (__G, Dec (_, __V2))) ->
          let _ = checkSub (__G', s', __G) in
          let Dec (_, __V1) = I.ctxDec (__G', k) in
          if Conv.conv ((__V1, I.id), (__V2, s'))
          then ()
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (__G', __V1))
                         ^ "\n  expected: ")
                    Print.expToString (__G', (I.EClo (__V2, s')))))
      | (__G', Dot (Exp (__U), s'), Decl (__G, Dec (_, __V2))) ->
          let _ = checkSub (__G', s', __G) in
          let _ = typeCheck (__G', (__U, (I.EClo (__V2, s')))) in ()
      | (__G', Dot (Idx w, t), Decl (__G, BDec (_, (l, s)))) ->
          let _ = checkSub (__G', t, __G) in
          let BDec (_, (l', s')) = I.ctxDec (__G', w) in
          ((if l <> l'
            then raise (Error "Incompatible block labels found")
            else
              if Conv.convSub ((I.comp (s, t)), s')
              then ()
              else
                raise
                  (Error "Substitution in block declaration not well-typed"))
            (* G' |- s' : GSOME *)(* G  |- s  : GSOME *)
            (* G' |- t  : G       (verified below) *))
      | (__G', Dot (Block (Inst (__I)), t), Decl (__G, BDec (_, (l, s)))) ->
          let _ = checkSub (__G', t, __G) in
          let (__G, __L) = I.constBlock l in
          let _ = checkBlock (__G', __I, ((I.comp (s, t)), __L)) in ()
      | (__G', (Dot (_, _) as s), I.Null) ->
          raise
            (Error ((^) ("Long substitution" ^ "\n") subToString (__G', s)))
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      (* Front of the substitution cannot be a I.Bidx or LVar *)
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
    let rec checkBlock __14__ __15__ __16__ =
      match (__14__, __15__, __16__) with
      | (__G, nil, (_, nil)) -> ()
      | (__G, (__U)::__I, (t, (Dec (_, __V))::__L)) ->
          (checkExp (__G, (__U, I.id), (__V, t));
           checkBlock (__G, __I, ((I.Dot ((I.Exp __U), t)), __L)))
    let rec checkDec __17__ __18__ =
      match (__17__, __18__) with
      | (__G, (Dec (_, __V), s)) ->
          checkExp (__G, (__V, s), ((I.Uni I.Type), I.id))
      | (__G, (BDec (_, (c, t)), s)) ->
          let (Gsome, piDecs) = I.constBlock c in
          ((checkSub (__G, (I.comp (t, s)), Gsome))
            (* G1 |- t : GSOME *)(* G  |- s : G1 *))
      | (__G, (NDec, _)) -> ()
    let rec checkCtx =
      function
      | I.Null -> ()
      | Decl (__G, __D) -> (checkCtx __G; checkDec (__G, (__D, I.id)))
    let rec check (__U) (__V) = checkExp (I.Null, (__U, I.id), (__V, I.id))
    let rec infer (__U) = I.EClo (inferExp (I.Null, (__U, I.id)))
    let rec infer' (__G) (__U) = I.EClo (inferExp (__G, (__U, I.id)))
    let rec checkConv (__U1) (__U2) =
      if Conv.conv ((__U1, I.id), (__U2, I.id))
      then ()
      else
        raise
          (Error
             ((^) (((^) "Terms not equal\n  left: " Print.expToString
                      (I.Null, __U1))
                     ^ "\n  right:")
                Print.expToString (I.Null, __U2)))
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
                     module Conv = Conv
                     module Whnf = Whnf
                     module Names = Names
                     module Print = Print
                   end)
module Strict =
  (Make_Strict)(struct module Whnf = Whnf
                       module Paths' = Paths end);;
