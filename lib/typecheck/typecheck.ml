module type TYPECHECK  =
  sig
    exception Error of string 
    val check : (IntSyn.exp_ * IntSyn.exp_) -> unit
    val checkDec : (IntSyn.dctx * (IntSyn.dec_ * IntSyn.sub_)) -> unit
    val checkConv : (IntSyn.exp_ * IntSyn.exp_) -> unit
    val infer : IntSyn.exp_ -> IntSyn.exp_
    val infer' : (IntSyn.dctx * IntSyn.exp_) -> IntSyn.exp_
    val typeCheck : (IntSyn.dctx * (IntSyn.exp_ * IntSyn.exp_)) -> unit
    val typeCheckCtx : IntSyn.dctx -> unit
    val typeCheckSub : (IntSyn.dctx * IntSyn.sub_ * IntSyn.dctx) -> unit
  end


module TypeCheck(TypeCheck:sig
                             module Conv : CONV
                             module Whnf : WHNF
                             module Names : NAMES
                             module Print : PRINT
                           end) : TYPECHECK =
  struct
    exception Error of string 
    module I = IntSyn
    let rec subToString =
      begin function
      | (g_, Dot (Idx n, s)) ->
          (^) ((Int.toString n) ^ ".") subToString (g_, s)
      | (g_, Dot (Exp (u_), s)) ->
          (^) (((^) "(" Print.expToString (g_, u_)) ^ ").") subToString
            (g_, s)
      | (g_, Dot (Block (LVar _ as l_), s)) ->
          (^) ((LVarToString (g_, l_)) ^ ".") subToString (g_, s)
      | (g_, Shift n) -> (^) "^" Int.toString n end
    let rec LVarToString =
      begin function
      | (g_, LVar ({ contents = Some (b_) }, sk, (l, t))) ->
          LVarToString (g_, (I.blockSub (b_, sk)))
      | (g_, LVar ({ contents = None }, sk, (cid, t))) ->
          ((^) (((^) "#" I.conDecName (I.sgnLookup cid)) ^ "[") subToString
             (g_, t))
            ^ "]" end(* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
  let rec checkExp (g_, us_, vs_) =
    let us'_ = inferExp (g_, us_) in
    if Conv.conv (us'_, vs_) then begin () end
      else begin raise (Error "Type mismatch") end
let rec inferUni (I.Type) = I.Kind
let rec inferExpW =
  begin function
  | (g_, (Uni (l_), _)) -> ((I.Uni (inferUni l_)), I.id)
  | (g_, (Pi ((d_, _), v_), s)) ->
      (begin checkDec (g_, (d_, s));
       inferExp ((I.Decl (g_, (I.decSub (d_, s)))), (v_, (I.dot1 s))) end)
  | (g_, (Root (c_, s_), s)) ->
      inferSpine (g_, (s_, s), (Whnf.whnf ((inferCon (g_, c_)), I.id)))
  | (g_, (Lam (d_, u_), s)) ->
      (begin checkDec (g_, (d_, s));
       ((I.Pi
           (((I.decSub (d_, s)), I.Maybe),
             (I.EClo
                (inferExp
                   ((I.Decl (g_, (I.decSub (d_, s)))), (u_, (I.dot1 s))))))),
         I.id) end)
  | (g_, (FgnExp csfe, s)) ->
      inferExp (g_, ((I.FgnExpStd.ToInternal.apply csfe ()), s)) end(* no cases for Redex, EVars and EClo's *)
let rec inferExp (g_, us_) = inferExpW (g_, (Whnf.whnf us_))
let rec inferSpine =
  begin function
  | (g_, (I.Nil, _), vs_) -> vs_
  | (g_, (SClo (s_, s'), s), vs_) ->
      inferSpine (g_, (s_, (I.comp (s', s))), vs_)
  | (g_, (App (u_, s_), s1), (Pi ((Dec (_, v1_), _), v2_), s2)) ->
      (begin checkExp (g_, (u_, s1), (v1_, s2));
       inferSpine
         (g_, (s_, s1),
           (Whnf.whnf (v2_, (I.Dot ((I.Exp (I.EClo (u_, s1))), s2))))) end)
  | (g_, ((App _, _) as ss_), ((Root (Def _, _), _) as vs_)) ->
      inferSpine (g_, ss_, (Whnf.expandDef vs_))
  | (g_, (App (u_, s_), _), (v_, s)) ->
      raise (Error "Expression is applied, but not a function") end(* V <> (Pi x:V1. V2, s) *)
(* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             G |- U [s1] : V1 [s2]
             Hence
             G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             G |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that G |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
let rec inferCon =
  begin function
  | (g_, BVar k') -> let Dec (_, v_) = I.ctxDec (g_, k') in v_
  | (g_, Proj (b_, i)) -> let Dec (_, v_) = I.blockDec (g_, b_, i) in v_
  | (g_, Const c) -> I.constType c
  | (g_, Def d) -> I.constType d
  | (g_, Skonst c) -> I.constType c
  | (g_, FgnConst (cs, conDec)) -> I.conDecType conDec end(* no case for FVar *)
(* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
let rec typeCheck (g_, (u_, v_)) =
  begin checkCtx g_; checkExp (g_, (u_, I.id), (v_, I.id)) end
let rec checkSub =
  begin function
  | (I.Null, Shift 0, I.Null) -> ()
  | (Decl (g_, d_), Shift k, I.Null) ->
      if k > 0 then begin checkSub (g_, (I.Shift (k - 1)), I.Null) end
      else begin raise (Error "Substitution not well-typed") end
  | (g'_, Shift k, g_) ->
      checkSub (g'_, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), g_)
  | (g'_, Dot (Idx k, s'), Decl (g_, Dec (_, v2_))) ->
      let _ = checkSub (g'_, s', g_) in
      let Dec (_, v1_) = I.ctxDec (g'_, k) in
      if Conv.conv ((v1_, I.id), (v2_, s')) then begin () end
        else begin
          raise
            (Error
               ((^) (((^) "Substitution not well-typed \n  found: "
                        Print.expToString (g'_, v1_))
                       ^ "\n  expected: ")
                  Print.expToString (g'_, (I.EClo (v2_, s'))))) end
| (g'_, Dot (Exp (u_), s'), Decl (g_, Dec (_, v2_))) ->
    let _ = checkSub (g'_, s', g_) in
    let _ = typeCheck (g'_, (u_, (I.EClo (v2_, s')))) in ()
| (g'_, Dot (Idx w, t), Decl (g_, BDec (_, (l, s)))) ->
    let _ = checkSub (g'_, t, g_) in
    let BDec (_, (l', s')) = I.ctxDec (g'_, w) in
    ((if l <> l'
      then begin raise (Error "Incompatible block labels found") end
      else begin if Conv.convSub ((I.comp (s, t)), s') then begin () end
        else begin
          raise (Error "Substitution in block declaration not well-typed") end end)
(* G' |- s' : GSOME *)(* G  |- s  : GSOME *)(* G' |- t  : G       (verified below) *))
| (g'_, Dot (Block (Inst (i_)), t), Decl (g_, BDec (_, (l, s)))) ->
    let _ = checkSub (g'_, t, g_) in
    let (g_, l_) = I.constBlock l in
    let _ = checkBlock (g'_, i_, ((I.comp (s, t)), l_)) in ()
| (g'_, (Dot (_, _) as s), I.Null) ->
    raise (Error ((^) ("Long substitution" ^ "\n") subToString (g'_, s))) end
(* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
(* Front of the substitution cannot be a I.Bidx or LVar *)
(* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
(* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
let rec checkBlock =
  begin function
  | (g_, [], (_, [])) -> ()
  | (g_, (u_)::i_, (t, (Dec (_, v_))::l_)) ->
      (begin checkExp (g_, (u_, I.id), (v_, t));
       checkBlock (g_, i_, ((I.Dot ((I.Exp u_), t)), l_)) end) end
let rec checkDec =
  begin function
  | (g_, (Dec (_, v_), s)) -> checkExp (g_, (v_, s), ((I.Uni I.Type), I.id))
  | (g_, (BDec (_, (c, t)), s)) ->
      let (Gsome, piDecs) = I.constBlock c in
      ((checkSub (g_, (I.comp (t, s)), Gsome))
        (* G1 |- t : GSOME *)(* G  |- s : G1 *))
  | (g_, (NDec, _)) -> () end
let rec checkCtx =
  begin function
  | I.Null -> ()
  | Decl (g_, d_) -> (begin checkCtx g_; checkDec (g_, (d_, I.id)) end) end
let rec check (u_, v_) = checkExp (I.Null, (u_, I.id), (v_, I.id))
let rec infer (u_) = I.EClo (inferExp (I.Null, (u_, I.id)))
let rec infer' (g_, u_) = I.EClo (inferExp (g_, (u_, I.id)))
let rec checkConv (u1_, u2_) =
  if Conv.conv ((u1_, I.id), (u2_, I.id)) then begin () end
  else begin
    raise
      (Error
         ((^) (((^) "Terms not equal\n  left: " Print.expToString
                  (I.Null, u1_))
                 ^ "\n  right:")
            Print.expToString (I.Null, u2_))) end
let check = check
let checkDec = checkDec
let checkConv = checkConv
let infer = infer
let infer' = infer'
let typeCheck = typeCheck
let typeCheckCtx = checkCtx
let typeCheckSub = checkSub end



module TypeCheck =
  (TypeCheck)(struct
                     module Conv = Conv
                     module Whnf = Whnf
                     module Names = Names
                     module Print = Print
                   end)
module Strict =
  (Strict)(struct module Whnf = Whnf
                       module Paths' = Paths end)