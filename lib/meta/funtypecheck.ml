module type FUNTYPECHECK  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val isFor : (IntSyn.dctx * FunSyn.for_) -> unit
    val check : (FunSyn.pro_ * FunSyn.for_) -> unit
    val checkSub : (FunSyn.lfctx * IntSyn.sub_ * FunSyn.lfctx) -> unit
    val isState : StateSyn.state_ -> unit
  end


module FunTypeCheck(FunTypeCheck:sig
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module TypeCheck : TYPECHECK
                                   module Conv : CONV
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Subordinate : SUBORDINATE
                                   module Weaken : WEAKEN
                                   module FunPrint : FUNPRINT
                                 end) : FUNTYPECHECK =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    let rec conv (gs_, gs'_) =
      let exception Conv  in
        let rec conv =
          begin function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (g_, Dec (_, v_)), s), (Decl (g'_, Dec (_, v'_)), s')) ->
              let (s1, s1') = conv ((g_, s), (g'_, s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((v_, s1), (v'_, s1')) then begin ps end
                else begin raise Conv end
          | _ -> raise Conv end in
    begin try begin conv (gs_, gs'_); true end with | Conv -> false end
let rec extend =
  begin function
  | (g_, []) -> g_
  | (g_, (d_)::l_) -> extend ((I.Decl (g_, d_)), l_) end
let rec validBlock (Psi, k, (l, g_)) =
  let rec skipBlock =
    begin function
    | (I.Null, k) -> k
    | (Decl (g'_, _), k) -> skipBlock (g'_, (k - 1)) end in
let rec validBlock' =
  begin function
  | (Decl (Psi, Block (CtxBlock (l', g'_))), 0) ->
      if (l' = l) && (conv ((g_, I.id), (g'_, I.id))) then begin () end
      else begin raise (Error "Typecheck Error: Not a valid block") end
  | (Decl (Psi, Prim _), 0) ->
      raise (Error "Typecheck Error: Not a valid block")
  | (I.Null, k) -> raise (Error "Typecheck Error: Not a valid block")
  | (Decl (Psi, Block (CtxBlock (l', g'_))), k) ->
      validBlock' (Psi, (skipBlock (g'_, k)))
  | (Decl (Psi, Prim (d_)), k) -> validBlock' (Psi, (k - 1)) end in
validBlock' (Psi, k)
let rec raiseSub (g_, Psi') =
  let n = I.ctxLength g_ in
  let m = I.ctxLength Psi' in
  let rec args =
    begin function
    | (0, a, s_) -> s_
    | (n', a, s_) ->
        let Dec (_, v_) = I.ctxDec (g_, n') in
        if Subordinate.belowEq ((I.targetFam v_), a)
        then
          begin args
                  ((n' - 1), a, (I.App ((I.Root ((I.BVar n'), I.Nil)), s_))) end
          else begin args ((n' - 1), a, s_) end end in
let rec term m' =
  let Dec (_, v_) = I.ctxDec (Psi', m') in
  I.Exp (I.Root ((I.BVar (n + m')), (args (n, (I.targetFam v_), I.Nil)))) in
let rec raiseSub'' =
  begin function
  | (0, s) -> s
  | (m', s) -> raiseSub'' ((m' - 1), (I.Dot ((term m'), s))) end in
let rec raiseSub' =
  begin function
  | (0, s) -> raiseSub'' (m, s)
  | (n', s) -> raiseSub' ((n' - 1), (I.Dot ((I.Idx n'), s))) end in
raiseSub' (n, (I.Shift (n + m)))
let rec raiseType (CtxBlock (l, g_), Psi') =
  let rec raiseType'' =
    begin function
    | (I.Null, Vn, a) -> Vn
    | (Decl (g'_, (Dec (_, v'_) as d_)), Vn, a) ->
        if Subordinate.belowEq ((I.targetFam v'_), a)
        then
          begin raiseType'' (g'_, (Abstract.piDepend ((d_, I.Maybe), Vn)), a) end
        else begin raiseType'' (g'_, (Weaken.strengthenExp (Vn, I.shift)), a) end end in
let rec raiseType' =
begin function
| (Psi1, []) -> []
| (Psi1, (Prim (Dec (x, v_) as d_))::Psi1') ->
    let s = raiseSub (g_, Psi1) in
    let Vn = Whnf.normalize (v_, s) in
    let a = I.targetFam Vn in
    let d'_ = I.Dec (x, (raiseType'' (g_, Vn, a))) in
    (F.Prim d'_) :: (raiseType' ((I.Decl (Psi1, d_)), Psi1')) end in
((raiseType' (I.Null, Psi'))
(* no case of F.Block by invariant *))
let rec raiseM =
  begin function
  | (b_, []) -> []
  | (b_, (MDec (xx, f_))::l_) ->
      (::) (F.MDec (xx, (F.All ((F.Block b_), f_)))) raiseM (b_, l_) end
let rec psub =
  begin function
  | (k, I.Null, s) -> s
  | (k, Decl (g_, _), s) -> psub ((k - 1), g_, (I.Dot ((I.Idx k), s))) end
let rec deltaSub =
  begin function
  | (I.Null, s) -> I.Null
  | (Decl (Delta, DD), s) ->
      I.Decl ((deltaSub (Delta, s)), (F.mdecSub (DD, s))) end
let rec shift (Delta) = deltaSub (Delta, I.shift)
let rec shifts =
  begin function
  | (I.Null, Delta) -> Delta
  | (Decl (g_, _), Delta) -> shifts (g_, (shift Delta)) end
let rec shiftBlock (CtxBlock (_, g_), Delta) = shifts (g_, Delta)
let rec shiftSub =
  begin function
  | (I.Null, s) -> s
  | (Decl (g_, _), s) -> shiftSub (g_, (I.comp (I.shift, s))) end
let rec shiftSubBlock (CtxBlock (_, g_), s) = shiftSub (g_, s)
let rec check =
  begin function
  | (Psi, Delta, F.Unit, (F.True, _)) -> ()
  | (Psi, Delta, Rec (DD, p_), f_) ->
      check (Psi, (I.Decl (Delta, DD)), p_, f_)
  | (Psi, Delta, Lam ((Prim (Dec (_, v_)) as LD), p_),
     (All (Prim (Dec (_, v'_)), f'_), s')) ->
      if Conv.conv ((v_, I.id), (v'_, s'))
      then
        begin check
                ((I.Decl (Psi, LD)), (shift Delta), p_, (f'_, (I.dot1 s'))) end
      else begin raise (Error "Typecheck Error: Primitive Abstraction") end
  | (Psi, Delta, Lam ((Block (CtxBlock (l, g_) as b_) as LD), p_),
     (All (Block (CtxBlock (l', g'_)), f'_), s')) ->
      if (l = l') && (conv ((g_, I.id), (g'_, s')))
      then
        begin check
                ((I.Decl (Psi, LD)), (shiftBlock (b_, Delta)), p_,
                  (f'_, (F.dot1n (g_, s')))) end
      else begin raise (Error "Typecheck Error: Block Abstraction") end
| (Psi, Delta, Inx (m_, p_), (Ex (Dec (_, v'_), f'_), s')) ->
    (begin TypeCheck.typeCheck ((F.makectx Psi), (m_, (I.EClo (v'_, s'))));
     check (Psi, Delta, p_, (f'_, (I.Dot ((I.Exp m_), s')))) end)
| (Psi, Delta, Case (Opts (o_)), (f'_, s')) ->
    checkOpts (Psi, Delta, o_, (f'_, s'))
| (Psi, Delta, Pair (p1_, p2_), (And (F1', F2'), s')) ->
    (begin check (Psi, Delta, p1_, (F1', s'));
     check (Psi, Delta, p2_, (F2', s')) end)
| (Psi, Delta, Let (ds_, p_), (f'_, s')) ->
    let (Psi', Delta', s'') = assume (Psi, Delta, ds_) in
    check
      ((extend (Psi, Psi')), (extend (Delta, Delta')), p_,
        (f'_, (I.comp (s', s''))))
| _ -> raise (Error "Typecheck Error: Term not well-typed") end
let rec infer (Delta, kk) = ((I.ctxLookup (Delta, kk)), I.id)
let rec assume =
  begin function
  | (Psi, Delta, F.Empty) -> ([], [], I.id)
  | (Psi, Delta, Split (kk, ds_)) ->
      (begin match infer (Delta, kk) with
       | (MDec (name, Ex (d_, f_)), s) ->
           let LD = F.Prim (I.decSub (d_, s)) in
           let DD = F.MDec (name, (F.forSub (f_, (I.dot1 s)))) in
           let (Psi', Delta', s') =
             assume ((I.Decl (Psi, LD)), (I.Decl ((shift Delta), DD)), ds_) in
           ((LD :: Psi'), ((F.mdecSub (DD, s')) :: Delta'),
             (I.comp (I.shift, s')))
       | _ -> raise (Error "Typecheck Error: Declaration") end)
  | (Psi, Delta, New (b_, ds_)) ->
      let _ =
        TypeCheck.typeCheck
          ((F.makectx (I.Decl (Psi, (F.Block b_)))),
            ((I.Uni I.Type), (I.Uni I.Kind))) in
      let (Psi', Delta', s') =
        assume ((I.Decl (Psi, (F.Block b_))), (shiftBlock (b_, Delta)), ds_) in
      ((((raiseType (b_, Psi')), (raiseM (b_, Delta')), s'))
        (* check B valid context block       <-------------- omission *))
  | (Psi, Delta, App ((kk, u_), ds_)) ->
      (begin match infer (Delta, kk) with
       | (MDec (name, All (Prim (Dec (_, v_)), f_)), s) ->
           let _ =
             begin try
                     TypeCheck.typeCheck
                       ((F.makectx Psi), (u_, (I.EClo (v_, s))))
             with
             | Error msg ->
                 raise
                   (Error
                      ((^) (((^) (((^) (msg ^ " ") Print.expToString
                                     ((F.makectx Psi), u_))
                                    ^ " has type ")
                               Print.expToString
                               ((F.makectx Psi),
                                 (TypeCheck.infer' ((F.makectx Psi), u_))))
                              ^ " expected ")
                         Print.expToString
                         ((F.makectx Psi), (I.EClo (v_, s))))) end in
         let DD = F.MDec (name, (F.forSub (f_, (I.Dot ((I.Exp u_), s))))) in
         let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), ds_) in
         (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
      | (MDec (name, f_), s) ->
          raise
            (Error
               ("Typecheck Error: Declaration App" ^
                  (FunPrint.forToString (I.Null, f_) ["x"]))) end)
| (Psi, Delta, PApp ((kk, k), ds_)) ->
    (begin match infer (Delta, kk) with
     | (MDec (name, All (Block (CtxBlock (l, g_)), f_)), s) ->
         let _ = validBlock (Psi, k, (l, g_)) in
         let DD = F.MDec (name, (F.forSub (f_, (psub (k, g_, s))))) in
         let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), ds_) in
         (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
     | _ -> raise (Error "Typecheck Error: Declaration PApp") end)
| (Psi, Delta, Left (kk, ds_)) ->
    (begin match infer (Delta, kk) with
     | (MDec (name, And (f1_, f2_)), s) ->
         let DD = F.MDec (name, (F.forSub (f1_, s))) in
         let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), ds_) in
         (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
     | _ -> raise (Error "Typecheck Error: Declaration Left") end)
| (Psi, Delta, Right (kk, ds_)) ->
    (begin match infer (Delta, kk) with
     | (MDec (name, And (f1_, f2_)), s) ->
         let DD = F.MDec (name, (F.forSub (f2_, s))) in
         let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), ds_) in
         (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
     | _ -> raise (Error "Typecheck Error: Declaration Left") end)
| (Psi, Delta, Lemma (cc, ds_)) ->
    let LemmaDec (names, _, f_) = F.lemmaLookup cc in
    let name = foldr (^) "" names in
    let DD = F.MDec ((Some name), f_) in
    let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), ds_) in
    (Psi', ((F.mdecSub (DD, s')) :: Delta'), s') end
let rec checkSub =
  begin function
  | (I.Null, Shift 0, I.Null) -> ()
  | (Decl (Psi, Prim (d_)), Shift k, I.Null) ->
      if k > 0 then begin checkSub (Psi, (I.Shift (k - 1)), I.Null) end
      else begin raise (Error "Substitution not well-typed") end
  | (Decl (Psi, Block (CtxBlock (_, g_))), Shift k, I.Null) ->
      let g = I.ctxLength g_ in
      if k >= g then begin checkSub (Psi, (I.Shift (k - g)), I.Null) end
        else begin raise (Error "Substitution not well-typed") end
| (Psi', Shift k, Psi) ->
    checkSub (Psi', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), Psi)
| (Psi', Dot (Idx k, s'), Decl (Psi, Prim (Dec (_, v2_)))) ->
    let g'_ = F.makectx Psi' in
    let Dec (_, v1_) = I.ctxDec (g'_, k) in
    if Conv.conv ((v1_, I.id), (v2_, s'))
    then begin checkSub (Psi', s', Psi) end
      else begin
        raise
          (Error
             ((^) (((^) "Substitution not well-typed \n  found: "
                      Print.expToString (g'_, v1_))
                     ^ "\n  expected: ")
                Print.expToString (g'_, (I.EClo (v2_, s'))))) end
| (Psi', Dot (Exp (u_), s'), Decl (Psi, Prim (Dec (_, v2_)))) ->
    let g'_ = F.makectx Psi' in
    let _ = TypeCheck.typeCheck (g'_, (u_, (I.EClo (v2_, s')))) in
    checkSub (Psi', s', Psi)
| (Psi', (Dot (Idx k, _) as s), Decl (Psi, Block (CtxBlock (l1, g_)))) ->
    let (Block (CtxBlock (l2, g'_)), w) = F.lfctxLFDec (Psi', k) in
    let rec checkSub' =
      begin function
      | ((I.Null, w1), s1, I.Null, _) -> s1
      | ((Decl (g'_, Dec (_, v'_)), w1), Dot (Idx k', s1), Decl
         (g_, Dec (_, v_)), m) ->
          if k' = m
          then
            begin (if Conv.conv ((v'_, w1), (v_, s1))
                   then
                     begin checkSub'
                             ((g'_, (I.comp (w1, I.shift))), s1, g_, (m + 1)) end
            else begin raise (Error "ContextBlock assignment not well-typed") end) end
      else begin raise (Error "ContextBlock assignment out of order") end end in
((checkSub (Psi', (checkSub' ((g'_, w), s, g_, k)), Psi))
(* check that l1 = l2     <----------------------- omission *)(* checkSub' ((G', w), s, G, m) = ()
          *)) end
let rec checkOpts =
  begin function
  | (Psi, Delta, [], _) -> ()
  | (Psi, Delta, (Psi', t, p_)::o_, (f'_, s')) ->
      (((begin checkSub (Psi', t, Psi);
         check (Psi', (deltaSub (Delta, t)), p_, (f'_, (I.comp (s', t))));
         checkOpts (Psi, Delta, o_, (f'_, s')) end))
  (* [Psi' strict in  t] <------------------------- omission*)) end
let rec checkRec (p_, t_) = check (I.Null, I.Null, p_, (t_, I.id))
let rec isFor =
  begin function
  | (g_, All (Prim (d_), f_)) ->
      (begin try
               begin TypeCheck.checkDec (g_, (d_, I.id));
               isFor ((I.Decl (g_, d_)), f_) end
      with | Error msg -> raise (Error msg) end)
  | (g_, All (Block (CtxBlock (_, g1_)), f_)) ->
      isForBlock (g_, (F.ctxToList g1_), f_)
  | (g_, Ex (d_, f_)) ->
      (begin try
               begin TypeCheck.checkDec (g_, (d_, I.id));
               isFor ((I.Decl (g_, d_)), f_) end
      with | Error msg -> raise (Error msg) end) | (g_, F.True) -> ()
| (g_, And (f1_, f2_)) -> (begin isFor (g_, f1_); isFor (g_, f2_) end) end
let rec isForBlock =
  begin function
  | (g_, [], f_) -> isFor (g_, f_)
  | (g_, (d_)::g1_, f_) -> isForBlock ((I.Decl (g_, d_)), g1_, f_) end
let rec checkTags' =
  begin function
  | (v_, Ex _) -> ()
  | (Pi (_, v_), All (_, f_)) -> checkTags' (v_, f_)
  | _ -> raise Domain end
let rec checkTags =
  begin function
  | (I.Null, I.Null) -> ()
  | (Decl (g_, Dec (_, v_)), Decl (b_, t_)) ->
      (begin checkTags (g_, b_);
       (begin match t_ with | Lemma _ -> () | _ -> () end) end) end
let rec isState (State (n, (g_, b_), (IH, OH), d, o_, h_, f_)) =
  ((begin TypeCheck.typeCheckCtx g_;
    checkTags (g_, b_);
    if not (Abstract.closedCtx g_)
    then begin raise (Error "State context not closed!") end
    else begin () end;
  map
    (begin function
     | (n', f'_) -> ((isFor (g_, f'_))
         (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *)) end)
  h_; isFor (g_, f_) end)
(* n' is not checked for consistency   --cs *))
let isFor = isFor
let check = checkRec
let checkSub = checkSub
let isState = isState end
