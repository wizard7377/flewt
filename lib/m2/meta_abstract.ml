module type METAABSTRACT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val abstract : MetaSyn.state_ -> MetaSyn.state_
  end


module MetaAbstract(MetaAbstract:sig
                                   module Global : GLOBAL
                                   module MetaSyn' : METASYN
                                   module MetaGlobal : METAGLOBAL
                                   module Abstract : ABSTRACT
                                   module ModeTable : MODETABLE
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Constraints : CONSTRAINTS
                                   module Unify : UNIFY
                                   module Names : NAMES
                                   module TypeCheck : TYPECHECK
                                   module Subordinate : SUBORDINATE
                                 end) : METAABSTRACT =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module I = IntSyn
    module S = Stream
    module M = MetaSyn
    module C = Constraints
    type var_ =
      | EV of
      (((I.exp_ option ref * I.exp_ * MetaSyn.mode_))(* Var ::= EVar <r_, V, St>       *))
      
      | BV 
    let rec checkEmpty =
      begin function
      | [] -> ()
      | Cnstr ->
          (begin match C.simplify Cnstr with
           | [] -> ()
           | _ -> raise (Error "Unresolved constraints") end) end
  let rec typecheck (Prefix (g_, m_, b_), v_) =
    TypeCheck.typeCheck (g_, (v_, (I.Uni I.Type)))
  let rec modeEq =
    begin function
    | (Marg (ModeSyn.Plus, _), M.Top) -> true
    | (Marg (ModeSyn.Minus, _), M.Bot) -> true
    | _ -> false end
let rec atxLookup =
  begin function
  | (I.Null, _) -> None
  | (Decl (m_, BV), r) -> atxLookup (m_, r)
  | (Decl (m_, (EV (r', _, _) as e_)), r) -> if r = r' then begin Some e_ end
      else begin atxLookup (m_, r) end end
let rec raiseType =
  begin function
  | (0, g_, v_) -> v_
  | (depth, Decl (g_, d_), v_) ->
      raiseType ((depth - 1), g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec weaken =
  begin function
  | (0, g_, a) -> I.id
  | (depth, Decl (g'_, (Dec (name, v_) as d_)), a) ->
      let w' = weaken ((depth - 1), g'_, a) in
      if Subordinate.belowEq ((I.targetFam v_), a) then begin I.dot1 w' end
        else begin I.comp (w', I.shift) end end
let rec countPi (v_) =
  let rec countPi' =
    begin function
    | (Root _, n) -> n
    | (Pi (_, v_), n) -> countPi' (v_, (n + 1))
    | (EClo (v_, _), n) -> countPi' (v_, n) end in
countPi' (v_, 0)
let rec collectExp (lG0, g_, us_, mode, Adepth) =
  collectExpW (lG0, g_, (Whnf.whnf us_), mode, Adepth)
let rec collectExpW =
  begin function
  | (lG0, g_, (Uni _, s), mode, Adepth) -> Adepth
  | (lG0, g_, (Pi ((d_, _), v_), s), mode, Adepth) ->
      collectExp
        (lG0, (I.Decl (g_, (I.decSub (d_, s)))), (v_, (I.dot1 s)), mode,
          (collectDec (lG0, g_, (d_, s), mode, Adepth)))
  | (lG0, g_, (Lam (d_, u_), s), mode, Adepth) ->
      collectExp
        (lG0, (I.Decl (g_, (I.decSub (d_, s)))), (u_, (I.dot1 s)), mode,
          (collectDec (lG0, g_, (d_, s), mode, Adepth)))
  | (lG0, g_, ((Root (BVar k, s_), s) as us_), mode, ((a_, depth) as Adepth))
      ->
      let l = I.ctxLength g_ in
      if (((k = l) + depth) - lG0) && (depth > 0)
      then
        begin let Dec (_, v_) = I.ctxDec (g_, k) in
              ((collectSpine
                  (lG0, g_, (s_, s), mode, ((I.Decl (a_, BV)), (depth - 1))))
                (* invariant: all variables (EV or BV) in V already seen! *)) end
        else begin collectSpine (lG0, g_, (s_, s), mode, Adepth) end
  | (lG0, g_, (Root (c_, s_), s), mode, Adepth) ->
      collectSpine (lG0, g_, (s_, s), mode, Adepth)
  | (lG0, g_, (EVar (r, GX, v_, cnstrs), s), mode, ((a_, depth) as Adepth))
      ->
      (begin match atxLookup (a_, r) with
       | None ->
           let _ = checkEmpty !cnstrs in
           let lGp' = ((I.ctxLength GX) - lG0) + depth in
           let w = weaken (lGp', GX, (I.targetFam v_)) in
           let iw = Whnf.invert w in
           let GX' = Whnf.strengthen (iw, GX) in
           let lGp'' = ((I.ctxLength GX') - lG0) + depth in
           let Vraised = raiseType (lGp'', GX', (I.EClo (v_, iw))) in
           let EVar (r', _, _, _) as x'_ = I.newEVar (GX', (I.EClo (v_, iw))) in
           let _ = Unify.instantiateEVar (r, (I.EClo (x'_, w)), []) in
           ((collectSub
               (lG0, g_, lGp'', s, mode,
                 ((I.Decl (a_, (EV (r', Vraised, mode)))), depth)))
             (* lGp' >= 0 *)(* lGp'' >= 0 *)(* invariant: all variables (EV) in Vraised already seen *))
       | Some (EV (_, v_, _)) ->
           let lGp' = countPi v_ in
           collectSub (lG0, g_, lGp', s, mode, Adepth) end)
| (lGO, g_, (FgnExp csfe, s), mode, Adepth) ->
    I.FgnExpStd.fold csfe
      (begin function
       | (u_, Adepth') -> collectExp (lGO, g_, (u_, s), mode, Adepth') end)
    Adepth end(* s = id *)(* impossible? *)
let rec collectSub =
  begin function
  | (_, _, 0, _, _, Adepth) -> Adepth
  | (lG0, g_, lG', Shift k, mode, Adepth) ->
      collectSub
        (lG0, g_, lG', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), mode,
          Adepth)
  | (lG0, g_, lG', Dot (Idx k, s), mode, ((a_, depth) as Adepth)) ->
      collectSub (lG0, g_, (lG' - 1), s, mode, Adepth)
  | (lG0, g_, lG', Dot (Exp (u_), s), mode, Adepth) ->
      collectSub
        (lG0, g_, (lG' - 1), s, mode,
          (collectExp (lG0, g_, (u_, I.id), mode, Adepth))) end(* typing invariant guarantees that (EV, BV) in V already
             collected !! *)
(* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *)
(* eta expansion *)
let rec collectSpine =
  begin function
  | (lG0, g_, (I.Nil, _), mode, Adepth) -> Adepth
  | (lG0, g_, (SClo (s_, s'), s), mode, Adepth) ->
      collectSpine (lG0, g_, (s_, (I.comp (s', s))), mode, Adepth)
  | (lG0, g_, (App (u_, s_), s), mode, Adepth) ->
      collectSpine
        (lG0, g_, (s_, s), mode,
          (collectExp (lG0, g_, (u_, s), mode, Adepth))) end
let rec collectDec (lG0, g_, (Dec (x, v_), s), mode, Adepth) =
  collectExp (lG0, g_, (v_, s), mode, Adepth)
let rec collectModeW =
  begin function
  | (lG0, g_, modeIn, modeRec, (Root (Const cid, s_), s), Adepth) ->
      let rec collectModeW' =
        begin function
        | (((I.Nil, _), ModeSyn.Mnil), Adepth) -> Adepth
        | (((SClo (s_, s'), s), m_), Adepth) ->
            collectModeW' (((s_, (I.comp (s', s))), m_), Adepth)
        | (((App (u_, s_), s), Mapp (m, mS)), Adepth) ->
            collectModeW'
              (((s_, s), mS),
                (if modeEq (m, modeIn)
                 then begin collectExp (lG0, g_, (u_, s), modeRec, Adepth) end
                else begin Adepth end)) end in
let mS = valOf (ModeTable.modeLookup cid) in
collectModeW' (((s_, s), mS), Adepth)
| (lG0, g_, modeIn, modeRec, (Pi ((d_, p_), v_), s), Adepth) ->
    raise
      (Error
         "Implementation restricted to the Horn fragment of the meta logic") end
(* s = id *)
let rec collectG (lG0, g_, vs_, Adepth) =
  collectGW (lG0, g_, (Whnf.whnf vs_), Adepth)
let rec collectGW (lG0, g_, vs_, Adepth) =
  collectModeW
    (lG0, g_, M.Bot, M.Top, vs_,
      (collectModeW (lG0, g_, M.Top, M.Bot, vs_, Adepth)))
let rec collectDTop (lG0, g_, vs_, Adepth) =
  collectDTopW (lG0, g_, (Whnf.whnf vs_), Adepth)
let rec collectDTopW =
  begin function
  | (lG0, g_, (Pi (((Dec (x, v1_) as d_), I.No), v2_), s), Adepth) ->
      collectG
        (lG0, g_, (v1_, s),
          (collectDTop
             (lG0, (I.Decl (g_, (I.decSub (d_, s)))), (v2_, (I.dot1 s)),
               Adepth)))
  | (lG0, g_, ((Root _, s) as vs_), Adepth) ->
      collectModeW (lG0, g_, M.Top, M.Top, vs_, Adepth) end(* s = id *)
(* only arrows *)
let rec collectDBot (lG0, g_, vs_, Adepth) =
  collectDBotW (lG0, g_, (Whnf.whnf vs_), Adepth)
let rec collectDBotW =
  begin function
  | (lG0, g_, (Pi ((d_, _), v_), s), Adepth) ->
      collectDBot
        (lG0, (I.Decl (g_, (I.decSub (d_, s)))), (v_, (I.dot1 s)), Adepth)
  | (lG0, g_, ((Root _, s) as vs_), Adepth) ->
      collectModeW (lG0, g_, M.Bot, M.Bot, vs_, Adepth) end(* s = id *)
let rec collect (Prefix (g_, m_, b_), v_) =
  let lG0 = I.ctxLength g_ in
  let (a_, k) =
    collectDBot
      (lG0, g_, (v_, I.id),
        (collectDTop (lG0, g_, (v_, I.id), (I.Null, lG0)))) in
  a_
let rec lookupEV (a_, r) =
  let rec lookupEV' =
    begin function
    | (Decl (a_, EV (r, v_, _)), r', k) -> if r = r' then begin (k, v_) end
        else begin lookupEV' (a_, r', (k + 1)) end
    | (Decl (a_, BV), r', k) -> lookupEV' (a_, r', (k + 1)) end in
((lookupEV' (a_, r, 1))
(* lookupEV' I.Null cannot occur by invariant *))
let rec lookupBV (a_, i) =
  let rec lookupBV' =
    begin function
    | (Decl (a_, EV (r, v_, _)), i, k) -> lookupBV' (a_, i, (k + 1))
    | (Decl (a_, BV), 1, k) -> k
    | (Decl (a_, BV), i, k) -> lookupBV' (a_, (i - 1), (k + 1)) end in
((lookupBV' (a_, i, 1))
  (* lookupBV' I.Null cannot occur by invariant *))
let rec abstractExpW =
  begin function
  | (a_, g_, depth, ((Uni (l_) as v_), s)) -> v_
  | (a_, g_, depth, (Pi ((d_, p_), v_), s)) ->
      Abstract.piDepend
        (((abstractDec (a_, g_, depth, (d_, s))), p_),
          (abstractExp
             (a_, (I.Decl (g_, (I.decSub (d_, s)))), (depth + 1),
               (v_, (I.dot1 s)))))
  | (a_, g_, depth, (Lam (d_, u_), s)) ->
      I.Lam
        ((abstractDec (a_, g_, depth, (d_, s))),
          (abstractExp
             (a_, (I.Decl (g_, (I.decSub (d_, s)))), (depth + 1),
               (u_, (I.dot1 s)))))
  | (a_, g_, depth, (Root ((BVar k as c_), s_), s)) ->
      if k > depth
      then
        begin let k' = lookupBV (a_, (k - depth)) in
              I.Root
                ((I.BVar (k' + depth)),
                  (abstractSpine (a_, g_, depth, (s_, s)))) end
      else begin I.Root (c_, (abstractSpine (a_, g_, depth, (s_, s)))) end
  | (a_, g_, depth, (Root (c_, s_), s)) ->
      I.Root (c_, (abstractSpine (a_, g_, depth, (s_, s))))
  | (a_, g_, depth, (EVar (r, _, v_, _), s)) ->
      let (k, Vraised) = lookupEV (a_, r) in
      ((I.Root
          ((I.BVar (k + depth)),
            (abstractSub
               (a_, g_, depth, (Vraised, I.id), s, (I.targetFam v_), I.Nil))))
        (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *))
  | (a_, g_, depth, (FgnExp csfe, s)) ->
      I.FgnExpStd.Map.apply csfe
        (begin function | u_ -> abstractExp (a_, g_, depth, (u_, s)) end) end
(* s = id *)(* s = id *)
let rec abstractExp (a_, g_, depth, us_) =
  abstractExpW (a_, g_, depth, (Whnf.whnf us_))
let rec abstractSpine =
  begin function
  | (a_, g_, depth, (I.Nil, _)) -> I.Nil
  | (a_, g_, depth, (App (u_, s_), s)) ->
      I.App
        ((abstractExp (a_, g_, depth, (u_, s))),
          (abstractSpine (a_, g_, depth, (s_, s))))
  | (a_, g_, depth, (SClo (s_, s'), s)) ->
      abstractSpine (a_, g_, depth, (s_, (I.comp (s', s)))) end
let rec abstractSub (a_, g_, depth, XVt, s, b, s_) =
  abstractSubW (a_, g_, depth, (Whnf.whnf XVt), s, b, s_)
let rec abstractSubW =
  begin function
  | (a_, g_, depth, (Root _, _), s, b, s_) -> s_
  | (a_, g_, depth, ((Pi _, _) as XVt), Shift k, b, s_) ->
      abstractSub
        (a_, g_, depth, XVt, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), b,
          s_)
  | (a_, g_, depth, ((Pi (_, XV'), t) as XVt), Dot (Idx k, s), b, s_) ->
      let Dec (x, v_) = I.ctxDec (g_, k) in
      if k > depth
      then
        begin let k' = lookupBV (a_, (k - depth)) in
              abstractSub
                (a_, g_, depth, (XV', (I.dot1 t)), s, b,
                  (I.App ((I.Root ((I.BVar (k' + depth)), I.Nil)), s_))) end
        else begin
          abstractSub
            (a_, g_, depth, (XV', (I.dot1 t)), s, b,
              (I.App ((I.Root ((I.BVar k), I.Nil)), s_))) end
  | (a_, g_, depth, ((Pi (_, XV'), t) as XVt), Dot (Exp (u_), s), b, s_) ->
      abstractSub
        (a_, g_, depth, (XV', (I.dot1 t)), s, b,
          (I.App ((abstractExp (a_, g_, depth, (u_, I.id))), s_))) end
let rec abstractDec (a_, g_, depth, (Dec (xOpt, v_), s)) =
  I.Dec (xOpt, (abstractExp (a_, g_, depth, (v_, s))))
let rec abstractCtx =
  begin function
  | (I.Null, (Prefix (I.Null, I.Null, I.Null) as GM)) -> (GM, I.Null)
  | (Decl (a_, BV), Prefix (Decl (g_, d_), Decl (m_, marg), Decl (b_, b))) ->
      let (Prefix (g'_, m'_, b'_), lG') =
        abstractCtx (a_, (M.Prefix (g_, m_, b_))) in
      let d'_ = abstractDec (a_, g_, 0, (d_, I.id)) in
      let Dec (_, v_) = d'_ in
      let _ =
        if !Global.doubleCheck
        then begin typecheck ((M.Prefix (g'_, m'_, b'_)), v_) end
        else begin () end in
      ((M.Prefix
          ((I.Decl (g'_, (Names.decName (g'_, d'_)))), (I.Decl (m'_, marg)),
            (I.Decl (b'_, b)))), (I.Decl (lG', d'_)))
  | (Decl (a_, EV (r, v_, m)), GM) ->
      let (Prefix (g'_, m'_, b'_), lG') = abstractCtx (a_, GM) in
      let V'' = abstractExp (a_, lG', 0, (v_, I.id)) in
      let _ =
        if !Global.doubleCheck
        then begin typecheck ((M.Prefix (g'_, m'_, b'_)), V'') end
        else begin () end in
      ((M.Prefix
          ((I.Decl (g'_, (Names.decName (g'_, (I.Dec (None, V'')))))),
            (I.Decl (m'_, m)),
            (I.Decl
               (b'_,
                 (begin match m with
                  | M.Top -> !MetaGlobal.maxSplit
                  | M.Bot -> 0 end))))),
        lG') end
let rec abstract (State (name, (Prefix (g_, m_, b_) as GM), v_) as s_) =
  let _ = Names.varReset I.Null in
  let a_ = collect (GM, v_) in
  let (GM', _) = abstractCtx (a_, GM) in
  let v'_ = abstractExp (a_, g_, 0, (v_, I.id)) in
  let s_ = M.State (name, GM', v'_) in
  let _ = if !Global.doubleCheck then begin typecheck (GM', v'_) end
    else begin () end in
  s_
let abstract = abstract end
