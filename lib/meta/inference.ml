module type INFERENCE  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.state_ -> operator
    val apply : operator -> StateSyn.state_
    val menu : operator -> string
  end


module Inference(Inference:sig
                             module MTPGlobal : MTPGLOBAL
                             module StateSyn' : STATESYN
                             module Abstract : ABSTRACT
                             module TypeCheck : TYPECHECK
                             module FunTypeCheck : FUNTYPECHECK
                             module UniqueSearch : UNIQUESEARCH
                             module Print : PRINT
                             module Whnf : WHNF
                           end) : INFERENCE =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = unit -> StateSyn'.state_
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success 
    let rec createEVars =
      begin function
      | (g_, (Pi ((Dec (_, v_), I.Meta), v'_), s)) ->
          let x_ = I.newEVar (g_, (I.EClo (v_, s))) in
          let x'_ = Whnf.lowerEVar x_ in
          let (xs_, FVs') = createEVars (g_, (v'_, (I.Dot ((I.Exp x_), s)))) in
          ((x'_ :: xs_), FVs')
      | (g_, ((_, s) as FVs)) -> ([], FVs) end
    let rec forward =
      begin function
      | (g_, b_, (Pi ((_, I.Meta), _) as v_)) ->
          let _ =
            if !Global.doubleCheck
            then begin TypeCheck.typeCheck (g_, (v_, (I.Uni I.Type))) end
            else begin () end in
    let (xs_, (v'_, s')) = createEVars (g_, (v_, I.id)) in
    (begin try
             begin match UniqueSearch.searchEx
                           (2, xs_,
                             (begin function
                              | [] -> [Whnf.normalize (v'_, s')]
                              | _ ->
                                  raise
                                    (UniqueSearch.Error "Too many solutions") end))
             with
             | (VF'')::[] -> Some VF''
             | [] -> None end
      with | Error _ -> None end) | (g_, b_, v_) -> None end
let rec expand' =
  begin function
  | ((g0_, b0_), (I.Null, I.Null), n) ->
      ((I.Null, I.Null),
        ((begin function | ((g'_, b'_), w') -> ((g'_, b'_), w') end)))
  | ((g0_, b0_),
     (Decl (g_, (Dec (_, v_) as d_)), Decl (b_, (Lemma (S.RL) as t_))), n) ->
      let ((G0', B0'), sc') = expand' ((g0_, b0_), (g_, b_), (n + 1)) in
      let s = I.Shift (n + 1) in
      let vs_ = Whnf.normalize (v_, s) in
      (begin match forward (g0_, b0_, vs_) with
       | None -> (((I.Decl (G0', d_)), (I.Decl (B0', t_))), sc')
       | Some (v'_) ->
           (((I.Decl (G0', d_)), (I.Decl (B0', (S.Lemma S.RLdone)))),
             ((begin function
               | ((g'_, b'_), w') ->
                   let V'' = Whnf.normalize (v'_, w') in
                   ((sc'
                       (((I.Decl (g'_, (I.Dec (None, V'')))),
                          (I.Decl
                             (b'_, (S.Lemma (S.Splits !MTPGlobal.maxSplit))))),
                         (I.comp (w', I.shift))))
                     (* G' |- V'' : type *)) end))) end)
| (GB0, (Decl (g_, d_), Decl (b_, t_)), n) ->
    let ((G0', B0'), sc') = expand' (GB0, (g_, b_), (n + 1)) in
    (((I.Decl (G0', d_)), (I.Decl (B0', t_))), sc') end
let rec expand (State (n, (g_, b_), (IH, OH), d, o_, h_, f_) as s_) =
  let _ = if !Global.doubleCheck then begin TypeCheck.typeCheckCtx g_ end
    else begin () end in
let ((Gnew, Bnew), sc) = expand' ((g_, b_), (g_, b_), 0) in
let _ = if !Global.doubleCheck then begin TypeCheck.typeCheckCtx Gnew end
  else begin () end in
let ((g'_, b'_), w') = sc ((Gnew, Bnew), I.id) in
let _ = TypeCheck.typeCheckCtx g'_ in
let s'_ =
  S.State
    (n, (g'_, b'_), (IH, OH), d, (S.orderSub (o_, w')),
      (map (begin function | (i, f'_) -> (i, (F.forSub (f'_, w'))) end) h_),
    (F.forSub (f_, w'))) in
let _ = if !Global.doubleCheck then begin FunTypeCheck.isState s'_ end
  else begin () end in
begin function | () -> s'_ end
let rec apply f = f ()
let rec menu _ = "Inference"
let expand = expand
let apply = apply
let menu = menu end
