module type MTPFILLING  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : StateSyn.state_ -> operator
    val apply : operator -> (int * FunSyn.pro_)
    val menu : operator -> string
  end


module MTPFilling(MTPFilling:sig
                               module MTPGlobal : MTPGLOBAL
                               module StateSyn' : STATESYN
                               module Abstract : ABSTRACT
                               module TypeCheck : TYPECHECK
                               module MTPData : MTPDATA
                               module Search : MTPSEARCH
                               module Whnf : WHNF
                             end) : MTPFILLING =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    exception TimeOut 
    type nonrec operator = unit -> (int * FunSyn.pro_)
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success of int 
    let rec createEVars =
      begin function
      | (g_, (F.True, s)) -> ([], F.Unit)
      | (g_, (Ex (Dec (_, v_), f_), s)) ->
          let x_ = I.newEVar (g_, (I.EClo (v_, s))) in
          let x'_ = Whnf.lowerEVar x_ in
          let (xs_, p_) = createEVars (g_, (f_, (I.Dot ((I.Exp x_), s)))) in
          ((x'_ :: xs_), (F.Inx (x_, p_))) end
    let rec expand (State (n, (g_, b_), (IH, OH), d, o_, h_, f_) as s_) =
      let _ = if !Global.doubleCheck then begin TypeCheck.typeCheckCtx g_ end
        else begin () end in
    let (xs_, p_) = createEVars (g_, (f_, I.id)) in
    begin function
    | () ->
        (begin try
                 begin Search.searchEx
                         (!MTPGlobal.maxFill, xs_,
                           (begin function
                            | max ->
                                (begin if !Global.doubleCheck
                                       then
                                         begin map
                                                 (begin function
                                                  | EVar (_, g'_, v_, _) as
                                                      x_ ->
                                                      TypeCheck.typeCheck
                                                        (g'_, (x_, v_)) end)
                                         xs_ end
                                else begin [] end; raise (Success max) end) end));
      raise (Error "Filling unsuccessful") end
  with
  | Success max ->
      (begin (:=) MTPData.maxFill Int.max (!MTPData.maxFill, max); (max, p_) end) end) end
let rec apply f = f ()
let rec menu _ = "Filling   (tries to close this subgoal)"
let expand = expand
let apply = apply
let menu = menu end
