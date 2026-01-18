
(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPFILLING  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> (int * FunSyn.__Pro)
    val menu : operator -> string
  end;;




(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)
module MTPFilling(MTPFilling:sig
                               module MTPGlobal : MTPGLOBAL
                               module StateSyn' : STATESYN
                               module Abstract : ABSTRACT
                               module TypeCheck : TYPECHECK
                               module MTPData : MTPDATA
                               module Search : MTPSEARCH
                               (*! structure IntSyn : INTSYN !*)
                               (*! structure FunSyn' : FUNSYN !*)
                               (*! sharing FunSyn'.IntSyn = IntSyn !*)
                               (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn !*)
                               (*! sharing TypeCheck.IntSyn = IntSyn !*)
                               module Whnf : WHNF
                             end) : MTPFILLING =
  struct
    (*! sharing Whnf.IntSyn = IntSyn !*)
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    exception Error of string 
    exception TimeOut 
    type nonrec operator = unit -> (int * FunSyn.__Pro)
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success of int 
    let rec createEVars =
      function
      | (__g, (F.True, s)) -> (nil, F.Unit)
      | (__g, (Ex (Dec (_, __v), F), s)) ->
          let x = I.newEVar (__g, (I.EClo (__v, s))) in
          let x' = Whnf.lowerEVar x in
          let (__Xs, P) = createEVars (__g, (F, (I.Dot ((I.Exp x), s)))) in
          ((x' :: __Xs), (F.Inx (x, P)))
    let rec expand (State (n, (__g, B), (IH, OH), d, O, H, F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx __g else () in
      let (__Xs, P) = createEVars (__g, (F, I.id)) in
      function
      | () ->
          (try
             Search.searchEx
               ((!MTPGlobal.maxFill), __Xs,
                 (function
                  | max ->
                      (if !Global.doubleCheck
                       then
                         map
                           (function
                            | EVar (_, __g', __v, _) as x ->
                                TypeCheck.typeCheck (__g', (x, __v))) __Xs
                       else [];
                       raise (Success max))));
             raise (Error "Filling unsuccessful")
           with
           | Success max ->
               ((:=) MTPData.maxFill Int.max ((!MTPData.maxFill), max);
                (max, P)))
    let rec apply f = f ()
    let rec menu _ = "Filling   (tries to close this subgoal)"
    (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)
    (* createEVars (__g, F) = (__Xs', __P')

       Invariant:
       If   |- __g ctx
       and  __g |- F = [[x1:A1]] .. [[xn::An]] formula
       then __Xs' = (X1', .., Xn') a list of EVars
       and  __g |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  __g; __d |- __P' = <X1', <.... <Xn', <>> ..> in F     for some __d
    *)
    (*    fun checkConstraints nil = raise Success
      | checkConstraints (x :: __l) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (x, I.id), I.id)) then checkConstraints __l
        else ()
*)
    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
