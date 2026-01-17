
module type MTPFILLING  =
  sig
    module StateSyn :
    ((STATESYN)(* Filling: Version 1.3 *)(* Author: Carsten Schuermann *)
    (*! structure FunSyn : FUNSYN !*))
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> (int * FunSyn.__Pro)
    val menu : operator -> string
  end;;




module MTPFilling(MTPFilling:sig
                               module MTPGlobal : MTPGLOBAL
                               module StateSyn' : STATESYN
                               module Abstract : ABSTRACT
                               module TypeCheck : TYPECHECK
                               module MTPData : MTPDATA
                               module Search : MTPSEARCH
                               module Whnf :
                               ((WHNF)(* Filling  Version 1.3*)(* Author: Carsten Schuermann *)
                               (*! structure IntSyn : INTSYN !*)
                               (*! structure FunSyn' : FUNSYN !*)
                               (*! sharing FunSyn'.IntSyn = IntSyn !*)
                               (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn !*)
                               (*! sharing TypeCheck.IntSyn = IntSyn !*))
                             end) : MTPFILLING =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing Whnf.IntSyn = IntSyn !*)
      (*! structure FunSyn = FunSyn' !*))
    exception Error of string 
    exception TimeOut 
    type nonrec operator = unit -> (int * FunSyn.__Pro)
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn
    exception Success of int 
    let rec createEVars =
      function
      | (g, (F.True, s)) -> (nil, F.Unit)
      | (g, (Ex (Dec (_, V), F), s)) ->
          let X = I.newEVar (g, (I.EClo (V, s))) in
          let X' = Whnf.lowerEVar X in
          let (Xs, P) = createEVars (g, (F, (I.Dot ((I.Exp X), s)))) in
          ((X' :: Xs), (F.Inx (X, P)))
    let rec expand (State (n, (g, B), (IH, OH), d, O, H, F) as S) =
      let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx g else () in
      let (Xs, P) = createEVars (g, (F, I.id)) in
      function
      | () ->
          (try
             Search.searchEx
               ((!MTPGlobal.maxFill), Xs,
                 (function
                  | max ->
                      (if !Global.doubleCheck
                       then
                         map
                           (function
                            | EVar (_, g', V, _) as X ->
                                TypeCheck.typeCheck (g', (X, V))) Xs
                       else [];
                       raise (Success max))));
             raise (Error "Filling unsuccessful")
           with
           | Success max ->
               ((:=) MTPData.maxFill Int.max ((!MTPData.maxFill), max);
                (max, P)))
    let rec apply f = f ()
    let rec menu _ = "Filling   (tries to close this subgoal)"
    let ((expand)(* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)
      (* createEVars (g, F) = (Xs', P')

       Invariant:
       If   |- g ctx
       and  g |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  g |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  g; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
      (*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
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
    *))
      = expand
    let apply = apply
    let menu = menu
  end ;;
