
(* Theorem Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka, Frank Pfenning *)
module type THM  =
  sig
    module ThmSyn : THMSYN
    (*! structure Paths : PATHS !*)
    exception Error of string 
    val installTotal :
      (ThmSyn.__TDecl * (Paths.region * Paths.region list)) ->
        IntSyn.cid list
    val uninstallTotal : IntSyn.cid -> bool
    val installTerminates :
      (ThmSyn.__TDecl * (Paths.region * Paths.region list)) ->
        IntSyn.cid list
    val uninstallTerminates : IntSyn.cid -> bool
    (* true: was declared, false not *)
    val installReduces :
      (ThmSyn.__RDecl * (Paths.region * Paths.region list)) ->
        IntSyn.cid list
    val uninstallReduces : IntSyn.cid -> bool
    val installTabled : ThmSyn.__TabledDecl -> unit
    val installKeepTable : ThmSyn.__KeepTableDecl -> unit
  end;;




(* Theorem and Related Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module Thm(Thm:sig
                 module Global : GLOBAL
                 module ThmSyn' : THMSYN
                 module TabledSyn : TABLEDSYN
                 module ModeTable : MODETABLE
                 module Order : ORDER
                 (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
                 module ThmPrint : THMPRINT
               end) : THM =
  struct
    (*! structure Paths' : PATHS !*)
    module ThmSyn = ThmSyn'
    (*! structure Paths = Paths' !*)
    module TabledSyn = TabledSyn
    (* -bp *)
    type __Order =
      | Varg 
      | Lex of __Order list 
      | Simul of __Order list 
    exception Error of string 
    module __l = ThmSyn
    module M = ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    let rec unique (((a, P), r), A) =
      let rec unique' =
        function
        | (Uni _, nil, A) -> A
        | (Pi (_, __v), (None)::P, A) -> unique' (__v, P, A)
        | (Pi (_, __v), (Some x)::P, A) ->
            (List.app
               (function
                | x' ->
                    if x = x'
                    then
                      error (r, (("Variable " ^ x) ^ " used more than once"))
                    else ()) A;
             unique' (__v, P, (x :: A)))
        | (Uni _, _, _) ->
            error
              (r,
                ((^) "Too many arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Pi (_, __v), nil, _) ->
            error
              (r,
                ((^) "Too few arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Root _, _, _) ->
            error
              (r,
                (((^) "Constant " Names.qidToString (Names.constQid a)) ^
                   " is an object, not a type family")) in
      let rec skip =
        function
        | (0, __v, P, A) -> unique' (__v, P, A)
        | (k, Pi (_, __v), P, A) -> skip ((k - 1), __v, P, A) in
      skip ((I.constImp a), (I.constType a), P, A)
    let rec uniqueCallpats (__l, rs) =
      let rec uniqueCallpats' =
        function
        | ((nil, nil), A) -> ()
        | ((aP::__l, r::rs), A) ->
            uniqueCallpats' ((__l, rs), (unique ((aP, r), A))) in
      uniqueCallpats' ((__l, rs), nil)
    let rec wfCallpats (L0, C0, r) =
      let rec makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::__l -> (s ^ " ") ^ (makestring __l) in
      let rec exists' =
        function
        | (x, nil, _) -> false__
        | (x, (None)::__l, Mapp (_, mS)) -> exists' (x, __l, mS)
        | (x, (Some y)::__l, Mapp (Marg (mode, _), mS)) ->
            if x = y
            then
              (match mode with
               | M.Plus -> true__
               | _ ->
                   error
                     (r,
                       (((^) (("Expected " ^ x) ^ " to have ") M.modeToString
                           M.Plus)
                          ^ " mode")))
            else exists' (x, __l, mS) in
      let rec skip =
        function
        | (0, x, P, mS) -> exists' (x, P, mS)
        | (k, x, P, Mapp (_, mS)) -> skip ((k - 1), x, P, mS) in
      let rec delete =
        function
        | (x, ((a, P) as aP)::C) ->
            if skip ((I.constImp a), x, P, (valOf (ModeTable.modeLookup a)))
            then C
            else (::) aP delete (x, C)
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let rec wfCallpats' =
        function
        | (nil, nil) -> ()
        | (x::__l, C) -> wfCallpats' (__l, (delete (x, C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring L0) ^
                   ") does not cover all call patterns")) in
      wfCallpats' (L0, C0)
    let rec wf ((O, Callpats (C)), (r, rs)) =
      let rec wfOrder =
        function
        | Varg (__l) -> wfCallpats (__l, C, r)
        | Lex (__l) -> wfOrders __l
        | Simul (__l) -> wfOrders __l
      and wfOrders = function | nil -> () | (O)::__l -> (wfOrder O; wfOrders __l) in
      let rec allModed =
        function
        | nil -> ()
        | (a, P)::__Cs ->
            ((match ModeTable.modeLookup a with
              | None ->
                  error
                    (r,
                      (((^) "Expected " Names.qidToString (Names.constQid a))
                         ^ " to be moded"))
              | Some mS -> ());
             allModed __Cs) in
      allModed C; uniqueCallpats (C, rs); wfOrder O
    let rec argPos =
      function
      | (x, nil, n) -> None
      | (x, (None)::__l, n) -> argPos (x, __l, (n + 1))
      | (x, (Some x')::__l, n) ->
          if x = x' then Some n else argPos (x, __l, (n + 1))
    let rec locate (x::vars, params, imp) =
      match argPos (x, params, (imp + 1)) with
      | None -> locate (vars, params, imp)
      | Some n -> n
    let rec argOrder =
      function
      | (Varg (__l), P, n) -> O.Arg (locate (__l, P, n))
      | (Simul (__l), P, n) -> O.Simul (argOrderL (__l, P, n))
      | (Lex (__l), P, n) -> O.Lex (argOrderL (__l, P, n))
    let rec argOrderL =
      function
      | (nil, P, n) -> nil
      | ((O)::__l, P, n) -> (::) (argOrder (O, P, n)) argOrderL (__l, P, n)
    let rec argOrderMutual =
      function
      | (nil, k, A) -> A
      | ((P)::__l, k, A) -> argOrderMutual (__l, k, (k (P, A)))
    let rec installOrder =
      function
      | (_, nil, _) -> ()
      | (O, ((a, P) as aP)::thmsLE, thmsLT) ->
          let M' =
            argOrderMutual
              (thmsLE, (function | ((a, _), __l) -> O.LE (a, __l)),
                (argOrderMutual
                   ((aP :: thmsLT), (function | ((a, _), __l) -> O.LT (a, __l)),
                     O.Empty))) in
          let O' = argOrder (O, P, (I.constImp a)) in
          let S' = O.install (a, (O.TDec (O', M'))) in
          installOrder (O, thmsLE, (aP :: thmsLT))
    let rec installDecl (O, Callpats (__l)) =
      installOrder (O, __l, nil); map (function | (a, _) -> a) __l
    let rec installTerminates (TDecl (T), rrs) = wf (T, rrs); installDecl T
    let rec uninstallTerminates cid = O.uninstall cid
    let rec installTotal (TDecl (T), rrs) = wf (T, rrs); installDecl T
    let rec uninstallTotal cid = O.uninstall cid
    let rec argROrder =
      function
      | (Varg (__l), P, n) -> O.Arg (locate (__l, P, n))
      | (Simul (__l), P, n) -> O.Simul (argROrderL (__l, P, n))
      | (Lex (__l), P, n) -> O.Lex (argROrderL (__l, P, n))
    let rec argROrderL =
      function
      | (nil, P, n) -> nil
      | ((O)::__l, P, n) -> (::) (argROrder (O, P, n)) argROrderL (__l, P, n)
    let rec argPredicate =
      function
      | (L.Less, O, O') -> O.Less (O, O')
      | (L.Leq, O, O') -> O.Leq (O, O')
      | (L.Eq, O, O') -> O.Eq (O, O')
    let rec installPredicate =
      function
      | (_, nil, _) -> ()
      | (RedOrder (Pred, O1, O2), ((a, P) as aP)::thmsLE, thmsLT) ->
          let M' =
            argOrderMutual
              (thmsLE, (function | ((a, _), __l) -> O.LE (a, __l)),
                (argOrderMutual
                   ((aP :: thmsLT), (function | ((a, _), __l) -> O.LT (a, __l)),
                     O.Empty))) in
          let O1' = argROrder (O1, P, (I.constImp a)) in
          let O2' = argROrder (O2, P, (I.constImp a)) in
          let pr = argPredicate (Pred, O1', O2') in
          let S'' = O.installROrder (a, (O.RDec (pr, M'))) in
          installPredicate
            ((L.RedOrder (Pred, O1, O2)), thmsLE, (aP :: thmsLT))
    let rec installRDecl (R, Callpats (__l)) =
      installPredicate (R, __l, nil); map (function | (a, _) -> a) __l
    let rec wfRCallpats (L0, C0, r) =
      let rec makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::__l -> (s ^ " ") ^ (makestring __l) in
      let rec exists' =
        function
        | (x, nil) -> false__
        | (x, (None)::__l) -> exists' (x, __l)
        | (x, (Some y)::__l) -> if x = y then true__ else exists' (x, __l) in
      let rec delete =
        function
        | (x, ((a, P) as aP)::C) ->
            if exists' (x, P) then C else (::) aP delete (x, C)
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let rec wfCallpats' =
        function
        | (nil, nil) -> ()
        | (x::__l, C) -> wfCallpats' (__l, (delete (x, C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring L0) ^
                   ") does not cover all call patterns")) in
      wfCallpats' (L0, C0)
    let rec wfred ((RedOrder (Pred, O, O'), Callpats (C)), (r, rs)) =
      let rec wfOrder =
        function
        | Varg (__l) -> (wfRCallpats (__l, C, r); Varg)
        | Lex (__l) -> Lex (wfOrders __l)
        | Simul (__l) -> Simul (wfOrders __l)
      and wfOrders =
        function | nil -> nil | (O)::__l -> (wfOrder O) :: (wfOrders __l) in
      uniqueCallpats (C, rs);
      if (=) (wfOrder O) wfOrder O'
      then ()
      else
        error
          (r,
            (((^) "Reduction Order (" P.ROrderToString
                (L.RedOrder (Pred, O, O')))
               ^ ") requires both orders to be of the same type."))
    let rec installReduces (RDecl (R, C), rrs) =
      wfred ((R, C), rrs); installRDecl (R, C)
    let rec uninstallReduces cid = O.uninstallROrder cid
    let rec installTabled (TabledDecl cid) = TabledSyn.installTabled cid
    let rec installKeepTable (KeepTableDecl cid) =
      TabledSyn.installKeepTable cid
    (* L.ModeSyn *)
    (* To check validity of a termination declaration  O C
       we enforce that all variable names which occur in C must be distinct
       and if C = C1 .. Cm then we ensure that for all Varg (X1 .. Xn) in O,

           1) n = m
       and 2) each Ci contains an occurrence of Xi
    *)
    (* unique (((a, P), r), A) = A'

       Invariant:
       If   A is a list of variables already collected in a call pattern
       and  P does not contain any variables in A
       then A' = A, Var (P)
       else exception Error is raised.
       (r is region information for error message)
    *)
    (* uniqueCallpats (__l, rs) = ()

       Invariant:
       If   __l is a callpattern
       and  each variable in __l is unique
       then uniqueCallpats returns ()
       else exception Error is raised.

       (rs is a list of region information for error message,
       each region corresponds to one type in the call pattern,
       in order)
    *)
    (* wfCallpats (__l, C, r) = ()

       Invariant:
       If   __l is a list of variable names of a virtual argument
       and  C is a call pattern, the predicate in C has a mode
       then wfCallpats terminates with () if
            1) there are as many call patterns as variable names
            2) each variable name occurs in a different call pattern
       else exception Error is raised
       (r region information, needed for error messages)
    *)
    (* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *)
    (* exists by invariant *)
    (* wf ((O, C), (r, rs)) = ()

       Invariant:
       If   O is an order
       and  C is a call pattern
       then wf terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
    (* argPos (x, __l, n) = nOpt

       Invariant:
       If   x is a variable name
       and  __l is a list of argument for a call pattern
       and  n is the position of the first argument name in __l
            in the call pattern
       then nOpt describes the optional  position of the occurrence
    *)
    (* locate (__l, P, n) = n'

       Invariant:
       If   __l is a list of variable names (as part of a virtual argument)
       and  P is an argument list (from a call pattern)
       and  n is the position of the first argument name in P
            in the call pattern
       then n' describes the position of the virtual argument in P
    *)
    (* locate nil cannot occur by invariant *)
    (* argOrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
    (*  argOrderMutual (C, k, A) = A'

        Invariant:

        If   C is a list of call patterns
        and  k is a function, mapping a call patterns to 'a
        and  A is an acculmulator for objects of type 'a
        then A' is an accumulator extending A containing all
             images of C under k.
    *)
    (* installorder (O, LE, LT) = ()

       Invariant:
       If   O is an order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument order with type families.
    *)
    (* installDecl (O, C) = __l'

       Invariant:
       If   O is an order
       and  C is a call pattern
       then __l' is a list of all type families mentioned in C

       Effect: All orders are stored
    *)
    (* installTerminates (T, (r,rs)) = __l'

       Invariant:
       If   T is a termination declaration of (O, C)
       and  O is an order
       and  C is a call pattern
       then __l' is a list of all type families mentioned in C
            if (O, C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
    (* installTotal (T, (r, rs)) = __l'
       Invariant as in installTerminates
    *)
    (* -bp *)
    (* argROrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
    (* installPredicate (name, R, LE, LT) = ()

       Invariant:
       If   R is a reduction order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument reduction order with
               type families.

    *)
    (* install termination order *)
    (* bug: %reduces should not entail %terminates *)
    (* fixed: Sun Mar 13 09:41:18 2005 -fp *)
    (* val S'  = O.install (a, O.TDec (O2', M')) *)
    (* install reduction order   *)
    (* installRDecl (R, C) = __l'

       Invariant:
       If   R is a reduction order
       and  C is a call pattern
       then __l' is a list of all type families mentioned in C

       Effect: reduction order is stored
    *)
    (* wfRCallpats
       well-formed call pattern in a reduction declaration
       pattern does not need to be moded
       Tue Apr 30 10:32:31 2002 -bp
     *)
    (* wfred ((Red(Pred,O.O'), C), (r, rs)) = ()

       Invariant:
       If   O,O' is an order and Pred is some predicate
       and  C is a call pattern
       then wfred terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
    (* installRedOrder (R, (r,rs)) = __l'

       Invariant:
       If   R is a reduction declaration of (pred(O,O'), C)
       and  O,O' is an order
       and pred is a predicate
       and  C is a call pattern
       then __l' is a list of all type families mentioned in C
            if (pred(O,O'), C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
    let installTotal = installTotal
    let uninstallTotal = uninstallTotal
    let installTerminates = installTerminates
    let uninstallTerminates = uninstallTerminates
    let installReduces = installReduces
    let uninstallReduces = uninstallReduces
    let installTabled = installTabled
    let installKeepTable = installKeepTable
  end ;;




module ThmSyn =
  (Make_ThmSyn)(struct
                  (*! structure IntSyn = IntSyn !*)
                  (*! structure ModeSyn' = ModeSyn !*)
                  module Abstract = Abstract
                  module Whnf = Whnf
                  module Paths' = Paths
                  module Names' = Names
                end)
module ThmPrint =
  (Make_ThmPrint)(struct
                    module ThmSyn' = ThmSyn
                    module Formatter = Formatter
                  end)
module Thm =
  (Make_Thm)(struct
               module Global = Global
               module ThmSyn' = ThmSyn
               module TabledSyn = TabledSyn
               (*       structure RedOrder = RedOrder *)
               (* -bp *)
               module Order = Order
               module ModeTable = ModeTable
               module ThmPrint = ThmPrint
               module Paths' = Paths
             end);;
