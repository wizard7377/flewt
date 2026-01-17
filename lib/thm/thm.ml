
module type THM  =
  sig
    module ThmSyn :
    ((THMSYN)(* Theorem Declarations *)(* Author: Carsten Schuermann *)
    (* Modified: Brigitte Pientka, Frank Pfenning *))
    exception Error of
      ((string)(*! structure Paths : PATHS !*)) 
    val installTotal :
      (ThmSyn.__TDecl * (Paths.region * Paths.region list)) ->
        IntSyn.cid list
    val uninstallTotal : IntSyn.cid -> bool
    val installTerminates :
      (ThmSyn.__TDecl * (Paths.region * Paths.region list)) ->
        IntSyn.cid list
    val uninstallTerminates : IntSyn.cid -> bool
    val installReduces :
      (ThmSyn.__RDecl * (Paths.region * Paths.region list)) ->
        ((IntSyn.cid)(* true: was declared, false not *))
          list
    val uninstallReduces : IntSyn.cid -> bool
    val installTabled : ThmSyn.__TabledDecl -> unit
    val installKeepTable : ThmSyn.__KeepTableDecl -> unit
  end;;




module Thm(Thm:sig
                 module Global : GLOBAL
                 module ThmSyn' : THMSYN
                 module TabledSyn : TABLEDSYN
                 module ModeTable : MODETABLE
                 module Order : ORDER
                 module ThmPrint :
                 ((THMPRINT)(* Theorem and Related Declarations *)
                 (* Author: Carsten Schuermann *)(* Modified: Brigitte Pientka *)
                 (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*))
               end) : THM =
  struct
    module ThmSyn =
      ((ThmSyn')(*! structure Paths' : PATHS !*))
    module TabledSyn =
      ((TabledSyn)(*! structure Paths = Paths' !*))
    type __Order =
      | Varg 
      | Lex of ((__Order)(* -bp *)) list 
      | Simul of __Order list 
    exception Error of string 
    module L = ThmSyn
    module M = ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    let rec unique (((a, P), r), A) =
      let unique' =
        function
        | (Uni _, nil, A) -> A
        | (Pi (_, V), (NONE)::P, A) -> unique' (V, P, A)
        | (Pi (_, V), (SOME x)::P, A) ->
            (List.app
               (function
                | x' ->
                    if x = x'
                    then
                      error (r, (("Variable " ^ x) ^ " used more than once"))
                    else ()) A;
             unique' (V, P, (x :: A)))
        | (Uni _, _, _) ->
            error
              (r,
                ((^) "Too many arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Pi (_, V), nil, _) ->
            error
              (r,
                ((^) "Too few arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Root _, _, _) ->
            error
              (r,
                (((^) "Constant " Names.qidToString (Names.constQid a)) ^
                   " is an object, not a type family")) in
      let skip =
        function
        | (0, V, P, A) -> unique' (V, P, A)
        | (k, Pi (_, V), P, A) -> skip ((k - 1), V, P, A) in
      skip ((I.constImp a), (I.constType a), P, A)
    let rec uniqueCallpats (L, rs) =
      let uniqueCallpats' =
        function
        | ((nil, nil), A) -> ()
        | ((aP::L, r::rs), A) ->
            uniqueCallpats' ((L, rs), (unique ((aP, r), A))) in
      uniqueCallpats' ((L, rs), nil)
    let rec wfCallpats (L0, C0, r) =
      let makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::L -> (s ^ " ") ^ (makestring L) in
      let exists' =
        function
        | (x, nil, _) -> false__
        | (x, (NONE)::L, Mapp (_, mS)) -> exists' (x, L, mS)
        | (x, (SOME y)::L, Mapp (Marg (mode, _), mS)) ->
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
            else exists' (x, L, mS) in
      let skip =
        function
        | (0, x, P, mS) -> exists' (x, P, mS)
        | (k, x, P, Mapp (_, mS)) -> skip ((k - 1), x, P, mS) in
      let delete =
        function
        | (x, ((a, P) as aP)::C) ->
            if skip ((I.constImp a), x, P, (valOf (ModeTable.modeLookup a)))
            then C
            else (::) aP delete (x, C)
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let wfCallpats' =
        function
        | (nil, nil) -> ()
        | (x::L, C) -> wfCallpats' (L, (delete (x, C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring L0) ^
                   ") does not cover all call patterns")) in
      wfCallpats' (L0, C0)
    let rec wf ((O, Callpats (C)), (r, rs)) =
      let wfOrder =
        function
        | Varg (L) -> wfCallpats (L, C, r)
        | Lex (L) -> wfOrders L
        | Simul (L) -> wfOrders L
      and wfOrders = function | nil -> () | (O)::L -> (wfOrder O; wfOrders L) in
      let allModed =
        function
        | nil -> ()
        | (a, P)::Cs ->
            ((match ModeTable.modeLookup a with
              | NONE ->
                  error
                    (r,
                      (((^) "Expected " Names.qidToString (Names.constQid a))
                         ^ " to be moded"))
              | SOME mS -> ());
             allModed Cs) in
      allModed C; uniqueCallpats (C, rs); wfOrder O
    let rec argPos =
      function
      | (x, nil, n) -> NONE
      | (x, (NONE)::L, n) -> argPos (x, L, (n + 1))
      | (x, (SOME x')::L, n) ->
          if x = x' then SOME n else argPos (x, L, (n + 1))
    let rec locate (x::vars, params, imp) =
      match argPos (x, params, (imp + 1)) with
      | NONE -> locate (vars, params, imp)
      | SOME n -> n
    let rec argOrder =
      function
      | (Varg (L), P, n) -> O.Arg (locate (L, P, n))
      | (Simul (L), P, n) -> O.Simul (argOrderL (L, P, n))
      | (Lex (L), P, n) -> O.Lex (argOrderL (L, P, n))
    let rec argOrderL =
      function
      | (nil, P, n) -> nil
      | ((O)::L, P, n) -> (::) (argOrder (O, P, n)) argOrderL (L, P, n)
    let rec argOrderMutual =
      function
      | (nil, k, A) -> A
      | ((P)::L, k, A) -> argOrderMutual (L, k, (k (P, A)))
    let rec installOrder =
      function
      | (_, nil, _) -> ()
      | (O, ((a, P) as aP)::thmsLE, thmsLT) ->
          let M' =
            argOrderMutual
              (thmsLE, (function | ((a, _), L) -> O.LE (a, L)),
                (argOrderMutual
                   ((aP :: thmsLT), (function | ((a, _), L) -> O.LT (a, L)),
                     O.Empty))) in
          let O' = argOrder (O, P, (I.constImp a)) in
          let S' = O.install (a, (O.TDec (O', M'))) in
          installOrder (O, thmsLE, (aP :: thmsLT))
    let rec installDecl (O, Callpats (L)) =
      installOrder (O, L, nil); map (function | (a, _) -> a) L
    let rec installTerminates (TDecl (T), rrs) = wf (T, rrs); installDecl T
    let rec uninstallTerminates cid = O.uninstall cid
    let rec installTotal (TDecl (T), rrs) = wf (T, rrs); installDecl T
    let rec uninstallTotal cid = O.uninstall cid
    let rec argROrder =
      function
      | (Varg (L), P, n) -> O.Arg (locate (L, P, n))
      | (Simul (L), P, n) -> O.Simul (argROrderL (L, P, n))
      | (Lex (L), P, n) -> O.Lex (argROrderL (L, P, n))
    let rec argROrderL =
      function
      | (nil, P, n) -> nil
      | ((O)::L, P, n) -> (::) (argROrder (O, P, n)) argROrderL (L, P, n)
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
              (thmsLE, (function | ((a, _), L) -> O.LE (a, L)),
                (argOrderMutual
                   ((aP :: thmsLT), (function | ((a, _), L) -> O.LT (a, L)),
                     O.Empty))) in
          let O1' = argROrder (O1, P, (I.constImp a)) in
          let O2' = argROrder (O2, P, (I.constImp a)) in
          let pr = argPredicate (Pred, O1', O2') in
          let S'' = O.installROrder (a, (O.RDec (pr, M'))) in
          installPredicate
            ((L.RedOrder (Pred, O1, O2)), thmsLE, (aP :: thmsLT))
    let rec installRDecl (R, Callpats (L)) =
      installPredicate (R, L, nil); map (function | (a, _) -> a) L
    let rec wfRCallpats (L0, C0, r) =
      let makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::L -> (s ^ " ") ^ (makestring L) in
      let exists' =
        function
        | (x, nil) -> false__
        | (x, (NONE)::L) -> exists' (x, L)
        | (x, (SOME y)::L) -> if x = y then true__ else exists' (x, L) in
      let delete =
        function
        | (x, ((a, P) as aP)::C) ->
            if exists' (x, P) then C else (::) aP delete (x, C)
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let wfCallpats' =
        function
        | (nil, nil) -> ()
        | (x::L, C) -> wfCallpats' (L, (delete (x, C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring L0) ^
                   ") does not cover all call patterns")) in
      wfCallpats' (L0, C0)
    let rec wfred ((RedOrder (Pred, O, O'), Callpats (C)), (r, rs)) =
      let wfOrder =
        function
        | Varg (L) -> (wfRCallpats (L, C, r); Varg)
        | Lex (L) -> Lex (wfOrders L)
        | Simul (L) -> Simul (wfOrders L)
      and wfOrders =
        function | nil -> nil | (O)::L -> (wfOrder O) :: (wfOrders L) in
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
    let ((installTotal)(* L.ModeSyn *)(* To check validity of a termination declaration  O C
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
      (* uniqueCallpats (L, rs) = ()

       Invariant:
       If   L is a callpattern
       and  each variable in L is unique
       then uniqueCallpats returns ()
       else exception Error is raised.

       (rs is a list of region information for error message,
       each region corresponds to one type in the call pattern,
       in order)
    *)
      (* wfCallpats (L, C, r) = ()

       Invariant:
       If   L is a list of variable names of a virtual argument
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
      (* exists by invariant *)(* wf ((O, C), (r, rs)) = ()

       Invariant:
       If   O is an order
       and  C is a call pattern
       then wf terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
      (* argPos (x, L, n) = nOpt

       Invariant:
       If   x is a variable name
       and  L is a list of argument for a call pattern
       and  n is the position of the first argument name in L
            in the call pattern
       then nOpt describes the optional  position of the occurrence
    *)
      (* locate (L, P, n) = n'

       Invariant:
       If   L is a list of variable names (as part of a virtual argument)
       and  P is an argument list (from a call pattern)
       and  n is the position of the first argument name in P
            in the call pattern
       then n' describes the position of the virtual argument in P
    *)
      (* locate nil cannot occur by invariant *)(* argOrder (O, P, n) = O'

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
      (* installDecl (O, C) = L'

       Invariant:
       If   O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: All orders are stored
    *)
      (* installTerminates (T, (r,rs)) = L'

       Invariant:
       If   T is a termination declaration of (O, C)
       and  O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (O, C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
      (* installTotal (T, (r, rs)) = L'
       Invariant as in installTerminates
    *)
      (* -bp *)(* argROrder (O, P, n) = O'

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
      (* install termination order *)(* bug: %reduces should not entail %terminates *)
      (* fixed: Sun Mar 13 09:41:18 2005 -fp *)(* val S'  = O.install (a, O.TDec (O2', M')) *)
      (* install reduction order   *)(* installRDecl (R, C) = L'

       Invariant:
       If   R is a reduction order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

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
      (* installRedOrder (R, (r,rs)) = L'

       Invariant:
       If   R is a reduction declaration of (pred(O,O'), C)
       and  O,O' is an order
       and pred is a predicate
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (pred(O,O'), C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *))
      = installTotal
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
                  module Abstract =
                    ((Abstract)(*! structure IntSyn = IntSyn !*)
                    (*! structure ModeSyn' = ModeSyn !*))
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
               module Order =
                 ((Order)(*       structure RedOrder = RedOrder *)
                 (* -bp *))
               module ModeTable = ModeTable
               module ThmPrint = ThmPrint
               module Paths' = Paths
             end);;
