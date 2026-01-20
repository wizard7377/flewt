
module type THM  =
  sig
    module ThmSyn : THMSYN
    exception Error of string 
    val installTotal :
      ThmSyn.__TDecl -> (Paths.region * Paths.region list) -> IntSyn.cid list
    val uninstallTotal : IntSyn.cid -> bool
    val installTerminates :
      ThmSyn.__TDecl -> (Paths.region * Paths.region list) -> IntSyn.cid list
    val uninstallTerminates : IntSyn.cid -> bool
    val installReduces :
      ThmSyn.__RDecl -> (Paths.region * Paths.region list) -> IntSyn.cid list
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
                 module ThmPrint : THMPRINT
               end) : THM =
  struct
    module ThmSyn = ThmSyn'
    module TabledSyn = TabledSyn
    type __Order =
      | Varg 
      | Lex of __Order list 
      | Simul of __Order list 
    exception Error of string 
    module L = ThmSyn
    module M = ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order
    let rec error r msg = raise (Error (Paths.wrap (r, msg)))
    let rec unique ((a, __P), r) (__A) =
      let rec unique' __0__ __1__ __2__ =
        match (__0__, __1__, __2__) with
        | (Uni _, nil, __A) -> __A
        | (Pi (_, __V), (NONE)::__P, __A) -> unique' (__V, __P, __A)
        | (Pi (_, __V), (Some x)::__P, __A) ->
            (List.app
               (fun x' ->
                  if x = x'
                  then
                    error (r, (("Variable " ^ x) ^ " used more than once"))
                  else ()) __A;
             unique' (__V, __P, (x :: __A)))
        | (Uni _, _, _) ->
            error
              (r,
                ((^) "Too many arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Pi (_, __V), nil, _) ->
            error
              (r,
                ((^) "Too few arguments supplied to type family "
                   Names.qidToString (Names.constQid a)))
        | (Root _, _, _) ->
            error
              (r,
                (((^) "Constant " Names.qidToString (Names.constQid a)) ^
                   " is an object, not a type family")) in
      let rec skip __3__ __4__ __5__ __6__ =
        match (__3__, __4__, __5__, __6__) with
        | (0, __V, __P, __A) -> unique' (__V, __P, __A)
        | (k, Pi (_, __V), __P, __A) -> skip ((k - 1), __V, __P, __A) in
      skip ((I.constImp a), (I.constType a), __P, __A)
    let rec uniqueCallpats (__L) rs =
      let rec uniqueCallpats' __7__ __8__ =
        match (__7__, __8__) with
        | ((nil, nil), __A) -> ()
        | ((aP::__L, r::rs), __A) ->
            uniqueCallpats' ((__L, rs), (unique ((aP, r), __A))) in
      uniqueCallpats' ((__L, rs), nil)
    let rec wfCallpats (__L0) (__C0) r =
      let rec makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::__L -> (s ^ " ") ^ (makestring __L) in
      let rec exists' __9__ __10__ __11__ =
        match (__9__, __10__, __11__) with
        | (x, nil, _) -> false__
        | (x, (NONE)::__L, Mapp (_, mS)) -> exists' (x, __L, mS)
        | (x, (Some y)::__L, Mapp (Marg (mode, _), mS)) ->
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
            else exists' (x, __L, mS) in
      let rec skip __12__ __13__ __14__ __15__ =
        match (__12__, __13__, __14__, __15__) with
        | (0, x, __P, mS) -> exists' (x, __P, mS)
        | (k, x, __P, Mapp (_, mS)) -> skip ((k - 1), x, __P, mS) in
      let rec delete __16__ __17__ =
        match (__16__, __17__) with
        | (x, ((a, __P) as aP)::__C) ->
            ((if
                skip
                  ((I.constImp a), x, __P, (valOf (ModeTable.modeLookup a)))
              then __C
              else (::) aP delete (x, __C))
            (* exists by invariant *))
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let rec wfCallpats' __18__ __19__ =
        match (__18__, __19__) with
        | (nil, nil) -> ()
        | (x::__L, __C) -> wfCallpats' (__L, (delete (x, __C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring __L0) ^
                   ") does not cover all call patterns")) in
      ((wfCallpats' (__L0, __C0))
        (* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *))
    let rec wf (__O, Callpats (__C)) (r, rs) =
      let rec wfOrder =
        function
        | Varg (__L) -> wfCallpats (__L, __C, r)
        | Lex (__L) -> wfOrders __L
        | Simul (__L) -> wfOrders __L
      and wfOrders =
        function | nil -> () | (__O)::__L -> (wfOrder __O; wfOrders __L) in
      let rec allModed =
        function
        | nil -> ()
        | (a, __P)::__Cs ->
            ((match ModeTable.modeLookup a with
              | NONE ->
                  error
                    (r,
                      (((^) "Expected " Names.qidToString (Names.constQid a))
                         ^ " to be moded"))
              | Some mS -> ());
             allModed __Cs) in
      allModed __C; uniqueCallpats (__C, rs); wfOrder __O
    let rec argPos __20__ __21__ __22__ =
      match (__20__, __21__, __22__) with
      | (x, nil, n) -> NONE
      | (x, (NONE)::__L, n) -> argPos (x, __L, (n + 1))
      | (x, (Some x')::__L, n) ->
          if x = x' then Some n else argPos (x, __L, (n + 1))
    let rec locate (x::vars) params imp =
      match argPos (x, params, (imp + 1)) with
      | NONE -> locate (vars, params, imp)
      | Some n -> n
    let rec argOrder __23__ __24__ __25__ =
      match (__23__, __24__, __25__) with
      | (Varg (__L), __P, n) -> O.Arg (locate (__L, __P, n))
      | (Simul (__L), __P, n) -> O.Simul (argOrderL (__L, __P, n))
      | (Lex (__L), __P, n) -> O.Lex (argOrderL (__L, __P, n))
    let rec argOrderL __26__ __27__ __28__ =
      match (__26__, __27__, __28__) with
      | (nil, __P, n) -> nil
      | ((__O)::__L, __P, n) ->
          (::) (argOrder (__O, __P, n)) argOrderL (__L, __P, n)
    let rec argOrderMutual __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (nil, k, __A) -> __A
      | ((__P)::__L, k, __A) -> argOrderMutual (__L, k, (k (__P, __A)))
    let rec installOrder __32__ __33__ __34__ =
      match (__32__, __33__, __34__) with
      | (_, nil, _) -> ()
      | (__O, ((a, __P) as aP)::thmsLE, thmsLT) ->
          let __M' =
            argOrderMutual
              (thmsLE, (fun (a, _) -> fun (__L) -> O.LE (a, __L)),
                (argOrderMutual
                   ((aP :: thmsLT),
                     (fun (a, _) -> fun (__L) -> O.LT (a, __L)), O.Empty))) in
          let __O' = argOrder (__O, __P, (I.constImp a)) in
          let __S' = O.install (a, (O.TDec (__O', __M'))) in
          installOrder (__O, thmsLE, (aP :: thmsLT))
    let rec installDecl (__O) (Callpats (__L)) =
      installOrder (__O, __L, nil); map (fun a -> fun _ -> a) __L
    let rec installTerminates (TDecl (__T)) rrs =
      wf (__T, rrs); installDecl __T
    let rec uninstallTerminates cid = O.uninstall cid
    let rec installTotal (TDecl (__T)) rrs = wf (__T, rrs); installDecl __T
    let rec uninstallTotal cid = O.uninstall cid
    let rec argROrder __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (Varg (__L), __P, n) -> O.Arg (locate (__L, __P, n))
      | (Simul (__L), __P, n) -> O.Simul (argROrderL (__L, __P, n))
      | (Lex (__L), __P, n) -> O.Lex (argROrderL (__L, __P, n))
    let rec argROrderL __38__ __39__ __40__ =
      match (__38__, __39__, __40__) with
      | (nil, __P, n) -> nil
      | ((__O)::__L, __P, n) ->
          (::) (argROrder (__O, __P, n)) argROrderL (__L, __P, n)
    let rec argPredicate __41__ __42__ __43__ =
      match (__41__, __42__, __43__) with
      | (L.Less, __O, __O') -> O.Less (__O, __O')
      | (L.Leq, __O, __O') -> O.Leq (__O, __O')
      | (L.Eq, __O, __O') -> O.Eq (__O, __O')
    let rec installPredicate __44__ __45__ __46__ =
      match (__44__, __45__, __46__) with
      | (_, nil, _) -> ()
      | (RedOrder (Pred, __O1, __O2), ((a, __P) as aP)::thmsLE, thmsLT) ->
          let __M' =
            argOrderMutual
              (thmsLE, (fun (a, _) -> fun (__L) -> O.LE (a, __L)),
                (argOrderMutual
                   ((aP :: thmsLT),
                     (fun (a, _) -> fun (__L) -> O.LT (a, __L)), O.Empty))) in
          let O1' = argROrder (__O1, __P, (I.constImp a)) in
          let O2' = argROrder (__O2, __P, (I.constImp a)) in
          let pr = argPredicate (Pred, O1', O2') in
          let S'' = O.installROrder (a, (O.RDec (pr, __M'))) in
          ((installPredicate
              ((L.RedOrder (Pred, __O1, __O2)), thmsLE, (aP :: thmsLT)))
            (* install termination order *)(* bug: %reduces should not entail %terminates *)
            (* fixed: Sun Mar 13 09:41:18 2005 -fp *)
            (* val S'  = O.install (a, O.TDec (O2', M')) *)
            (* install reduction order   *))
    let rec installRDecl (__R) (Callpats (__L)) =
      installPredicate (__R, __L, nil); map (fun a -> fun _ -> a) __L
    let rec wfRCallpats (__L0) (__C0) r =
      let rec makestring =
        function
        | nil -> ""
        | s::nil -> s
        | s::__L -> (s ^ " ") ^ (makestring __L) in
      let rec exists' __47__ __48__ =
        match (__47__, __48__) with
        | (x, nil) -> false__
        | (x, (NONE)::__L) -> exists' (x, __L)
        | (x, (Some y)::__L) -> if x = y then true__ else exists' (x, __L) in
      let rec delete __49__ __50__ =
        match (__49__, __50__) with
        | (x, ((a, __P) as aP)::__C) ->
            if exists' (x, __P) then __C else (::) aP delete (x, __C)
        | (x, nil) ->
            error (r, (("Variable " ^ x) ^ " does not occur as argument")) in
      let rec wfCallpats' __51__ __52__ =
        match (__51__, __52__) with
        | (nil, nil) -> ()
        | (x::__L, __C) -> wfCallpats' (__L, (delete (x, __C)))
        | _ ->
            error
              (r,
                (((^) "Mutual argument (" makestring __L0) ^
                   ") does not cover all call patterns")) in
      wfCallpats' (__L0, __C0)
    let rec wfred (RedOrder (Pred, __O, __O'), Callpats (__C)) (r, rs) =
      let rec wfOrder =
        function
        | Varg (__L) -> (wfRCallpats (__L, __C, r); Varg)
        | Lex (__L) -> Lex (wfOrders __L)
        | Simul (__L) -> Simul (wfOrders __L)
      and wfOrders =
        function | nil -> nil | (__O)::__L -> (wfOrder __O) :: (wfOrders __L) in
      uniqueCallpats (__C, rs);
      if (=) (wfOrder __O) wfOrder __O'
      then ()
      else
        error
          (r,
            (((^) "Reduction Order (" P.ROrderToString
                (L.RedOrder (Pred, __O, __O')))
               ^ ") requires both orders to be of the same type."))
    let rec installReduces (RDecl (__R, __C)) rrs =
      wfred ((__R, __C), rrs); installRDecl (__R, __C)
    let rec uninstallReduces cid = O.uninstallROrder cid
    let rec installTabled (TabledDecl cid) = TabledSyn.installTabled cid
    let rec installKeepTable (KeepTableDecl cid) =
      TabledSyn.installKeepTable cid
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
               module Order = Order
               module ModeTable = ModeTable
               module ThmPrint = ThmPrint
               module Paths' = Paths
             end);;
