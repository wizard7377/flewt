module type THM  =
  sig
    module ThmSyn : THMSYN
    exception Error of string 
    val installTotal :
      (ThmSyn.tDecl_ * (Paths.region * Paths.region list)) -> IntSyn.cid list
    val uninstallTotal : IntSyn.cid -> bool
    val installTerminates :
      (ThmSyn.tDecl_ * (Paths.region * Paths.region list)) -> IntSyn.cid list
    val uninstallTerminates : IntSyn.cid -> bool
    val installReduces :
      (ThmSyn.rDecl_ * (Paths.region * Paths.region list)) -> IntSyn.cid list
    val uninstallReduces : IntSyn.cid -> bool
    val installTabled : ThmSyn.tabledDecl_ -> unit
    val installKeepTable : ThmSyn.keepTableDecl_ -> unit
  end


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
    type order_ =
      | Varg 
      | Lex of order_ list 
      | Simul of order_ list 
    exception Error of string 
    module L = ThmSyn
    module M = ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    let rec unique (((a, p_), r), a_) =
      let rec unique' =
        begin function
        | (Uni _, [], a_) -> a_
        | (Pi (_, v_), (None)::p_, a_) -> unique' (v_, p_, a_)
        | (Pi (_, v_), (Some x)::p_, a_) ->
            (begin List.app
                     (begin function
                      | x' ->
                          if x = x'
                          then
                            begin error
                                    (r,
                                      (("Variable " ^ x) ^
                                         " used more than once")) end
                          else begin () end end)
        a_; unique' (v_, p_, (x :: a_)) end)
      | (Uni _, _, _) ->
          error
            (r,
              ((^) "Too many arguments supplied to type family "
                 Names.qidToString (Names.constQid a)))
      | (Pi (_, v_), [], _) ->
          error
            (r,
              ((^) "Too few arguments supplied to type family "
                 Names.qidToString (Names.constQid a)))
      | (Root _, _, _) ->
          error
            (r,
              (((^) "Constant " Names.qidToString (Names.constQid a)) ^
                 " is an object, not a type family")) end in
let rec skip =
  begin function
  | (0, v_, p_, a_) -> unique' (v_, p_, a_)
  | (k, Pi (_, v_), p_, a_) -> skip ((k - 1), v_, p_, a_) end in
skip ((I.constImp a), (I.constType a), p_, a_)
let rec uniqueCallpats (l_, rs) =
  let rec uniqueCallpats' =
    begin function
    | (([], []), a_) -> ()
    | ((aP::l_, r::rs), a_) ->
        uniqueCallpats' ((l_, rs), (unique ((aP, r), a_))) end in
uniqueCallpats' ((l_, rs), [])
let rec wfCallpats (l0_, c0_, r) =
  let rec makestring =
    begin function
    | [] -> ""
    | s::[] -> s
    | s::l_ -> (s ^ " ") ^ (makestring l_) end in
let rec exists' =
  begin function
  | (x, [], _) -> false
  | (x, (None)::l_, Mapp (_, mS)) -> exists' (x, l_, mS)
  | (x, (Some y)::l_, Mapp (Marg (mode, _), mS)) ->
      if x = y
      then
        begin (begin match mode with
               | M.Plus -> true
               | _ ->
                   error
                     (r,
                       (((^) (("Expected " ^ x) ^ " to have ") M.modeToString
                           M.Plus)
                          ^ " mode")) end) end
  else begin exists' (x, l_, mS) end end in
let rec skip =
begin function
| (0, x, p_, mS) -> exists' (x, p_, mS)
| (k, x, p_, Mapp (_, mS)) -> skip ((k - 1), x, p_, mS) end in
let rec delete =
begin function
| (x, ((a, p_) as aP)::c_) ->
    ((if skip ((I.constImp a), x, p_, (valOf (ModeTable.modeLookup a)))
      then begin c_ end
    else begin (::) aP delete (x, c_) end)
(* exists by invariant *))
| (x, []) -> error (r, (("Variable " ^ x) ^ " does not occur as argument")) end in
let rec wfCallpats' =
begin function
| ([], []) -> ()
| (x::l_, c_) -> wfCallpats' (l_, (delete (x, c_)))
| _ ->
    error
      (r,
        (((^) "Mutual argument (" makestring l0_) ^
           ") does not cover all call patterns")) end in
((wfCallpats' (l0_, c0_))
(* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *))
let rec wf ((o_, Callpats (c_)), (r, rs)) =
  let rec wfOrder =
    begin function
    | Varg (l_) -> wfCallpats (l_, c_, r)
    | Lex (l_) -> wfOrders l_
    | Simul (l_) -> wfOrders l_ end
    and wfOrders =
      begin function
      | [] -> ()
      | (o_)::l_ -> (begin wfOrder o_; wfOrders l_ end) end in
let rec allModed =
begin function
| [] -> ()
| (a, p_)::cs_ ->
    (begin (begin match ModeTable.modeLookup a with
            | None ->
                error
                  (r,
                    (((^) "Expected " Names.qidToString (Names.constQid a)) ^
                       " to be moded"))
            | Some mS -> () end);
    allModed cs_ end) end in
begin allModed c_; uniqueCallpats (c_, rs); wfOrder o_ end
let rec argPos =
  begin function
  | (x, [], n) -> None
  | (x, (None)::l_, n) -> argPos (x, l_, (n + 1))
  | (x, (Some x')::l_, n) -> if x = x' then begin Some n end
      else begin argPos (x, l_, (n + 1)) end end
let rec locate (x::vars, params, imp) =
  begin match argPos (x, params, (imp + 1)) with
  | None -> locate (vars, params, imp)
  | Some n -> n end
let rec argOrder =
  begin function
  | (Varg (l_), p_, n) -> O.Arg (locate (l_, p_, n))
  | (Simul (l_), p_, n) -> O.Simul (argOrderL (l_, p_, n))
  | (Lex (l_), p_, n) -> O.Lex (argOrderL (l_, p_, n)) end
let rec argOrderL =
  begin function
  | ([], p_, n) -> []
  | ((o_)::l_, p_, n) -> (::) (argOrder (o_, p_, n)) argOrderL (l_, p_, n) end
let rec argOrderMutual =
  begin function
  | ([], k, a_) -> a_
  | ((p_)::l_, k, a_) -> argOrderMutual (l_, k, (k (p_, a_))) end
let rec installOrder =
  begin function
  | (_, [], _) -> ()
  | (o_, ((a, p_) as aP)::thmsLE, thmsLT) ->
      let m'_ =
        argOrderMutual
          (thmsLE, (begin function | ((a, _), l_) -> O.LE (a, l_) end),
          (argOrderMutual
             ((aP :: thmsLT),
               (begin function | ((a, _), l_) -> O.LT (a, l_) end), O.Empty))) in
let o'_ = argOrder (o_, p_, (I.constImp a)) in
let s'_ = O.install (a, (O.TDec (o'_, m'_))) in
installOrder (o_, thmsLE, (aP :: thmsLT)) end
let rec installDecl (o_, Callpats (l_)) =
  begin installOrder (o_, l_, []); map (begin function | (a, _) -> a end) l_ end
let rec installTerminates (TDecl (t_), rrs) =
  begin wf (t_, rrs); installDecl t_ end
let rec uninstallTerminates cid = O.uninstall cid
let rec installTotal (TDecl (t_), rrs) =
  begin wf (t_, rrs); installDecl t_ end
let rec uninstallTotal cid = O.uninstall cid
let rec argROrder =
  begin function
  | (Varg (l_), p_, n) -> O.Arg (locate (l_, p_, n))
  | (Simul (l_), p_, n) -> O.Simul (argROrderL (l_, p_, n))
  | (Lex (l_), p_, n) -> O.Lex (argROrderL (l_, p_, n)) end
let rec argROrderL =
  begin function
  | ([], p_, n) -> []
  | ((o_)::l_, p_, n) -> (::) (argROrder (o_, p_, n)) argROrderL (l_, p_, n) end
let rec argPredicate =
  begin function
  | (L.Less, o_, o'_) -> O.Less (o_, o'_)
  | (L.Leq, o_, o'_) -> O.Leq (o_, o'_)
  | (L.Eq, o_, o'_) -> O.Eq (o_, o'_) end
let rec installPredicate =
  begin function
  | (_, [], _) -> ()
  | (RedOrder (Pred, o1_, o2_), ((a, p_) as aP)::thmsLE, thmsLT) ->
      let m'_ =
        argOrderMutual
          (thmsLE, (begin function | ((a, _), l_) -> O.LE (a, l_) end),
          (argOrderMutual
             ((aP :: thmsLT),
               (begin function | ((a, _), l_) -> O.LT (a, l_) end), O.Empty))) in
let O1' = argROrder (o1_, p_, (I.constImp a)) in
let O2' = argROrder (o2_, p_, (I.constImp a)) in
let pr = argPredicate (Pred, O1', O2') in
let S'' = O.installROrder (a, (O.RDec (pr, m'_))) in
((installPredicate ((L.RedOrder (Pred, o1_, o2_)), thmsLE, (aP :: thmsLT)))
  (* install termination order *)(* bug: %reduces should not entail %terminates *)
  (* fixed: Sun Mar 13 09:41:18 2005 -fp *)(* val S'  = O.install (a, O.TDec (O2', M')) *)
  (* install reduction order   *)) end
let rec installRDecl (r_, Callpats (l_)) =
  begin installPredicate (r_, l_, []);
  map (begin function | (a, _) -> a end)
  l_ end
let rec wfRCallpats (l0_, c0_, r) =
  let rec makestring =
    begin function
    | [] -> ""
    | s::[] -> s
    | s::l_ -> (s ^ " ") ^ (makestring l_) end in
let rec exists' =
  begin function
  | (x, []) -> false
  | (x, (None)::l_) -> exists' (x, l_)
  | (x, (Some y)::l_) -> if x = y then begin true end
      else begin exists' (x, l_) end end in
let rec delete =
begin function
| (x, ((a, p_) as aP)::c_) -> if exists' (x, p_) then begin c_ end
    else begin (::) aP delete (x, c_) end
| (x, []) -> error (r, (("Variable " ^ x) ^ " does not occur as argument")) end in
let rec wfCallpats' =
begin function
| ([], []) -> ()
| (x::l_, c_) -> wfCallpats' (l_, (delete (x, c_)))
| _ ->
    error
      (r,
        (((^) "Mutual argument (" makestring l0_) ^
           ") does not cover all call patterns")) end in
wfCallpats' (l0_, c0_)
let rec wfred ((RedOrder (Pred, o_, o'_), Callpats (c_)), (r, rs)) =
  let rec wfOrder =
    begin function | Varg (l_) -> (begin wfRCallpats (l_, c_, r); Varg end)
    | Lex (l_) -> Lex (wfOrders l_) | Simul (l_) -> Simul (wfOrders l_) end
  and wfOrders =
    begin function | [] -> [] | (o_)::l_ -> (wfOrder o_) :: (wfOrders l_) end in
begin uniqueCallpats (c_, rs);
if (=) (wfOrder o_) wfOrder o'_ then begin () end
else begin
error
  (r,
    (((^) "Reduction Order (" P.ROrderToString (L.RedOrder (Pred, o_, o'_)))
       ^ ") requires both orders to be of the same type.")) end end
let rec installReduces (RDecl (r_, c_), rrs) =
  begin wfred ((r_, c_), rrs); installRDecl (r_, c_) end
let rec uninstallReduces cid = O.uninstallROrder cid
let rec installTabled (TabledDecl cid) = TabledSyn.installTabled cid
let rec installKeepTable (KeepTableDecl cid) = TabledSyn.installKeepTable cid
let installTotal = installTotal
let uninstallTotal = uninstallTotal
let installTerminates = installTerminates
let uninstallTerminates = uninstallTerminates
let installReduces = installReduces
let uninstallReduces = uninstallReduces
let installTabled = installTabled
let installKeepTable = installKeepTable end



module ThmSyn =
  (ThmSyn)(struct
                  module Abstract = Abstract
                  module Whnf = Whnf
                  module Paths' = Paths
                  module Names' = Names
                end)
module ThmPrint =
  (ThmPrint)(struct
                    module ThmSyn' = ThmSyn
                    module Formatter = Formatter
                  end)
module Thm =
  (Thm)(struct
               module Global = Global
               module ThmSyn' = ThmSyn
               module TabledSyn = TabledSyn
               module Order = Order
               module ModeTable = ModeTable
               module ThmPrint = ThmPrint
               module Paths' = Paths
             end)