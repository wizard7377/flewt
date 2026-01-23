module type STATESYN  =
  sig
    type order_ =
      | Arg of ((IntSyn.exp_ * IntSyn.sub_) * (IntSyn.exp_ * IntSyn.sub_)) 
      | Lex of order_ list 
      | Simul of order_ list 
      | All of (IntSyn.dec_ * order_) 
      | And of (order_ * order_) 
    type info_ =
      | Splits of int 
      | RL 
      | RLdone 
    type tag_ =
      | Parameter of FunSyn.label option 
      | Lemma of info_ 
      | None 
    type state_ =
      | State of
      (((int *
          (((IntSyn.dctx * tag_ IntSyn.ctx_))(* Context of Hypothesis, in general not named *))
          * (FunSyn.for_ * order_) * int * order_ * (int * FunSyn.for_) list
          * FunSyn.for_))(* History of residual lemmas *)
      (* Current order *)(* length of meta context            *)
      (* Induction hypothesis, order       *)(* Status information *)
      (* Part of theorem                   *)) 
    val orderSub : (order_ * IntSyn.sub_) -> order_
    val decrease : tag_ -> tag_
    val splitDepth : info_ -> int
    val normalizeOrder : order_ -> order_
    val convOrder : (order_ * order_) -> bool
    val normalizeTag : (tag_ * IntSyn.sub_) -> tag_
  end


module StateSyn(StateSyn:sig module Whnf : WHNF module Conv : CONV end) :
  STATESYN =
  struct
    type order_ =
      | Arg of ((IntSyn.exp_ * IntSyn.sub_) * (IntSyn.exp_ * IntSyn.sub_)) 
      | Lex of order_ list 
      | Simul of order_ list 
      | All of (IntSyn.dec_ * order_) 
      | And of (order_ * order_) 
    type info_ =
      | Splits of int 
      | RL 
      | RLdone 
    type tag_ =
      | Parameter of FunSyn.label option 
      | Lemma of info_ 
      | None 
    type state_ =
      | State of
      (((int *
          (((IntSyn.dctx * tag_ IntSyn.ctx_))(* Context of Hypothesis in general not named *))
          * (FunSyn.for_ * order_) * int * order_ * (int * FunSyn.for_) list
          * FunSyn.for_))(* History of residual lemmas *)
      (* Current Order *)(* length of meta context            *)
      (* Induction hypothesis, order       *)(* Status information *)
      (* Part of theorem                   *)) 
    module F = FunSyn
    module I = IntSyn
    let rec orderSub =
      begin function
      | (Arg ((u_, s1), (v_, s2)), s) ->
          Arg ((u_, (I.comp (s1, s))), (v_, (I.comp (s2, s))))
      | (Lex (os_), s) ->
          Lex (map (begin function | o_ -> orderSub (o_, s) end) os_)
      | (Simul (os_), s) ->
          Simul (map (begin function | o_ -> orderSub (o_, s) end) os_) end
let rec normalizeOrder =
  begin function
  | Arg (us_, vs_) ->
      Arg (((Whnf.normalize us_), I.id), ((Whnf.normalize vs_), I.id))
  | Lex (os_) -> Lex (map normalizeOrder os_)
  | Simul (os_) -> Simul (map normalizeOrder os_) end
let rec convOrder =
  begin function
  | (Arg (us1_, _), Arg (us2_, _)) -> Conv.conv (us1_, us2_)
  | (Lex (os1_), Lex (os2_)) -> convOrders (os1_, os2_)
  | (Simul (os1_), Simul (os2_)) -> convOrders (os1_, os2_) end
let rec convOrders =
  begin function
  | ([], []) -> true
  | ((o1_)::l1_, (o2_)::l2_) ->
      (convOrder (o1_, o2_)) && (convOrders (l1_, l2_)) end
let rec decreaseInfo =
  begin function | Splits k -> Splits (k - 1) | RL -> RL | RLdone -> RLdone end
let rec decrease =
  begin function | Lemma (Sp) -> Lemma (decreaseInfo Sp) | None -> None end
let rec splitDepth (Splits k) = k
let rec normalizeTag =
  begin function
  | ((Parameter _ as t_), _) -> t_
  | (Lemma (k_), s) -> Lemma k_ end
let orderSub = orderSub
let decrease = decrease
let splitDepth = splitDepth
let normalizeOrder = normalizeOrder
let convOrder = convOrder
let normalizeTag = normalizeTag end
