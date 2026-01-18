
(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module type STATESYN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure FunSyn : FUNSYN !*)
    type __Order =
      | Arg of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) 
      | Lex of __Order list 
      | Simul of __Order list 
      | All of (IntSyn.__Dec * __Order) 
      | And of (__Order * __Order) 
    (*     | O1 ^ O2              *)
    type __Info =
      | Splits of int 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of (int * (IntSyn.dctx * __Tag IntSyn.__Ctx) * (FunSyn.__For *
      __Order) * int * __Order * (int * FunSyn.__For) list * FunSyn.__For) 
    (* Part of theorem                   *)
    (* Status information *)
    (* Induction hypothesis, order       *)
    (* length of meta context            *)
    (* Current order *)
    (* History of residual lemmas *)
    (* Context of Hypothesis, in general not named *)
    (* Formula *)
    val orderSub : (__Order * IntSyn.__Sub) -> __Order
    val decrease : __Tag -> __Tag
    val splitDepth : __Info -> int
    val normalizeOrder : __Order -> __Order
    val convOrder : (__Order * __Order) -> bool
    val normalizeTag : (__Tag * IntSyn.__Sub) -> __Tag
  end;;




(* State for Proof Search *)
(* Author: Carsten Schuermann *)
module StateSyn(StateSyn:sig
                           (*! structure IntSyn' : INTSYN !*)
                           (*! structure FunSyn' : FUNSYN !*)
                           (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                           module Whnf : WHNF
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           module Conv : CONV
                         end) : STATESYN =
  struct
    (*! sharing Conv.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure FunSyn = FunSyn' !*)
    type __Order =
      | Arg of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) 
      | Lex of __Order list 
      | Simul of __Order list 
      | All of (IntSyn.__Dec * __Order) 
      | And of (__Order * __Order) 
    (*     | O1 ^ O2              *)
    type __Info =
      | Splits of int 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of (int * (IntSyn.dctx * __Tag IntSyn.__Ctx) * (FunSyn.__For *
      __Order) * int * __Order * (int * FunSyn.__For) list * FunSyn.__For) 
    (* Part of theorem                   *)
    (* Status information *)
    (* Induction hypothesis, order       *)
    (* length of meta context            *)
    (* Current Order *)
    (* History of residual lemmas *)
    (* Context of Hypothesis in general not named *)
    (* Formula *)
    module F = FunSyn
    module I = IntSyn
    let rec orderSub =
      function
      | (Arg ((__u, s1), (__v, s2)), s) ->
          Arg ((__u, (I.comp (s1, s))), (__v, (I.comp (s2, s))))
      | (Lex (__Os), s) -> Lex (map (function | O -> orderSub (O, s)) __Os)
      | (Simul (__Os), s) -> Simul (map (function | O -> orderSub (O, s)) __Os)
    let rec normalizeOrder =
      function
      | Arg (__Us, __Vs) ->
          Arg (((Whnf.normalize __Us), I.id), ((Whnf.normalize __Vs), I.id))
      | Lex (__Os) -> Lex (map normalizeOrder __Os)
      | Simul (__Os) -> Simul (map normalizeOrder __Os)
    let rec convOrder =
      function
      | (Arg (us1, _), Arg (us2, _)) -> Conv.conv (us1, us2)
      | (Lex (Os1), Lex (Os2)) -> convOrders (Os1, Os2)
      | (Simul (Os1), Simul (Os2)) -> convOrders (Os1, Os2)
    let rec convOrders =
      function
      | (nil, nil) -> true__
      | ((O1)::L1, (O2)::L2) -> (convOrder (O1, O2)) && (convOrders (L1, L2))
    let rec decreaseInfo =
      function | Splits k -> Splits (k - 1) | RL -> RL | RLdone -> RLdone
    let rec decrease =
      function | Lemma (Sp) -> Lemma (decreaseInfo Sp) | None -> None
    let rec splitDepth (Splits k) = k
    let rec normalizeTag =
      function | ((Parameter _ as T), _) -> T | (Lemma (K), s) -> Lemma K
    (* orderSub (O, s) = O'

       Invariant:
       If   __g' |- O order    and    __g |- s : __g'
       then __g |- O' order
       and  __g |- O' == O[s] order
    *)
    (* by invariant: no case for All and And *)
    (* normalizeOrder (O) = O'

       Invariant:
       If   __g |- O order
       then __g |- O' order
       and  __g |- O = O' order
       and  each sub term of O' is in normal form.
    *)
    (* by invariant: no case for All and And *)
    (* convOrder (O1, O2) = B'

       Invariant:
       If   __g |- O1 order
       and  __g |- O2 order
       then B' holds iff __g |- O1 == O2 order
    *)
    (* by invariant: no case for All and And *)
    (* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
    (* decrease (Assumption k) = Assumption (k-1)
      | *)
    (* normalizeTag (T, s) = T'

       Invariant:
       If   __g |- T : tag
            __g' |- s : __g
       then __g' |- T' = T[s] tag
    *)
    let orderSub = orderSub
    let decrease = decrease
    let splitDepth = splitDepth
    let normalizeOrder = normalizeOrder
    let convOrder = convOrder
    let normalizeTag = normalizeTag
  end ;;
