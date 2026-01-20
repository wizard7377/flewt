
module type STATESYN  =
  sig
    type __Order =
      | Arg of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) 
      | Lex of __Order list 
      | Simul of __Order list 
      | All of (IntSyn.__Dec * __Order) 
      | And of (__Order * __Order) 
    type __Info =
      | Splits of int 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of
      (((int *
          (((IntSyn.dctx * __Tag IntSyn.__Ctx))(* Context of Hypothesis, in general not named *))
          * (FunSyn.__For * __Order) * int * __Order * (int * FunSyn.__For)
          list * FunSyn.__For))(* History of residual lemmas *)(* Current order *)
      (* length of meta context            *)(* Induction hypothesis, order       *)
      (* Status information *)(* Part of theorem                   *))
      
    val orderSub : __Order -> IntSyn.__Sub -> __Order
    val decrease : __Tag -> __Tag
    val splitDepth : __Info -> int
    val normalizeOrder : __Order -> __Order
    val convOrder : __Order -> __Order -> bool
    val normalizeTag : __Tag -> IntSyn.__Sub -> __Tag
  end;;




module StateSyn(StateSyn:sig module Whnf : WHNF module Conv : CONV end) :
  STATESYN =
  struct
    type __Order =
      | Arg of ((IntSyn.__Exp * IntSyn.__Sub) * (IntSyn.__Exp *
      IntSyn.__Sub)) 
      | Lex of __Order list 
      | Simul of __Order list 
      | All of (IntSyn.__Dec * __Order) 
      | And of (__Order * __Order) 
    type __Info =
      | Splits of int 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of
      (((int *
          (((IntSyn.dctx * __Tag IntSyn.__Ctx))(* Context of Hypothesis in general not named *))
          * (FunSyn.__For * __Order) * int * __Order * (int * FunSyn.__For)
          list * FunSyn.__For))(* History of residual lemmas *)(* Current Order *)
      (* length of meta context            *)(* Induction hypothesis, order       *)
      (* Status information *)(* Part of theorem                   *))
      
    module F = FunSyn
    module I = IntSyn
    let rec orderSub __0__ __1__ =
      match (__0__, __1__) with
      | (Arg ((__U, s1), (__V, s2)), s) ->
          Arg ((__U, (I.comp (s1, s))), (__V, (I.comp (s2, s))))
      | (Lex (__Os), s) -> Lex (map (fun (__O) -> orderSub (__O, s)) __Os)
      | (Simul (__Os), s) ->
          Simul (map (fun (__O) -> orderSub (__O, s)) __Os)
    let rec normalizeOrder =
      function
      | Arg (__Us, __Vs) ->
          Arg (((Whnf.normalize __Us), I.id), ((Whnf.normalize __Vs), I.id))
      | Lex (__Os) -> Lex (map normalizeOrder __Os)
      | Simul (__Os) -> Simul (map normalizeOrder __Os)
    let rec convOrder __2__ __3__ =
      match (__2__, __3__) with
      | (Arg (__Us1, _), Arg (__Us2, _)) -> Conv.conv (__Us1, __Us2)
      | (Lex (__Os1), Lex (__Os2)) -> convOrders (__Os1, __Os2)
      | (Simul (__Os1), Simul (__Os2)) -> convOrders (__Os1, __Os2)
    let rec convOrders __4__ __5__ =
      match (__4__, __5__) with
      | (nil, nil) -> true
      | ((__O1)::__L1, (__O2)::__L2) ->
          (convOrder (__O1, __O2)) && (convOrders (__L1, __L2))
    let rec decreaseInfo =
      function | Splits k -> Splits (k - 1) | RL -> RL | RLdone -> RLdone
    let rec decrease =
      function | Lemma (Sp) -> Lemma (decreaseInfo Sp) | None -> None
    let rec splitDepth (Splits k) = k
    let rec normalizeTag __6__ __7__ =
      match (__6__, __7__) with
      | ((Parameter _ as T), _) -> __T
      | (Lemma (__K), s) -> Lemma __K
    let orderSub = orderSub
    let decrease = decrease
    let splitDepth = splitDepth
    let normalizeOrder = normalizeOrder
    let convOrder = convOrder
    let normalizeTag = normalizeTag
  end ;;
