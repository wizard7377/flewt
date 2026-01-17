
module type STATESYN  =
  sig
    type __Order =
      | Arg of
      ((((IntSyn.__Exp)(* Orders                     *)
      (*! structure FunSyn : FUNSYN !*)(*! structure IntSyn : INTSYN !*)
      (* Author: Carsten Schuermann *)(* State definition for Proof Search *))
      * IntSyn.__Sub) * (IntSyn.__Exp * IntSyn.__Sub)) 
      | Lex of ((__Order)(* O ::= U[s] : V[s]          *))
      list 
      | Simul of ((__Order)(*     | (O1 .. On)           *))
      list 
      | All of
      (((IntSyn.__Dec)(*     | {O1 .. On}           *)) *
      __Order) 
      | And of (((__Order)(*     | {{D}} O              *))
      * __Order) 
    type __Info =
      | Splits of ((int)(*     | O1 ^ O2              *)) 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of
      (((int)(* S = <n, (g, B), (IH, OH), d, O, H, F> *)) *
      (((IntSyn.dctx)(* Part of theorem                   *))
      *
      ((__Tag)(* Context of Hypothesis, in general not named *))
      IntSyn.__Ctx) *
      (((FunSyn.__For)(* Status information *)) * __Order) *
      ((int)(* Induction hypothesis, order       *)) *
      ((__Order)(* length of meta context            *)) *
      (((int)(* Current order *)) * FunSyn.__For) list *
      ((FunSyn.__For)(* History of residual lemmas *))) 
    val orderSub :
      (__Order * IntSyn.__Sub) -> ((__Order)(* Formula *))
    val decrease : __Tag -> __Tag
    val splitDepth : __Info -> int
    val normalizeOrder : __Order -> __Order
    val convOrder : (__Order * __Order) -> bool
    val normalizeTag : (__Tag * IntSyn.__Sub) -> __Tag
  end;;




module StateSyn(StateSyn:sig
                           module Whnf : WHNF
                           module Conv :
                           ((CONV)(* State for Proof Search *)(* Author: Carsten Schuermann *)
                           (*! structure IntSyn' : INTSYN !*)(*! structure FunSyn' : FUNSYN !*)
                           (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                           (*! sharing Whnf.IntSyn = IntSyn' !*))
                         end) : STATESYN =
  struct
    type __Order =
      | Arg of
      ((((IntSyn.__Exp)(* Orders                     *)
      (*! structure FunSyn = FunSyn' !*)(*! structure IntSyn = IntSyn' !*)
      (*! sharing Conv.IntSyn = IntSyn' !*)) * IntSyn.__Sub)
      * (IntSyn.__Exp * IntSyn.__Sub)) 
      | Lex of ((__Order)(* O ::= U[s] : V[s]          *))
      list 
      | Simul of ((__Order)(*     | (O1 .. On)           *))
      list 
      | All of
      (((IntSyn.__Dec)(*     | {O1 .. On}           *)) *
      __Order) 
      | And of (((__Order)(*     | {{D}} O              *))
      * __Order) 
    type __Info =
      | Splits of ((int)(*     | O1 ^ O2              *)) 
      | RL 
      | RLdone 
    type __Tag =
      | Parameter of FunSyn.label option 
      | Lemma of __Info 
      | None 
    type __State =
      | State of
      (((int)(* S = <n, (g, B), (IH, OH), d, O, H, F> *)) *
      (((IntSyn.dctx)(* Part of theorem                   *))
      *
      ((__Tag)(* Context of Hypothesis in general not named *))
      IntSyn.__Ctx) *
      (((FunSyn.__For)(* Status information *)) * __Order) *
      ((int)(* Induction hypothesis, order       *)) *
      ((__Order)(* length of meta context            *)) *
      (((int)(* Current Order *)) * FunSyn.__For) list *
      ((FunSyn.__For)(* History of residual lemmas *))) 
    module F = FunSyn
    module I = IntSyn
    let rec orderSub =
      function
      | (Arg ((U, s1), (V, s2)), s) ->
          Arg ((U, (I.comp (s1, s))), (V, (I.comp (s2, s))))
      | (Lex (Os), s) -> Lex (map (function | O -> orderSub (O, s)) Os)
      | (Simul (Os), s) -> Simul (map (function | O -> orderSub (O, s)) Os)
    let rec normalizeOrder =
      function
      | Arg (Us, Vs) ->
          Arg (((Whnf.normalize Us), I.id), ((Whnf.normalize Vs), I.id))
      | Lex (Os) -> Lex (map normalizeOrder Os)
      | Simul (Os) -> Simul (map normalizeOrder Os)
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
    let ((orderSub)(* Formula *)(* orderSub (O, s) = O'

       Invariant:
       If   g' |- O order    and    g |- s : g'
       then g |- O' order
       and  g |- O' == O[s] order
    *)
      (* by invariant: no case for All and And *)(* normalizeOrder (O) = O'

       Invariant:
       If   g |- O order
       then g |- O' order
       and  g |- O = O' order
       and  each sub term of O' is in normal form.
    *)
      (* by invariant: no case for All and And *)(* convOrder (O1, O2) = B'

       Invariant:
       If   g |- O1 order
       and  g |- O2 order
       then B' holds iff g |- O1 == O2 order
    *)
      (* by invariant: no case for All and And *)(* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
      (* decrease (Assumption k) = Assumption (k-1)
      | *)(* normalizeTag (T, s) = T'

       Invariant:
       If   g |- T : tag
            g' |- s : g
       then g' |- T' = T[s] tag
    *))
      = orderSub
    let decrease = decrease
    let splitDepth = splitDepth
    let normalizeOrder = normalizeOrder
    let convOrder = convOrder
    let normalizeTag = normalizeTag
  end ;;
