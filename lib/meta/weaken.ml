
(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module type WEAKEN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    val strengthenExp : (IntSyn.__Exp * IntSyn.__Sub) -> IntSyn.__Exp
    val strengthenSpine : (IntSyn.__Spine * IntSyn.__Sub) -> IntSyn.__Spine
    val strengthenCtx :
      (IntSyn.dctx * IntSyn.__Sub) -> (IntSyn.dctx * IntSyn.__Sub)
    val strengthenDec : (IntSyn.__Dec * IntSyn.__Sub) -> IntSyn.__Dec
    val strengthenSub : (IntSyn.__Sub * IntSyn.__Sub) -> IntSyn.__Sub
  end;;




(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module Weaken(Weaken:sig
                       (*! structure IntSyn' : INTSYN !*)
                       module Whnf : WHNF
                     end) : WEAKEN =
  struct
    (*! sharing Whnf.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module I = IntSyn
    let rec strengthenExp (U, s) =
      Whnf.normalize ((Whnf.cloInv (U, s)), I.id)
    let rec strengthenDec (Dec (name, V), s) =
      I.Dec (name, (strengthenExp (V, s)))
    let rec strengthenCtx =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (G, D), s) ->
          let (G', s') = strengthenCtx (G, s) in
          ((I.Decl (G', (strengthenDec (D, s')))), (I.dot1 s'))
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)
    let rec strengthenSpine =
      function
      | (I.Nil, t) -> I.Nil
      | (App (U, S), t) ->
          I.App ((strengthenExp (U, t)), (strengthenSpine (S, t)))
    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- s G1
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'
    *)
    let strengthenExp = strengthenExp
    let strengthenSpine = strengthenSpine
    let strengthenDec = strengthenDec
    let strengthenCtx = strengthenCtx
    let strengthenSub = strengthenSub
  end ;;
