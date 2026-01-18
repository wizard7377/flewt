
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
    let rec strengthenExp (__u, s) =
      Whnf.normalize ((Whnf.cloInv (__u, s)), I.id)
    let rec strengthenDec (Dec (name, __v), s) =
      I.Dec (name, (strengthenExp (__v, s)))
    let rec strengthenCtx =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__g, __d), s) ->
          let (__g', s') = strengthenCtx (__g, s) in
          ((I.Decl (__g', (strengthenDec (__d, s')))), (I.dot1 s'))
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)
    let rec strengthenSpine =
      function
      | (I.Nil, t) -> I.Nil
      | (App (__u, S), t) ->
          I.App ((strengthenExp (__u, t)), (strengthenSpine (S, t)))
    (* strengthenExp (__u, s) = __u'

       Invariant:
       If   __g |- s : __g'
       and  __g |- __u : __v
       then __g' |- __u' = __u[s^-1] : __v [s^-1]
    *)
    (* strengthenDec (x:__v, s) = x:__v'

       Invariant:
       If   __g |- s : __g'
       and  __g |- __v : __l
       then __g' |- __v' = __v[s^-1] : __l
    *)
    (* strengthenCtx (__g, s) = (__g', s')

       If   G0 |- __g ctx
       and  G0 |- s G1
       then G1 |- __g' = __g[s^-1] ctx
       and  G0 |- s' : G1, __g'
    *)
    let strengthenExp = strengthenExp
    let strengthenSpine = strengthenSpine
    let strengthenDec = strengthenDec
    let strengthenCtx = strengthenCtx
    let strengthenSub = strengthenSub
  end ;;
