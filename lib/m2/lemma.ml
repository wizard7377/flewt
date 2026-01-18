
(* Lemma *)
(* Author: Carsten Schuermann *)
module type LEMMA  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val apply : (MetaSyn.__State * IntSyn.cid) -> MetaSyn.__State
  end;;




(* Lemma *)
(* Author: Carsten Schuermann *)
module Lemma(Lemma:sig
                     module MetaSyn' : METASYN
                     module MetaAbstract : METAABSTRACT
                   end) : LEMMA =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module A = MetaAbstract
    module M = MetaSyn
    module I = IntSyn
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (__g, __d), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (__g', M', B'), s') = createEVars (M.Prefix (__g, M, B)) in
          ((M.Prefix
              ((I.Decl (__g', (I.decSub (__d, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (__g, Dec (_, __v)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (__g', M', B'), s') = createEVars (M.Prefix (__g, M, B)) in
          let x = I.newEVar (__g', (I.EClo (__v, s'))) in
          ((M.Prefix (__g', M', B')), (I.Dot ((I.Exp x), s')))
    let rec apply (State (name, GM, __v), a) =
      let ((Prefix (__g', M', B') as GM'), s') = createEVars GM in
      let (__u', __Vs') = M.createAtomConst (__g', (I.Const a)) in
      A.abstract
        (M.State
           (name, GM',
             (I.Pi
                (((I.Dec (None, __u')), I.No),
                  (I.EClo (__v, (I.comp (s', I.shift))))))))
    (* createEVars (__g, M, B) = ((__g', M', B'), s')

       Invariant:
       If   |- __g ctx
       then |- __g' ctx
       and  . |- s' : __g
       M and B are mode and bound contexts matching __g, and similarly for M' and B'.
    *)
    (* apply (((__g, M), __v), a) = ((__g', M'), __v')

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- __g' ctx
       and  __g' |- M' mtx
       and  __g' |- S' : Va > type
       and  __g' |- s' : __g
       and  __g' |- __v' = {a S'}. __v[s' o ^]
       and  ((__g', M'), __v') is a state
    *)
    (* __Vs' = type *)
    let apply = apply
  end ;;
