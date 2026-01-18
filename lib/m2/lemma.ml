
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
      | Prefix (Decl (G, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) in
          ((M.Prefix
              ((I.Decl (G', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (G, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) in
          let X = I.newEVar (G', (I.EClo (V, s'))) in
          ((M.Prefix (G', M', B')), (I.Dot ((I.Exp X), s')))
    let rec apply (State (name, GM, V), a) =
      let ((Prefix (G', M', B') as GM'), s') = createEVars GM in
      let (U', Vs') = M.createAtomConst (G', (I.Const a)) in
      A.abstract
        (M.State
           (name, GM',
             (I.Pi
                (((I.Dec (NONE, U')), I.No),
                  (I.EClo (V, (I.comp (s', I.shift))))))))
    (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for M' and B'.
    *)
    (* apply (((G, M), V), a) = ((G', M'), V')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- S' : Va > type
       and  G' |- s' : G
       and  G' |- V' = {a S'}. V[s' o ^]
       and  ((G', M'), V') is a state
    *)
    (* Vs' = type *)
    let apply = apply
  end ;;
