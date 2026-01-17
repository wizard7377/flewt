
module type LEMMA  =
  sig
    module MetaSyn :
    ((METASYN)(* Lemma *)(* Author: Carsten Schuermann *))
    exception Error of string 
    val apply : (MetaSyn.__State * IntSyn.cid) -> MetaSyn.__State
  end;;




module Lemma(Lemma:sig
                     module MetaSyn' : METASYN
                     module MetaAbstract :
                     ((METAABSTRACT)(* Lemma *)(* Author: Carsten Schuermann *))
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
      | Prefix (Decl (g, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (g', M', B'), s') = createEVars (M.Prefix (g, M, B)) in
          ((M.Prefix
              ((I.Decl (g', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (g, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (g', M', B'), s') = createEVars (M.Prefix (g, M, B)) in
          let X = I.newEVar (g', (I.EClo (V, s'))) in
          ((M.Prefix (g', M', B')), (I.Dot ((I.Exp X), s')))
    let rec apply (State (name, GM, V), a) =
      let ((Prefix (g', M', B') as GM'), s') = createEVars GM in
      let (U', Vs') = M.createAtomConst (g', (I.Const a)) in
      A.abstract
        (M.State
           (name, GM',
             (I.Pi
                (((I.Dec (NONE, U')), I.No),
                  (I.EClo (V, (I.comp (s', I.shift))))))))
    let ((apply)(* createEVars (g, M, B) = ((g', M', B'), s')

       Invariant:
       If   |- g ctx
       then |- g' ctx
       and  . |- s' : g
       M and B are mode and bound contexts matching g, and similarly for M' and B'.
    *)
      (* apply (((g, M), V), a) = ((g', M'), V')

       Invariant:
       If   |- g ctx
       and  g |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- g' ctx
       and  g' |- M' mtx
       and  g' |- S' : Va > type
       and  g' |- s' : g
       and  g' |- V' = {a S'}. V[s' o ^]
       and  ((g', M'), V') is a state
    *)
      (* Vs' = type *)) = apply
  end ;;
