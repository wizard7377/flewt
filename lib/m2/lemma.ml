module type LEMMA  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val apply : (MetaSyn.state_ * IntSyn.cid) -> MetaSyn.state_
  end


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
      begin function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (g_, d_), Decl (m_, M.Top), Decl (b_, b)) ->
          let (Prefix (g'_, m'_, b'_), s') =
            createEVars (M.Prefix (g_, m_, b_)) in
          ((M.Prefix
              ((I.Decl (g'_, (I.decSub (d_, s')))), (I.Decl (m'_, M.Top)),
                (I.Decl (b'_, b)))), (I.dot1 s'))
      | Prefix (Decl (g_, Dec (_, v_)), Decl (m_, M.Bot), Decl (b_, _)) ->
          let (Prefix (g'_, m'_, b'_), s') =
            createEVars (M.Prefix (g_, m_, b_)) in
          let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
          ((M.Prefix (g'_, m'_, b'_)), (I.Dot ((I.Exp x_), s'))) end
    let rec apply (State (name, GM, v_), a) =
      let ((Prefix (g'_, m'_, b'_) as GM'), s') = createEVars GM in
      let (u'_, vs'_) = M.createAtomConst (g'_, (I.Const a)) in
      ((A.abstract
          (M.State
             (name, GM',
               (I.Pi
                  (((I.Dec (None, u'_)), I.No),
                    (I.EClo (v_, (I.comp (s', I.shift)))))))))
        (* Vs' = type *))
    let apply = apply end 