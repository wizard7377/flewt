
module type LEMMA  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val apply : MetaSyn.__State -> IntSyn.cid -> MetaSyn.__State
  end;;




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
      | Prefix (Decl (__G, __D), Decl (__M, M.Top), Decl (__B, b)) ->
          let (Prefix (__G', __M', __B'), s') =
            createEVars (M.Prefix (__G, __M, __B)) in
          ((M.Prefix
              ((I.Decl (__G', (I.decSub (__D, s')))), (I.Decl (__M', M.Top)),
                (I.Decl (__B', b)))), (I.dot1 s'))
      | Prefix (Decl (__G, Dec (_, __V)), Decl (__M, M.Bot), Decl (__B, _))
          ->
          let (Prefix (__G', __M', __B'), s') =
            createEVars (M.Prefix (__G, __M, __B)) in
          let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
          ((M.Prefix (__G', __M', __B')), (I.Dot ((I.Exp __X), s')))
    let rec apply (State (name, GM, __V)) a =
      let ((Prefix (__G', __M', __B') as GM'), s') = createEVars GM in
      let (__U', __Vs') = M.createAtomConst (__G', (I.Const a)) in
      ((A.abstract
          (M.State
             (name, GM',
               (I.Pi
                  (((I.Dec (NONE, __U')), I.No),
                    (I.EClo (__V, (I.comp (s', I.shift)))))))))
        (* Vs' = type *))
    let apply = apply
  end ;;
