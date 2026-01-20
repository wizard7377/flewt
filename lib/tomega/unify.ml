
module type TOMEGAUNIFY  =
  sig
    exception Unify of string 
    val unifyFor :
      Tomega.__Dec IntSyn.__Ctx -> Tomega.__For -> Tomega.__For -> unit
  end;;




module TomegaUnify(TomegaUnify:sig
                                 module Abstract : ABSTRACT
                                 module TypeCheck : TYPECHECK
                                 module Conv : CONV
                                 module Normalize : NORMALIZE
                                 module Whnf : WHNF
                                 module Print : PRINT
                                 module TomegaPrint : TOMEGAPRINT
                                 module Subordinate : SUBORDINATE
                                 module Weaken : WEAKEN
                               end) : TOMEGAUNIFY =
  struct
    exception Unify of string 
    module I = IntSyn
    module T = Tomega
    let rec unifyFor (Psi) (__F1) (__F2) =
      unifyForN (Psi, (T.forSub (__F1, T.id)), (T.forSub (__F2, T.id)))
    let rec unifyForN __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Psi, T.True, T.True) -> ()
      | (Psi, Ex ((__D1, _), __F1), Ex ((__D2, _), __F2)) ->
          (unifyDec (Psi, (T.UDec __D1), (T.UDec __D2));
           unifyFor ((I.Decl (Psi, (T.UDec __D1))), __F1, __F2))
      | (Psi, All ((__D1, _), __F1), All ((__D2, _), __F2)) ->
          (unifyDec (Psi, __D1, __D2);
           unifyFor ((I.Decl (Psi, __D1)), __F1, __F2))
      | (Psi, FVar (_, r), __F) -> (:=) r Some __F
      | (Psi, __F, FVar (_, r)) -> (:=) r Some __F
      | (Psi, _, _) -> raise (Unify "Formula mismatch")
    let rec unifyDec __3__ __4__ __5__ =
      match (__3__, __4__, __5__) with
      | (Psi, UDec (__D1), UDec (__D2)) ->
          if Conv.convDec ((__D1, I.id), (__D2, I.id))
          then ()
          else raise (Unify "Declaration mismatch")
      | (Psi, PDec (_, __F1), PDec (_, __F2)) -> unifyFor (Psi, __F1, __F2)
    let unifyFor = unifyFor
  end ;;
