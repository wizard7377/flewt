
(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGAUNIFY  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    exception Unify of string 
    val unifyFor :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__For * Tomega.__For) -> unit
  end;;




(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
module TomegaUnify(TomegaUnify:sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure Tomega' : TOMEGA !*)
                                 (*! sharing Tomega'.IntSyn = IntSyn' !*)
                                 module Abstract : ABSTRACT
                                 module TypeCheck : TYPECHECK
                                 module Conv : CONV
                                 module Normalize : NORMALIZE
                                 module Whnf : WHNF
                                 module Print : PRINT
                                 module TomegaPrint : TOMEGAPRINT
                                 module Subordinate : SUBORDINATE
                                 (*! sharing Abstract.IntSyn = IntSyn' !*)
                                 (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                                 (*! sharing Conv.IntSyn = IntSyn' !*)
                                 (*! sharing Normalize.IntSyn = IntSyn' !*)
                                 (*! sharing Normalize.Tomega = Tomega' !*)
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Print.IntSyn = IntSyn' !*)
                                 (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
                                 (*! sharing TomegaPrint.Tomega = Tomega' !*)
                                 (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                 module Weaken : WEAKEN
                               end) : TOMEGAUNIFY =
  struct
    (*! sharing Weaken.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    exception Unify of string 
    module I = IntSyn
    module T = Tomega
    let rec unifyFor (Psi, F1, F2) =
      unifyForN (Psi, (T.forSub (F1, T.id)), (T.forSub (F2, T.id)))
    let rec unifyForN =
      function
      | (Psi, T.True, T.True) -> ()
      | (Psi, Ex ((D1, _), F1), Ex ((D2, _), F2)) ->
          (unifyDec (Psi, (T.UDec D1), (T.UDec D2));
           unifyFor ((I.Decl (Psi, (T.UDec D1))), F1, F2))
      | (Psi, All ((D1, _), F1), All ((D2, _), F2)) ->
          (unifyDec (Psi, D1, D2); unifyFor ((I.Decl (Psi, D1)), F1, F2))
      | (Psi, FVar (_, r), F) -> (:=) r SOME F
      | (Psi, F, FVar (_, r)) -> (:=) r SOME F
      | (Psi, _, _) -> raise (Unify "Formula mismatch")
    let rec unifyDec =
      function
      | (Psi, UDec (D1), UDec (D2)) ->
          if Conv.convDec ((D1, I.id), (D2, I.id))
          then ()
          else raise (Unify "Declaration mismatch")
      | (Psi, PDec (_, F1), PDec (_, F2)) -> unifyFor (Psi, F1, F2)
    (* unifyFor (Psi, F1, F2) = R

       Invariant:
       If   F1, F2 contain free variables X1 ... Xn
       and  Psi |- F1 for
       and  Psi |- F2 for
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- F1[I] = F2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
    (* unifyDec (Psi, D1, D2) = R

       Invariant:
       If   D1, D2 contain free variables X1 ... Xn
       and  Psi |- D1 dec
       and  Psi |- D2 dec
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- D1[I] = D2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
    let unifyFor = unifyFor
  end ;;
