module type TOMEGAUNIFY  =
  sig
    exception Unify of string 
    val unifyFor :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.for_ * Tomega.for_) -> unit
  end


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
    let rec unifyFor (Psi, f1_, f2_) =
      unifyForN (Psi, (T.forSub (f1_, T.id)), (T.forSub (f2_, T.id)))
    let rec unifyForN =
      begin function
      | (Psi, T.True, T.True) -> ()
      | (Psi, Ex ((d1_, _), f1_), Ex ((d2_, _), f2_)) ->
          (begin unifyDec (Psi, (T.UDec d1_), (T.UDec d2_));
           unifyFor ((I.Decl (Psi, (T.UDec d1_))), f1_, f2_) end)
      | (Psi, All ((d1_, _), f1_), All ((d2_, _), f2_)) ->
          (begin unifyDec (Psi, d1_, d2_);
           unifyFor ((I.Decl (Psi, d1_)), f1_, f2_) end)
      | (Psi, FVar (_, r), f_) -> (:=) r Some f_
      | (Psi, f_, FVar (_, r)) -> (:=) r Some f_
      | (Psi, _, _) -> raise (Unify "Formula mismatch") end
let rec unifyDec =
  begin function
  | (Psi, UDec (d1_), UDec (d2_)) ->
      if Conv.convDec ((d1_, I.id), (d2_, I.id)) then begin () end
      else begin raise (Unify "Declaration mismatch") end
  | (Psi, PDec (_, f1_), PDec (_, f2_)) -> unifyFor (Psi, f1_, f2_) end
let unifyFor = unifyFor end
