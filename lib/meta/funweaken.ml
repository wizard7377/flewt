
(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)
module type FUNWEAKEN  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    val strengthenPsi :
      (FunSyn.lfctx * IntSyn.__Sub) -> (FunSyn.lfctx * IntSyn.__Sub)
    val strengthenPsi' :
      (FunSyn.__LFDec list * IntSyn.__Sub) ->
        (FunSyn.__LFDec list * IntSyn.__Sub)
  end;;




(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)
module FunWeaken(FunWeaken:sig
                             (*! structure FunSyn' : FUNSYN !*)
                             module Weaken : WEAKEN
                           end) : FUNWEAKEN =
  struct
    (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
    (*! structure FunSyn = FunSyn' !*)
    module F = FunSyn
    module I = IntSyn
    let rec strengthenPsi =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, Prim (__d)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (F.Prim (Weaken.strengthenDec (__d, s'))))),
            (I.dot1 s'))
      | (Decl (Psi, Block (CtxBlock (l, __g))), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          let (__g'', s'') = Weaken.strengthenCtx (__g, s') in
          ((I.Decl (Psi', (F.Block (F.CtxBlock (l, __g''))))), s'')
    let rec strengthenPsi' =
      function
      | (nil, s) -> (nil, s)
      | ((Prim (__d))::Psi, s) ->
          let __d' = Weaken.strengthenDec (__d, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Prim __d') :: Psi''), s'')
      | ((Block (CtxBlock (l, __g)))::Psi, s) ->
          let (__g', s') = Weaken.strengthenCtx (__g, s) in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Block (F.CtxBlock (l, __g'))) :: Psi''), s'')
    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    let strengthenPsi = strengthenPsi
    let strengthenPsi' = strengthenPsi'
  end ;;
