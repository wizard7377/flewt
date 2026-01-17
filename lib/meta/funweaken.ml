
module type FUNWEAKEN  =
  sig
    val strengthenPsi :
      (FunSyn.lfctx * IntSyn.__Sub) ->
        (((FunSyn.lfctx)(*! structure FunSyn : FUNSYN !*)
          (* Author: Carsten Schuermann *)(* Weakening substitutions for meta substitutions *))
          * IntSyn.__Sub)
    val strengthenPsi' :
      (FunSyn.__LFDec list * IntSyn.__Sub) ->
        (FunSyn.__LFDec list * IntSyn.__Sub)
  end;;




module FunWeaken(FunWeaken:sig
                             module Weaken :
                             ((WEAKEN)(* Weakening substitutions for meta substitutions *)
                             (* Author: Carsten Schuermann *)(*! structure FunSyn' : FUNSYN !*))
                           end) : FUNWEAKEN =
  struct
    module F = FunSyn
    module I = IntSyn
    let rec strengthenPsi =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, Prim (D)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (F.Prim (Weaken.strengthenDec (D, s'))))),
            (I.dot1 s'))
      | (Decl (Psi, Block (CtxBlock (l, G))), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          let (G'', s'') = Weaken.strengthenCtx (G, s') in
          ((I.Decl (Psi', (F.Block (F.CtxBlock (l, G''))))), s'')
    let rec strengthenPsi' =
      function
      | (nil, s) -> (nil, s)
      | ((Prim (D))::Psi, s) ->
          let D' = Weaken.strengthenDec (D, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Prim D') :: Psi''), s'')
      | ((Block (CtxBlock (l, G)))::Psi, s) ->
          let (G', s') = Weaken.strengthenCtx (G, s) in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Block (F.CtxBlock (l, G'))) :: Psi''), s'')
    let ((strengthenPsi)(*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
      (*! structure FunSyn = FunSyn' !*)(* strengthenPsi (Psi, s) = (Psi', s')

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
    *))
      = strengthenPsi
    let strengthenPsi' = strengthenPsi'
  end ;;
