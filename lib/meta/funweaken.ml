
module type FUNWEAKEN  =
  sig
    val strengthenPsi :
      FunSyn.lfctx -> IntSyn.__Sub -> (FunSyn.lfctx * IntSyn.__Sub)
    val strengthenPsi' :
      FunSyn.__LFDec list ->
        IntSyn.__Sub -> (FunSyn.__LFDec list * IntSyn.__Sub)
  end;;




module FunWeaken(FunWeaken:sig module Weaken : WEAKEN end) : FUNWEAKEN =
  struct
    module F = FunSyn
    module I = IntSyn
    let rec strengthenPsi __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, Prim (__D)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (F.Prim (Weaken.strengthenDec (__D, s'))))),
            (I.dot1 s'))
      | (Decl (Psi, Block (CtxBlock (l, __G))), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          let (G'', s'') = Weaken.strengthenCtx (__G, s') in
          ((I.Decl (Psi', (F.Block (F.CtxBlock (l, G''))))), s'')
    let rec strengthenPsi' __2__ __3__ =
      match (__2__, __3__) with
      | (nil, s) -> (nil, s)
      | ((Prim (__D))::Psi, s) ->
          let __D' = Weaken.strengthenDec (__D, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Prim __D') :: Psi''), s'')
      | ((Block (CtxBlock (l, __G)))::Psi, s) ->
          let (__G', s') = Weaken.strengthenCtx (__G, s) in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Block (F.CtxBlock (l, __G'))) :: Psi''), s'')
    let strengthenPsi = strengthenPsi
    let strengthenPsi' = strengthenPsi'
  end ;;
