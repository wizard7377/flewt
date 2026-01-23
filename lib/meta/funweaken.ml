module type FUNWEAKEN  =
  sig
    val strengthenPsi :
      (FunSyn.lfctx * IntSyn.sub_) -> (FunSyn.lfctx * IntSyn.sub_)
    val strengthenPsi' :
      (FunSyn.lFDec_ list * IntSyn.sub_) ->
        (FunSyn.lFDec_ list * IntSyn.sub_)
  end


module FunWeaken(FunWeaken:sig module Weaken : WEAKEN end) : FUNWEAKEN =
  struct
    module F = FunSyn
    module I = IntSyn
    let rec strengthenPsi =
      begin function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, Prim (d_)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (F.Prim (Weaken.strengthenDec (d_, s'))))),
            (I.dot1 s'))
      | (Decl (Psi, Block (CtxBlock (l, g_))), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          let (G'', s'') = Weaken.strengthenCtx (g_, s') in
          ((I.Decl (Psi', (F.Block (F.CtxBlock (l, G''))))), s'') end
    let rec strengthenPsi' =
      begin function
      | ([], s) -> ([], s)
      | ((Prim (d_))::Psi, s) ->
          let d'_ = Weaken.strengthenDec (d_, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Prim d'_) :: Psi''), s'')
      | ((Block (CtxBlock (l, g_)))::Psi, s) ->
          let (g'_, s') = Weaken.strengthenCtx (g_, s) in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((F.Block (F.CtxBlock (l, g'_))) :: Psi''), s'') end
  let strengthenPsi = strengthenPsi
  let strengthenPsi' = strengthenPsi' end
