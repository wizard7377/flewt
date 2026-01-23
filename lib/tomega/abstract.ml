module type TOMEGAABSTRACT  =
  sig
    exception Error of string 
    val raiseFor :
      (IntSyn.dec_ IntSyn.ctx_ * (Tomega.for_ * IntSyn.sub_)) -> Tomega.for_
    val raisePrg :
      (IntSyn.dec_ IntSyn.ctx_ * Tomega.prg_ * Tomega.for_) -> Tomega.prg_
    val raiseP :
      (IntSyn.dec_ IntSyn.ctx_ * Tomega.prg_ * Tomega.for_) -> Tomega.prg_
    val raiseF :
      (IntSyn.dec_ IntSyn.ctx_ * (Tomega.for_ * IntSyn.sub_)) -> Tomega.for_
  end


module TomegaAbstract(TomegaAbstract:sig
                                       module Global : GLOBAL
                                       module Abstract : ABSTRACT
                                       module Whnf : WHNF
                                       module Subordinate : SUBORDINATE
                                     end) : TOMEGAABSTRACT =
  struct
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract
    let rec shiftCtx =
      begin function
      | (I.Null, t) -> (I.Null, t)
      | (Decl (g_, d_), t) ->
          let (g'_, t') = shiftCtx (g_, t) in
          ((I.Decl (g'_, (I.decSub (d_, t')))), (I.dot1 t')) end
    let rec dotn =
      begin function | (t, 0) -> t | (t, n) -> I.dot1 (dotn (t, (n - 1))) end
  let rec strengthenToSpine =
    begin function
    | (((Shift _, 0, (n, s_)))(* =0 *)) -> s_
    | (Dot (((Idx _, t))(* = 1 *)), l, (n, s_)) ->
        let t' = I.comp (t, I.invShift) in
        strengthenToSpine
          (t', (l - 1),
            ((n + 1), (I.App ((I.Root ((I.BVar n), I.Nil)), s_))))
    | (Dot (I.Undef, t), l, (n, s_)) ->
        strengthenToSpine (t, (l - 1), ((n + 1), s_))
    | (Shift k, l, (n, s_)) ->
        strengthenToSpine
          ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), l, (n, s_)) end
let rec raiseFor =
  begin function
  | (b'_, (T.True, t)) -> T.True
  | (b'_, (And (f1_, f2_), t)) ->
      let F1' = raiseFor (b'_, (f1_, t)) in
      let F2' = raiseFor (b'_, (f2_, t)) in T.And (F1', F2')
  | (b'_, (Ex ((Dec (x, v_), q_), f_), t)) ->
      let w = S.weaken (b'_, (I.targetFam v_)) in
      let iw = Whnf.invert w in
      let B'' = Whnf.strengthen (iw, b'_) in
      let v'_ = A.raiseType (B'', (I.EClo (v_, (I.comp (t, iw))))) in
      let (B''', _) = shiftCtx (b'_, I.shift) in
      let t'' = dotn (I.shift, (I.ctxLength b'_)) in
      let t' = I.comp (t, t'') in
      let s_ = strengthenToSpine (iw, (I.ctxLength b'_), (1, I.Nil)) in
      let u_ = I.Root ((I.BVar ((I.ctxLength B''') + 1)), s_) in
      let t''' = Whnf.dotEta ((I.Exp u_), t') in
      let f'_ = raiseFor (B''', (f_, t''')) in
      ((T.Ex (((I.Dec (x, v'_)), q_), f'_))
        (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
        (* B'  |- w  : B''    *)(* B'' |- iw : B'     *)
        (* Psi0, G' |- B'' ctx *)(* Psi0, G' |- V' : type *)
        (* Psi, G', x: V' |- B''' ctx *)(* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
        (* Psi, G', B' |- t : Psi, B, G  *)(* Psi, G', x:V', B''' |- t' : Psi, B, G *)
        (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
        (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)(* Psi, G', x:V', B''' |- U : V[t'] *)
        (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
        (* Psi, G', x:V' |- F' for*)(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *))
  | (_, (All _, _)) -> raise Domain end(* Psi, G' |- B' ctx  *)(* Psi, B, G, x:V |- F for *)
(* Psi, G', B' |- V[t] : type *)
let rec raisePrg =
  begin function
  | (g_, (T.Unit, t), _) -> T.Unit
  | (g_, (PairPrg (p1_, p2_), t), And (f1_, f2_)) ->
      let P1' = raisePrg (g_, (p1_, t), f1_) in
      let P2' = raisePrg (g_, (p2_, t), f2_) in T.PairPrg (P1', P2')
  | (g_, (PairExp (u_, p_), t), Ex ((Dec (_, v_), _), f_)) ->
      let w = S.weaken (g_, (I.targetFam v_)) in
      let iw = Whnf.invert w in
      let g'_ = Whnf.strengthen (iw, g_) in
      let u'_ = A.raiseTerm (g'_, (I.EClo (u_, (I.comp (t, iw))))) in
      let p'_ = raisePrg (g_, (p_, t), f_) in ((T.PairExp (u'_, p'_))
        (* G  |- w  : G'    *)(* G' |- iw : G     *)
        (* Psi0, G' |- B'' ctx *)) end
let rec raiseP (g_, p_, f_) =
  let (g'_, s) = T.deblockify g_ in
  let f'_ = T.forSub (f_, s) in
  let P'' = raisePrg (g'_, (p_, (T.coerceSub s)), f'_) in ((P'')
    (*      val P' = T.normalizePrg (P, s)  G' |- P' : F' *))
let rec raiseF (g_, (f_, t)) =
  let (g'_, s) = T.deblockify g_ in
  let f'_ = raiseFor (g'_, (f_, (I.comp (t, (T.coerceSub s))))) in f'_
let raisePrg =
  begin function | (g_, p_, f_) -> raisePrg (g_, (p_, I.id), f_) end
let raiseP = raiseP
let raiseFor = raiseFor
let raiseF = raiseF end
