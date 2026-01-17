
module type TOMEGAABSTRACT  =
  sig
    exception Error of
      ((string)(* Author: Carsten Schuermann *)(* Abstraction mechanisms form programs and formulas *))
      
    val raiseFor :
      (IntSyn.__Dec IntSyn.__Ctx * (Tomega.__For * IntSyn.__Sub)) ->
        Tomega.__For
    val raisePrg :
      (IntSyn.__Dec IntSyn.__Ctx * Tomega.__Prg * Tomega.__For) ->
        Tomega.__Prg
    val raiseP :
      (IntSyn.__Dec IntSyn.__Ctx * Tomega.__Prg * Tomega.__For) ->
        Tomega.__Prg
    val raiseF :
      (IntSyn.__Dec IntSyn.__Ctx * (Tomega.__For * IntSyn.__Sub)) ->
        Tomega.__For
  end;;




module TomegaAbstract(TomegaAbstract:sig
                                       module Global : GLOBAL
                                       module Abstract : ABSTRACT
                                       module Whnf : WHNF
                                       module Subordinate :
                                       ((SUBORDINATE)(* Converter from relational representation to a functional
   representation of proof terms *)
                                       (* Author: Carsten Schuermann *))
                                     end) : TOMEGAABSTRACT =
  struct
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract
    let rec shiftCtx =
      function
      | (I.Null, t) -> (I.Null, t)
      | (Decl (g, D), t) ->
          let (g', t') = shiftCtx (g, t) in
          ((I.Decl (g', (I.decSub (D, t')))), (I.dot1 t'))
    let rec dotn =
      function | (t, 0) -> t | (t, n) -> I.dot1 (dotn (t, (n - 1)))
    let rec strengthenToSpine =
      function
      | (Shift _, 0, (n, S)) -> S
      | (Dot (Idx _, t), l, (n, S)) ->
          let t' = I.comp (t, I.invShift) in
          strengthenToSpine
            (t', (l - 1),
              ((n + 1), (I.App ((I.Root ((I.BVar n), I.Nil)), S))))
      | (Dot (I.Undef, t), l, (n, S)) ->
          strengthenToSpine (t, (l - 1), ((n + 1), S))
      | (Shift k, l, (n, S)) ->
          strengthenToSpine
            ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), l, (n, S))
    let rec raiseFor =
      function
      | (B', (T.True, t)) -> T.True
      | (B', (And (F1, F2), t)) ->
          let F1' = raiseFor (B', (F1, t)) in
          let F2' = raiseFor (B', (F2, t)) in T.And (F1', F2')
      | (B', (Ex ((Dec (x, V), Q), F), t)) ->
          let w = S.weaken (B', (I.targetFam V)) in
          let iw = Whnf.invert w in
          let B'' = Whnf.strengthen (iw, B') in
          let V' = A.raiseType (B'', (I.EClo (V, (I.comp (t, iw))))) in
          let (B''', _) = shiftCtx (B', I.shift) in
          let t'' = dotn (I.shift, (I.ctxLength B')) in
          let t' = I.comp (t, t'') in
          let S = strengthenToSpine (iw, (I.ctxLength B'), (1, I.Nil)) in
          let U = I.Root ((I.BVar ((I.ctxLength B''') + 1)), S) in
          let t''' = Whnf.dotEta ((I.Exp U), t') in
          let F' = raiseFor (B''', (F, t''')) in
          T.Ex (((I.Dec (x, V')), Q), F')
      | (_, (All _, _)) -> raise Domain
    let rec raisePrg =
      function
      | (g, (T.Unit, t), _) -> T.Unit
      | (g, (PairPrg (P1, P2), t), And (F1, F2)) ->
          let P1' = raisePrg (g, (P1, t), F1) in
          let P2' = raisePrg (g, (P2, t), F2) in T.PairPrg (P1', P2')
      | (g, (PairExp (U, P), t), Ex ((Dec (_, V), _), F)) ->
          let w = S.weaken (g, (I.targetFam V)) in
          let iw = Whnf.invert w in
          let g' = Whnf.strengthen (iw, g) in
          let U' = A.raiseTerm (g', (I.EClo (U, (I.comp (t, iw))))) in
          let P' = raisePrg (g, (P, t), F) in T.PairExp (U', P')
    let rec raiseP (g, P, F) =
      let (g', s) = T.deblockify g in
      let F' = T.forSub (F, s) in
      let P'' = raisePrg (g', (P, (T.coerceSub s)), F') in P''
    let rec raiseF (g, (F, t)) =
      let (g', s) = T.deblockify g in
      let F' = raiseFor (g', (F, (I.comp (t, (T.coerceSub s))))) in F'
    let ((raisePrg)(* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |g| = n   for any g
       then Psi0, g[t] |- t : Psi, g
    *)
      (* =0 *)(* = 1 *)(* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, g |-  F for
       and  Psi, g', B' |- t : Psi, B, g
       then Psi, g' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
      (* Psi, g', B' |- V[t] : type *)(* Psi, B, g, x:V |- F for *)
      (* Psi, g' |- B' ctx  *)(*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
      (* B'  |- w  : B''    *)(* B'' |- iw : B'     *)
      (* Psi0, g' |- B'' ctx *)(* Psi0, g' |- V' : type *)
      (* Psi, g', x: V' |- B''' ctx *)(* Psi, g', x: V', B''' |- t'' :   Psi, g', B' *)
      (* Psi, g', B' |- t : Psi, B, g  *)(* Psi, g', x:V', B''' |- t' : Psi, B, g *)
      (* Psi, g', x:V', B''' |- w : Psi,g', x:V', B'''' *)
      (* Psi, g', x:V', B''' |- S : V' [^|B'''|] >> type  *)
      (* Psi, g', x:V', B''' |- U : V[t'] *)(* Psi, g', x:V', B''' |- t''' :  Psi, B, g, x:V *)
      (* Psi, g', x:V' |- F' for*)(* Psi, g', x:V', B''' |- t''' :  Psi, B, g, x:V *)
      (* raisePrg (g, P, F) = (P', F'))

       Invariant:
       If   Psi, g |- P in F
       and  Psi |- g : blockctx
       then Psi |- P' in F'
       and  P = raise (g, P')   (using subordination)
       and  F = raise (g, F')   (using subordination)
    *)
      (* g  |- w  : g'    *)(* g' |- iw : g     *)
      (* Psi0, g' |- B'' ctx *)(*      val P' = T.normalizePrg (P, s)  g' |- P' : F' *))
      = function | (g, P, F) -> raisePrg (g, (P, I.id), F)
    let raiseP = raiseP
    let raiseFor = raiseFor
    let raiseF = raiseF
  end ;;
