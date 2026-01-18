
(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGAABSTRACT  =
  sig
    exception Error of string 
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




(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
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
      function
      | (I.Null, t) -> (I.Null, t)
      | (Decl (G, D), t) ->
          let (G', t') = shiftCtx (G, t) in
          ((I.Decl (G', (I.decSub (D, t')))), (I.dot1 t'))
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
      | (G, (T.Unit, t), _) -> T.Unit
      | (G, (PairPrg (P1, P2), t), And (F1, F2)) ->
          let P1' = raisePrg (G, (P1, t), F1) in
          let P2' = raisePrg (G, (P2, t), F2) in T.PairPrg (P1', P2')
      | (G, (PairExp (U, P), t), Ex ((Dec (_, V), _), F)) ->
          let w = S.weaken (G, (I.targetFam V)) in
          let iw = Whnf.invert w in
          let G' = Whnf.strengthen (iw, G) in
          let U' = A.raiseTerm (G', (I.EClo (U, (I.comp (t, iw))))) in
          let P' = raisePrg (G, (P, t), F) in T.PairExp (U', P')
    let rec raiseP (G, P, F) =
      let (G', s) = T.deblockify G in
      let F' = T.forSub (F, s) in
      let P'' = raisePrg (G', (P, (T.coerceSub s)), F') in P''
    let rec raiseF (G, (F, t)) =
      let (G', s) = T.deblockify G in
      let F' = raiseFor (G', (F, (I.comp (t, (T.coerceSub s))))) in F'
    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
    (* =0 *)
    (* = 1 *)
    (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
    (* Psi, G', B' |- V[t] : type *)
    (* Psi, B, G, x:V |- F for *)
    (* Psi, G' |- B' ctx  *)
    (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
    (* B'  |- w  : B''    *)
    (* B'' |- iw : B'     *)
    (* Psi0, G' |- B'' ctx *)
    (* Psi0, G' |- V' : type *)
    (* Psi, G', x: V' |- B''' ctx *)
    (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
    (* Psi, G', B' |- t : Psi, B, G  *)
    (* Psi, G', x:V', B''' |- t' : Psi, B, G *)
    (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
    (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
    (* Psi, G', x:V', B''' |- U : V[t'] *)
    (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
    (* Psi, G', x:V' |- F' for*)
    (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
    (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
    (* G  |- w  : G'    *)
    (* G' |- iw : G     *)
    (* Psi0, G' |- B'' ctx *)
    (*      val P' = T.normalizePrg (P, s)  G' |- P' : F' *)
    let raisePrg = function | (G, P, F) -> raisePrg (G, (P, I.id), F)
    let raiseP = raiseP
    let raiseFor = raiseFor
    let raiseF = raiseF
  end ;;
