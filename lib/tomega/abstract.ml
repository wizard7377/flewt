
module type TOMEGAABSTRACT  =
  sig
    exception Error of string 
    val raiseFor :
      IntSyn.__Dec IntSyn.__Ctx ->
        (Tomega.__For * IntSyn.__Sub) -> Tomega.__For
    val raisePrg :
      IntSyn.__Dec IntSyn.__Ctx ->
        Tomega.__Prg -> Tomega.__For -> Tomega.__Prg
    val raiseP :
      IntSyn.__Dec IntSyn.__Ctx ->
        Tomega.__Prg -> Tomega.__For -> Tomega.__Prg
    val raiseF :
      IntSyn.__Dec IntSyn.__Ctx ->
        (Tomega.__For * IntSyn.__Sub) -> Tomega.__For
  end;;




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
    let rec shiftCtx __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, t) -> (I.Null, t)
      | (Decl (__G, __D), t) ->
          let (__G', t') = shiftCtx (__G, t) in
          ((I.Decl (__G', (I.decSub (__D, t')))), (I.dot1 t'))
    let rec dotn __2__ __3__ =
      match (__2__, __3__) with
      | (t, 0) -> t
      | (t, n) -> I.dot1 (dotn (t, (n - 1)))
    let rec strengthenToSpine __4__ __5__ __6__ =
      match (__4__, __5__, __6__) with
      | (Shift _, 0, (n, __S)) -> __S
      | (Dot (((Idx _, t))(* = 1 *)), l, (n, __S)) ->
          let t' = I.comp (t, I.invShift) in
          strengthenToSpine
            (t', (l - 1),
              ((n + 1), (I.App ((I.Root ((I.BVar n), I.Nil)), __S))))
      | (Dot (I.Undef, t), l, (n, __S)) ->
          strengthenToSpine (t, (l - 1), ((n + 1), __S))
      | (Shift k, l, (n, __S)) ->
          strengthenToSpine
            ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), l, (n, __S))
      (* =0 *)
    let rec raiseFor __7__ __8__ =
      match (__7__, __8__) with
      | (__B', (T.True, t)) -> T.True
      | (__B', (And (__F1, __F2), t)) ->
          let F1' = raiseFor (__B', (__F1, t)) in
          let F2' = raiseFor (__B', (__F2, t)) in T.And (F1', F2')
      | (__B', (Ex ((Dec (x, __V), __Q), __F), t)) ->
          let w = S.weaken (__B', (I.targetFam __V)) in
          let iw = Whnf.invert w in
          let B'' = Whnf.strengthen (iw, __B') in
          let __V' = A.raiseType (B'', (I.EClo (__V, (I.comp (t, iw))))) in
          let (B''', _) = shiftCtx (__B', I.shift) in
          let t'' = dotn (I.shift, (I.ctxLength __B')) in
          let t' = I.comp (t, t'') in
          let __S = strengthenToSpine (iw, (I.ctxLength __B'), (1, I.Nil)) in
          let __U = I.Root ((I.BVar ((I.ctxLength B''') + 1)), __S) in
          let t''' = Whnf.dotEta ((I.Exp __U), t') in
          let __F' = raiseFor (B''', (__F, t''')) in
          ((T.Ex (((I.Dec (x, __V')), __Q), __F'))
            (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
            (* B'  |- w  : B''    *)(* B'' |- iw : B'     *)
            (* Psi0, G' |- B'' ctx *)(* Psi0, G' |- V' : type *)
            (* Psi, G', x: V' |- B''' ctx *)(* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
            (* Psi, G', B' |- t : Psi, B, G  *)(* Psi, G', x:V', B''' |- t' : Psi, B, G *)
            (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
            (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
            (* Psi, G', x:V', B''' |- U : V[t'] *)(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
            (* Psi, G', x:V' |- F' for*)(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *))
      | (_, (All _, _)) -> raise Domain(* Psi, G' |- B' ctx  *)(* Psi, B, G, x:V |- F for *)
      (* Psi, G', B' |- V[t] : type *)
    let rec raisePrg __9__ __10__ __11__ =
      match (__9__, __10__, __11__) with
      | (__G, (T.Unit, t), _) -> T.Unit
      | (__G, (PairPrg (__P1, __P2), t), And (__F1, __F2)) ->
          let P1' = raisePrg (__G, (__P1, t), __F1) in
          let P2' = raisePrg (__G, (__P2, t), __F2) in T.PairPrg (P1', P2')
      | (__G, (PairExp (__U, __P), t), Ex ((Dec (_, __V), _), __F)) ->
          let w = S.weaken (__G, (I.targetFam __V)) in
          let iw = Whnf.invert w in
          let __G' = Whnf.strengthen (iw, __G) in
          let __U' = A.raiseTerm (__G', (I.EClo (__U, (I.comp (t, iw))))) in
          let __P' = raisePrg (__G, (__P, t), __F) in
          ((T.PairExp (__U', __P'))
            (* G  |- w  : G'    *)(* G' |- iw : G     *)
            (* Psi0, G' |- B'' ctx *))
    let rec raiseP (__G) (__P) (__F) =
      let (__G', s) = T.deblockify __G in
      let __F' = T.forSub (__F, s) in
      let P'' = raisePrg (__G', (__P, (T.coerceSub s)), __F') in ((P'')
        (*      val P' = T.normalizePrg (P, s)  G' |- P' : F' *))
    let rec raiseF (__G) (__F, t) =
      let (__G', s) = T.deblockify __G in
      let __F' = raiseFor (__G', (__F, (I.comp (t, (T.coerceSub s))))) in
      __F'
    let raisePrg (__G) (__P) (__F) = raisePrg (__G, (__P, I.id), __F)
    let raiseP = raiseP
    let raiseFor = raiseFor
    let raiseF = raiseF
  end ;;
