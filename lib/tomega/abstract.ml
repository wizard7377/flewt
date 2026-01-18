
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
      | (Decl (__g, __d), t) ->
          let (__g', t') = shiftCtx (__g, t) in
          ((I.Decl (__g', (I.decSub (__d, t')))), (I.dot1 t'))
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
      | (B', (And (__F1, __F2), t)) ->
          let __F1' = raiseFor (B', (__F1, t)) in
          let __F2' = raiseFor (B', (__F2, t)) in T.And (__F1', __F2')
      | (B', (Ex ((Dec (x, __v), Q), F), t)) ->
          let w = S.weaken (B', (I.targetFam __v)) in
          let iw = Whnf.invert w in
          let B'' = Whnf.strengthen (iw, B') in
          let __v' = A.raiseType (B'', (I.EClo (__v, (I.comp (t, iw))))) in
          let (B''', _) = shiftCtx (B', I.shift) in
          let t'' = dotn (I.shift, (I.ctxLength B')) in
          let t' = I.comp (t, t'') in
          let S = strengthenToSpine (iw, (I.ctxLength B'), (1, I.Nil)) in
          let __u = I.Root ((I.BVar ((I.ctxLength B''') + 1)), S) in
          let t''' = Whnf.dotEta ((I.Exp __u), t') in
          let __F' = raiseFor (B''', (F, t''')) in
          T.Ex (((I.Dec (x, __v')), Q), __F')
      | (_, (All _, _)) -> raise Domain
    let rec raisePrg =
      function
      | (__g, (T.Unit, t), _) -> T.Unit
      | (__g, (PairPrg (__P1, __P2), t), And (__F1, __F2)) ->
          let __P1' = raisePrg (__g, (__P1, t), __F1) in
          let __P2' = raisePrg (__g, (__P2, t), __F2) in T.PairPrg (__P1', __P2')
      | (__g, (PairExp (__u, P), t), Ex ((Dec (_, __v), _), F)) ->
          let w = S.weaken (__g, (I.targetFam __v)) in
          let iw = Whnf.invert w in
          let __g' = Whnf.strengthen (iw, __g) in
          let __u' = A.raiseTerm (__g', (I.EClo (__u, (I.comp (t, iw))))) in
          let __P' = raisePrg (__g, (P, t), F) in T.PairExp (__u', __P')
    let rec raiseP (__g, P, F) =
      let (__g', s) = T.deblockify __g in
      let __F' = T.forSub (F, s) in
      let __P'' = raisePrg (__g', (P, (T.coerceSub s)), __F') in __P''
    let rec raiseF (__g, (F, t)) =
      let (__g', s) = T.deblockify __g in
      let __F' = raiseFor (__g', (F, (I.comp (t, (T.coerceSub s))))) in __F'
    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |__g| = n   for any __g
       then Psi0, __g[t] |- t : Psi, __g
    *)
    (* =0 *)
    (* = 1 *)
    (* raiseFor (B, (F, t)) = (__P', __F'))

       Invariant:
       If   Psi, B, __g |-  F for
       and  Psi, __g', B' |- t : Psi, B, __g
       then Psi, __g' |-  __F' for
       and  __F' = raise (B', F[t])   (using subordination)
    *)
    (* Psi, __g', B' |- __v[t] : type *)
    (* Psi, B, __g, x:__v |- F for *)
    (* Psi, __g' |- B' ctx  *)
    (*        val (w, S) = subweaken (B', 1, I.targetFam __v, I.Nil)     *)
    (* B'  |- w  : B''    *)
    (* B'' |- iw : B'     *)
    (* Psi0, __g' |- B'' ctx *)
    (* Psi0, __g' |- __v' : type *)
    (* Psi, __g', x: __v' |- B''' ctx *)
    (* Psi, __g', x: __v', B''' |- t'' :   Psi, __g', B' *)
    (* Psi, __g', B' |- t : Psi, B, __g  *)
    (* Psi, __g', x:__v', B''' |- t' : Psi, B, __g *)
    (* Psi, __g', x:__v', B''' |- w : Psi,__g', x:__v', B'''' *)
    (* Psi, __g', x:__v', B''' |- S : __v' [^|B'''|] >> type  *)
    (* Psi, __g', x:__v', B''' |- __u : __v[t'] *)
    (* Psi, __g', x:__v', B''' |- t''' :  Psi, B, __g, x:__v *)
    (* Psi, __g', x:__v' |- __F' for*)
    (* Psi, __g', x:__v', B''' |- t''' :  Psi, B, __g, x:__v *)
    (* raisePrg (__g, P, F) = (__P', __F'))

       Invariant:
       If   Psi, __g |- P in F
       and  Psi |- __g : blockctx
       then Psi |- __P' in __F'
       and  P = raise (__g, __P')   (using subordination)
       and  F = raise (__g, __F')   (using subordination)
    *)
    (* __g  |- w  : __g'    *)
    (* __g' |- iw : __g     *)
    (* Psi0, __g' |- B'' ctx *)
    (*      val __P' = T.normalizePrg (P, s)  __g' |- __P' : __F' *)
    let raisePrg = function | (__g, P, F) -> raisePrg (__g, (P, I.id), F)
    let raiseP = raiseP
    let raiseFor = raiseFor
    let raiseF = raiseF
  end ;;
