
(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGACOVERAGE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    exception Error of string 
    val coverageCheckPrg :
      (Tomega.__Worlds * Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg) -> unit
  end;;




(* Coverage checker for programs *)
(* Author: Carsten Schuermann *)
module TomegaCoverage(TomegaCoverage:sig
                                       (*! structure IntSyn' : INTSYN !*)
                                       (*! structure Tomega' : TOMEGA !*)
                                       (*! sharing Tomega'.IntSyn = IntSyn' !*)
                                       module TomegaPrint : TOMEGAPRINT
                                       module TomegaTypeCheck :
                                       TOMEGATYPECHECK
                                       (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
                                       (*! sharing TomegaPrint.Tomega = Tomega' !*)
                                       (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
                                       (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
                                       module Cover : COVER
                                     end) : TOMEGACOVERAGE =
  struct
    (*! sharing Cover.IntSyn = IntSyn' !*)
    (*! sharing Cover.Tomega = Tomega' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev
      then print ((^) "[coverage] " f ())
      else ()
    let rec purifyFor =
      function
      | ((T.Unit, t), (Psi, T.True), s) -> (t, Psi, s)
      | ((PairExp (__u, P), t), (Psi, Ex ((__d, _), F)), s) ->
          purifyFor
            ((P, (T.Dot ((T.Exp __u), t))), ((I.Decl (Psi, (T.UDec __d))), F),
              (T.comp (s, T.shift)))
    let rec purifyCtx =
      function
      | ((Shift k as t), Psi) -> (t, Psi, T.id)
      | (Dot (Prg (P), t), Decl (Psi, PDec (_, All _, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          (t', Psi', (T.Dot (T.Undef, s')))
      | (Dot (Prg (Var _), t), Decl (Psi, PDec (_, _, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          (t', Psi', (T.Dot (T.Undef, s')))
      | (Dot (Prg (Const _), t), Decl (Psi, PDec (_, _, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          (t', Psi', (T.Dot (T.Undef, s')))
      | (Dot (Prg (PairPrg (_, _)), t), Decl (Psi, PDec (_, _, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          (t', Psi', (T.Dot (T.Undef, s')))
      | (Dot (Prg (P), t), Decl (Psi, PDec (_, F, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          let (t'', Psi'', s'') =
            purifyFor ((P, t'), (Psi', (T.forSub (F, s'))), s') in
          (t'', Psi'', (T.Dot (T.Undef, s'')))
      | (Dot (F, t), Decl (Psi, UDec (__d))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          ((T.Dot (F, t')),
            (I.Decl (Psi', (T.UDec (I.decSub (__d, (T.coerceSub s')))))),
            (T.dot1 s'))
    let rec purify (Psi0, t, Psi) =
      let (t', Psi', s') = purifyCtx (t, Psi) in
      let _ = TomegaTypeCheck.checkSub (Psi0, t', Psi') in (Psi0, t', Psi')
    let rec coverageCheckPrg =
      function
      | (W, Psi, Lam (__d, P)) -> coverageCheckPrg (W, (I.Decl (Psi, __d)), P)
      | (W, Psi, New (P)) -> coverageCheckPrg (W, Psi, P)
      | (W, Psi, PairExp (__u, P)) -> coverageCheckPrg (W, Psi, P)
      | (W, Psi, PairBlock (B, P)) -> coverageCheckPrg (W, Psi, P)
      | (W, Psi, PairPrg (__P1, __P2)) ->
          (coverageCheckPrg (W, Psi, __P1); coverageCheckPrg (W, Psi, __P2))
      | (W, Psi, T.Unit) -> ()
      | (W, Psi, Var _) -> ()
      | (W, Psi, Const _) -> ()
      | (W, Psi, Rec (__d, P)) -> coverageCheckPrg (W, (I.Decl (Psi, __d)), P)
      | (W, Psi, Case (Cases (Omega))) ->
          coverageCheckCases (W, Psi, Omega, nil)
      | (W, Psi, (Let (__d, __P1, __P2) as P)) ->
          (coverageCheckPrg (W, Psi, __P1);
           coverageCheckPrg (W, (I.Decl (Psi, __d)), __P2))
      | (W, Psi, Redex (P, S)) -> coverageCheckSpine (W, Psi, S)
    let rec coverageCheckSpine =
      function
      | (W, Psi, T.Nil) -> ()
      | (W, Psi, AppExp (__u, S)) -> coverageCheckSpine (W, Psi, S)
      | (W, Psi, AppBlock (B, S)) -> coverageCheckSpine (W, Psi, S)
      | (W, Psi, AppPrg (P, S)) ->
          (coverageCheckPrg (W, Psi, P); coverageCheckSpine (W, Psi, S))
    let rec coverageCheckCases =
      function
      | (W, Psi, nil, nil) -> ()
      | (W, Psi, nil, __Cs) ->
          let _ =
            chatter 5
              (function
               | () ->
                   (Int.toString (List.length __Cs)) ^ " cases to be checked\n") in
          let (_, _, Psi')::_ as __Cs' = map purify __Cs in
          let __Cs'' =
            map
              (function
               | (Psi0, t, _) -> ((T.coerceCtx Psi0), (T.coerceSub t))) __Cs' in
          Cover.coverageCheckCases (W, __Cs'', (T.coerceCtx Psi'))
      | (W, Psi, (Psi', t, P)::Omega, __Cs) ->
          (coverageCheckPrg (W, Psi', P);
           coverageCheckCases (W, Psi, Omega, ((Psi', t, Psi) :: __Cs)))
    (* chatter chlev f = ()

       Invariant:
       f () returns the string to be printed
         if current chatter level exceeds chlev
    *)
    (* purifyFor ((P, t), (Psi, F), s) = (t', Psi', s')

       Invariant:
       If    Psi0 |- t : Psi
       and   Psi0 |- P in F[t]
       and   Psi |- s : Psi1
       and   P == <M1, <M2, ... Mn, <>>>>
       and   F[t] = Ex x1:A1 ... Ex xn:An.true
       then  Psi' = Psi, x::A1, .... An
       and   t' = Mn...M1.t
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi1
    *)
    (*      | purifyFor ((T.Lam _, _), (_, _), _) = raise Domain
      | purifyFor ((T.New _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairBlock _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairPrg _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Unit, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Root (T.Var k, _), _), (_,  _), _) = raise Domain
      | purifyFor ((T.Redex _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Rec _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Case _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PClo _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Let _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.EVar _, _), (_,  _), _) = raise Domain
*)
    (*  | purifyFor (Psi, T.All (_, F), s) = (Psi, s)
        cannot occur by invariant Mon Dec  2 18:03:20 2002 -cs *)
    (* purifyCtx (t, Psi) = (t', Psi', s')
       If    Psi0 |- t : Psi
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi
    *)
    (* Mutual recursive predicates
                                           don't have to be checked.
                                         --cs Fri Jan  3 11:35:09 2003 *)
    (* subToSpine (Psi', t, Psi) *)
    (* chatter 5 ("fn () => TomegaPrint.prgToString (Psi, P)); *)
    (*    | coverageCheckPrg (Psi, T.EVar) =
          should not occur by invariant  *)
    (*    | coverageCheckSpine (Psi, T.SClo _) =
          should not occur by invariant  *)
    let coverageCheckPrg = coverageCheckPrg
  end ;;
