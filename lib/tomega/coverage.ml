
module type TOMEGACOVERAGE  =
  sig
    exception Error of string 
    val coverageCheckPrg :
      Tomega.__Worlds -> Tomega.__Dec IntSyn.__Ctx -> Tomega.__Prg -> unit
  end;;




module TomegaCoverage(TomegaCoverage:sig
                                       module TomegaPrint : TOMEGAPRINT
                                       module TomegaTypeCheck :
                                       TOMEGATYPECHECK
                                       module Cover : COVER
                                     end) : TOMEGACOVERAGE =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev
      then print ((^) "[coverage] " f ())
      else ()
    let rec purifyFor __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | ((T.Unit, t), (Psi, T.True), s) -> (t, Psi, s)
      | ((PairExp (__U, __P), t), (Psi, Ex ((__D, _), __F)), s) ->
          purifyFor
            ((__P, (T.Dot ((T.Exp __U), t))),
              ((I.Decl (Psi, (T.UDec __D))), __F), (T.comp (s, T.shift)))
    let rec purifyCtx __3__ __4__ =
      match (__3__, __4__) with
      | ((Shift k as t), Psi) -> (t, Psi, T.id)
      | (Dot (Prg (__P), t), Decl (Psi, PDec (_, All _, _, _))) ->
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
      | (Dot (Prg (__P), t), Decl (Psi, PDec (_, __F, _, _))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          let (t'', Psi'', s'') =
            purifyFor ((__P, t'), (Psi', (T.forSub (__F, s'))), s') in
          (t'', Psi'', (T.Dot (T.Undef, s'')))
      | (Dot (__F, t), Decl (Psi, UDec (__D))) ->
          let (t', Psi', s') = purifyCtx (t, Psi) in
          ((T.Dot (__F, t')),
            (I.Decl (Psi', (T.UDec (I.decSub (__D, (T.coerceSub s')))))),
            (T.dot1 s'))(* Mutual recursive predicates
                                           don't have to be checked.
                                         --cs Fri Jan  3 11:35:09 2003 *)
    let rec purify (Psi0) t (Psi) =
      let (t', Psi', s') = purifyCtx (t, Psi) in
      let _ = TomegaTypeCheck.checkSub (Psi0, t', Psi') in (Psi0, t', Psi')
    let rec coverageCheckPrg __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (__W, Psi, Lam (__D, __P)) ->
          coverageCheckPrg (__W, (I.Decl (Psi, __D)), __P)
      | (__W, Psi, New (__P)) -> coverageCheckPrg (__W, Psi, __P)
      | (__W, Psi, PairExp (__U, __P)) -> coverageCheckPrg (__W, Psi, __P)
      | (__W, Psi, PairBlock (__B, __P)) -> coverageCheckPrg (__W, Psi, __P)
      | (__W, Psi, PairPrg (__P1, __P2)) ->
          (coverageCheckPrg (__W, Psi, __P1);
           coverageCheckPrg (__W, Psi, __P2))
      | (__W, Psi, T.Unit) -> ()
      | (__W, Psi, Var _) -> ()
      | (__W, Psi, Const _) -> ()
      | (__W, Psi, Rec (__D, __P)) ->
          coverageCheckPrg (__W, (I.Decl (Psi, __D)), __P)
      | (__W, Psi, Case (Cases (Omega))) ->
          coverageCheckCases (__W, Psi, Omega, nil)
      | (__W, Psi, (Let (__D, __P1, __P2) as P)) ->
          (((coverageCheckPrg (__W, Psi, __P1);
             coverageCheckPrg (__W, (I.Decl (Psi, __D)), __P2)))
          (* chatter 5 ("fn () => TomegaPrint.prgToString (Psi, P)); *))
      | (__W, Psi, Redex (__P, __S)) -> coverageCheckSpine (__W, Psi, __S)
    let rec coverageCheckSpine __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (__W, Psi, T.Nil) -> ()
      | (__W, Psi, AppExp (__U, __S)) -> coverageCheckSpine (__W, Psi, __S)
      | (__W, Psi, AppBlock (__B, __S)) -> coverageCheckSpine (__W, Psi, __S)
      | (__W, Psi, AppPrg (__P, __S)) ->
          (coverageCheckPrg (__W, Psi, __P);
           coverageCheckSpine (__W, Psi, __S))
    let rec coverageCheckCases __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (__W, Psi, nil, nil) -> ()
      | (__W, Psi, nil, __Cs) ->
          let _ =
            chatter 5
              (fun () ->
                 (Int.toString (List.length __Cs)) ^ " cases to be checked\n") in
          let (_, _, Psi')::_ as Cs' = map purify __Cs in
          let Cs'' =
            map
              (fun (Psi0) ->
                 fun t -> fun _ -> ((T.coerceCtx Psi0), (T.coerceSub t)))
              __Cs' in
          Cover.coverageCheckCases (__W, Cs'', (T.coerceCtx Psi'))
      | (__W, Psi, (Psi', t, __P)::Omega, __Cs) ->
          (coverageCheckPrg (__W, Psi', __P);
           coverageCheckCases (__W, Psi, Omega, ((Psi', t, Psi) :: __Cs)))
    let coverageCheckPrg = coverageCheckPrg
  end ;;
