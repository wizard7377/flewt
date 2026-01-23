module type TOMEGACOVERAGE  =
  sig
    exception Error of string 
    val coverageCheckPrg :
      (Tomega.worlds_ * Tomega.dec_ IntSyn.ctx_ * Tomega.prg_) -> unit
  end


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
      if !Global.chatter >= chlev
      then begin print ((^) "[coverage] " f ()) end else begin () end
  let rec purifyFor =
    begin function
    | ((T.Unit, t), (Psi, T.True), s) -> (t, Psi, s)
    | ((PairExp (u_, p_), t), (Psi, Ex ((d_, _), f_)), s) ->
        purifyFor
          ((p_, (T.Dot ((T.Exp u_), t))), ((I.Decl (Psi, (T.UDec d_))), f_),
            (T.comp (s, T.shift))) end
let rec purifyCtx =
  begin function
  | ((Shift k as t), Psi) -> (t, Psi, T.id)
  | (Dot (Prg (p_), t), Decl (Psi, PDec (_, All _, _, _))) ->
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
  | (Dot (Prg (p_), t), Decl (Psi, PDec (_, f_, _, _))) ->
      let (t', Psi', s') = purifyCtx (t, Psi) in
      let (t'', Psi'', s'') =
        purifyFor ((p_, t'), (Psi', (T.forSub (f_, s'))), s') in
      (t'', Psi'', (T.Dot (T.Undef, s'')))
  | (Dot (f_, t), Decl (Psi, UDec (d_))) ->
      let (t', Psi', s') = purifyCtx (t, Psi) in
      ((T.Dot (f_, t')),
        (I.Decl (Psi', (T.UDec (I.decSub (d_, (T.coerceSub s')))))),
        (T.dot1 s')) end(* Mutual recursive predicates
                                           don't have to be checked.
                                         --cs Fri Jan  3 11:35:09 2003 *)
let rec purify (Psi0, t, Psi) =
  let (t', Psi', s') = purifyCtx (t, Psi) in
  let _ = TomegaTypeCheck.checkSub (Psi0, t', Psi') in (Psi0, t', Psi')
let rec coverageCheckPrg =
  begin function
  | (w_, Psi, Lam (d_, p_)) -> coverageCheckPrg (w_, (I.Decl (Psi, d_)), p_)
  | (w_, Psi, New (p_)) -> coverageCheckPrg (w_, Psi, p_)
  | (w_, Psi, PairExp (u_, p_)) -> coverageCheckPrg (w_, Psi, p_)
  | (w_, Psi, PairBlock (b_, p_)) -> coverageCheckPrg (w_, Psi, p_)
  | (w_, Psi, PairPrg (p1_, p2_)) ->
      (begin coverageCheckPrg (w_, Psi, p1_); coverageCheckPrg (w_, Psi, p2_) end)
  | (w_, Psi, T.Unit) -> () | (w_, Psi, Var _) -> ()
  | (w_, Psi, Const _) -> ()
  | (w_, Psi, Rec (d_, p_)) -> coverageCheckPrg (w_, (I.Decl (Psi, d_)), p_)
  | (w_, Psi, Case (Cases (Omega))) ->
      coverageCheckCases (w_, Psi, Omega, [])
  | (w_, Psi, (Let (d_, p1_, p2_) as p_)) ->
      (((begin coverageCheckPrg (w_, Psi, p1_);
         coverageCheckPrg (w_, (I.Decl (Psi, d_)), p2_) end))
  (* chatter 5 ("fn () => TomegaPrint.prgToString (Psi, P)); *))
  | (w_, Psi, Redex (p_, s_)) -> coverageCheckSpine (w_, Psi, s_) end
let rec coverageCheckSpine =
  begin function
  | (w_, Psi, T.Nil) -> ()
  | (w_, Psi, AppExp (u_, s_)) -> coverageCheckSpine (w_, Psi, s_)
  | (w_, Psi, AppBlock (b_, s_)) -> coverageCheckSpine (w_, Psi, s_)
  | (w_, Psi, AppPrg (p_, s_)) ->
      (begin coverageCheckPrg (w_, Psi, p_); coverageCheckSpine (w_, Psi, s_) end) end
let rec coverageCheckCases =
  begin function
  | (w_, Psi, [], []) -> ()
  | (w_, Psi, [], cs_) ->
      let _ =
        chatter 5
          (begin function
           | () ->
               (Int.toString (List.length cs_)) ^ " cases to be checked\n" end) in
    let (_, _, Psi')::_ as cs'_ = map purify cs_ in
    let Cs'' =
      map
        (begin function
         | (Psi0, t, _) -> ((T.coerceCtx Psi0), (T.coerceSub t)) end)
      cs'_ in
    Cover.coverageCheckCases (w_, Cs'', (T.coerceCtx Psi'))
  | (w_, Psi, (Psi', t, p_)::Omega, cs_) ->
      (begin coverageCheckPrg (w_, Psi', p_);
       coverageCheckCases (w_, Psi, Omega, ((Psi', t, Psi) :: cs_)) end) end
let coverageCheckPrg = coverageCheckPrg end
