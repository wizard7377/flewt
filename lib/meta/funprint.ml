module type FUNPRINT  =
  sig
    module Formatter : FORMATTER
    val formatForBare : (IntSyn.dctx * FunSyn.for_) -> Formatter.format
    val formatFor :
      (FunSyn.lfctx * FunSyn.for_) -> string list -> Formatter.format
    val formatPro :
      (FunSyn.lfctx * FunSyn.pro_) -> string list -> Formatter.format
    val formatLemmaDec : FunSyn.lemmaDec_ -> Formatter.format
    val forToString : (FunSyn.lfctx * FunSyn.for_) -> string list -> string
    val proToString : (FunSyn.lfctx * FunSyn.pro_) -> string list -> string
    val lemmaDecToString : FunSyn.lemmaDec_ -> string
  end


module FunPrint(FunPrint:sig
                           module Formatter : FORMATTER
                           module Names : NAMES
                           module Print : PRINT
                         end) : FUNPRINT =
  struct
    module Formatter = Formatter
    module F = FunSyn
    module I = IntSyn
    module Fmt = Formatter
    module P = Print
    let rec formatCtxBlock =
      begin function
      | (g_, (I.Null, s)) -> (g_, s, [])
      | (g_, (Decl (I.Null, d_), s)) ->
          let d'_ = I.decSub (d_, s) in
          let fmt = P.formatDec (g_, d'_) in
          ((I.Decl (g_, d'_)), (I.dot1 s), [fmt])
      | (g_, (Decl (g'_, d_), s)) ->
          let (G'', s'', fmts) = formatCtxBlock (g_, (g'_, s)) in
          let D'' = I.decSub (d_, s'') in
          let fmt = P.formatDec (G'', D'') in
          ((I.Decl (G'', D'')), (I.dot1 s''),
            (fmts @ [Fmt.String ","; Fmt.Break; fmt])) end
    let rec formatFor' =
      begin function
      | (g_, (All (LD, f_), s)) ->
          (begin match LD with
           | Prim (d_) ->
               let d'_ = Names.decName (g_, d_) in
               (@) [Fmt.String "{{";
                   P.formatDec (g_, (I.decSub (d'_, s)));
                   Fmt.String "}}";
                   Fmt.Break]
                 formatFor' ((I.Decl (g_, d'_)), (f_, (I.dot1 s)))
           | Block (CtxBlock (l, g'_)) ->
               let (G'', s'', fmts) = formatCtxBlock (g_, (g'_, s)) in
               (@) [Fmt.String "{"; Fmt.Hbox fmts; Fmt.String "}"; Fmt.Break]
                 formatFor' (G'', (f_, s'')) end)
      | (g_, (Ex (d_, f_), s)) ->
          let d'_ = Names.decName (g_, d_) in
          (@) [Fmt.String "[[";
              P.formatDec (g_, (I.decSub (d'_, s)));
              Fmt.String "]]";
              Fmt.Break]
            formatFor' ((I.Decl (g_, d'_)), (f_, (I.dot1 s)))
      | (g_, (F.True, s)) -> [Fmt.String "True"] end
let rec formatFor (Psi, f_) names =
  let rec nameLookup index = List.nth (names, index) in
  let rec formatFor1 =
    begin function
    | (index, g_, (And (f1_, f2_), s)) ->
        (@) ((formatFor1 (index, g_, (f1_, s))) @ [Fmt.Break]) formatFor1
          ((index + 1), g_, (f2_, s))
    | (index, g_, (f_, s)) ->
        [Fmt.String (nameLookup index);
        Fmt.Space;
        Fmt.String "::";
        Fmt.Space;
        Fmt.HVbox (formatFor' (g_, (f_, s)))] end in
  let rec formatFor0 (Args) = Fmt.Vbox0 0 1 (formatFor1 Args) in
  ((begin Names.varReset I.Null; formatFor0 (0, (F.makectx Psi), (f_, I.id)) end)
    (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *))
let rec formatForBare (g_, f_) = Fmt.HVbox (formatFor' (g_, (f_, I.id)))
let rec formatPro (Args) names =
  let rec nameLookup index = List.nth (names, index) in
  let rec blockName (g1_, g2_) =
    let rec blockName' =
      begin function
      | (g1_, I.Null) -> (g1_, I.Null)
      | (g1_, Decl (g2_, d_)) ->
          let (G1', G2') = blockName' (g1_, g2_) in
          let d'_ = Names.decName (g1_, d_) in
          ((I.Decl (G1', d'_)), (I.Decl (G2', d'_))) end in
  let (G1', G2') = blockName' (g1_, g2_) in G2' in
  let rec ctxBlockName (g1_, CtxBlock (name, g2_)) =
    F.CtxBlock (name, (blockName (g1_, g2_))) in
  let rec decName =
    begin function
    | (g_, Prim (d_)) -> F.Prim (Names.decName (g_, d_))
    | (g_, Block (CB)) -> F.Block (ctxBlockName (g_, CB)) end in
  let rec numberOfSplits (ds_) =
    let rec numberOfSplits' =
      begin function
      | (F.Empty, n) -> n
      | (New (_, ds_), n) -> numberOfSplits' (ds_, n)
      | (App (_, ds_), n) -> numberOfSplits' (ds_, n)
      | (Lemma (_, ds_), n) -> numberOfSplits' (ds_, n)
      | (Split (_, ds_), n) -> numberOfSplits' (ds_, (n + 1))
      | (Left (_, ds_), n) -> numberOfSplits' (ds_, n)
      | (Right (_, ds_), n) -> numberOfSplits' (ds_, n) end in
  numberOfSplits' (ds_, 0) in
  let rec psiName (Psi1, s, Psi2, l) =
    let rec nameDec =
      begin function
      | ((Dec (Some _, _) as d_), name) -> d_
      | (Dec (None, v_), name) -> I.Dec ((Some name), v_) end in
  let rec namePsi =
    begin function
    | (Decl (Psi, Prim (d_)), 1, name) ->
        I.Decl (Psi, (F.Prim (nameDec (d_, name))))
    | (Decl (Psi, (Prim (d_) as LD)), n, name) ->
        I.Decl ((namePsi (Psi, (n - 1), name)), LD)
    | (Decl (Psi, Block (CtxBlock (label, g_))), n, name) ->
        let (Psi', g'_) =
          nameG
            (Psi, g_, n, name,
              (begin function | n' -> namePsi (Psi, n', name) end)) in
      I.Decl (Psi', (F.Block (F.CtxBlock (label, g'_)))) end
    and nameG =
      begin function
      | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
      | (Psi, Decl (g_, d_), 1, name, k) ->
          (Psi, (I.Decl (g_, (nameDec (d_, name)))))
      | (Psi, Decl (g_, d_), n, name, k) ->
          let (Psi', g'_) = nameG (Psi, g_, (n - 1), name, k) in
          (Psi', (I.Decl (g'_, d_))) end in
  let rec ignore =
    begin function
    | (s, 0) -> s
    | (Dot (_, s), k) -> ignore (s, (k - 1))
    | (Shift n, k) ->
        ignore ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), (k - 1)) end in
  let rec copyNames arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | ((Shift n, (Decl _ as g_)), Psi1) ->
        copyNames ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), g_) Psi1
    | ((Dot (Exp _, s), Decl (g_, _)), Psi1) -> copyNames (s, g_) Psi1
    | ((Dot (Idx k, s), Decl (g_, Dec (None, _))), Psi1) ->
        copyNames (s, g_) Psi1
    | ((Dot (Idx k, s), Decl (g_, Dec (Some name, _))), Psi1) ->
        let Psi1' = namePsi (Psi1, k, name) in copyNames (s, g_) Psi1'
    | ((Shift _, I.Null), Psi1) -> Psi1 end in
  let rec psiName' =
    begin function
    | I.Null -> I.Null
    | Decl (Psi, d_) ->
        let Psi' = psiName' Psi in
        I.Decl (Psi', (decName ((F.makectx Psi'), d_))) end in
  psiName' (copyNames ((ignore (s, l)), (F.makectx Psi2)) Psi1) in
let rec merge =
begin function
| (g1_, I.Null) -> g1_
| (g1_, Decl (g2_, d_)) -> I.Decl ((merge (g1_, g2_)), d_) end in
let rec formatCtx (Psi, g_) =
let g0_ = F.makectx Psi in
let rec formatCtx' =
  begin function
  | I.Null -> []
  | Decl (I.Null, Dec (Some name, v_)) ->
      [Fmt.String name; Fmt.String ":"; Print.formatExp (g0_, v_)]
  | Decl (g_, Dec (Some name, v_)) ->
      (formatCtx' g_) @
        [Fmt.String ",";
        Fmt.Break;
        Fmt.String name;
        Fmt.String ":";
        Print.formatExp ((merge (g0_, g_)), v_)] end in
Fmt.Hbox ((Fmt.String "|") :: ((formatCtx' g_) @ [Fmt.String "|"])) in
let rec formatTuple (Psi, p_) =
let rec formatTuple' =
  begin function
  | F.Unit -> []
  | Inx (m_, F.Unit) -> [Print.formatExp ((F.makectx Psi), m_)]
  | Inx (m_, p'_) ->
      (::) (((::) (Print.formatExp ((F.makectx Psi), m_)) Fmt.String ",") ::
              Fmt.Break)
        formatTuple' p'_ end in
begin match p_ with
| Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' p_)
| _ ->
  Fmt.HVbox0 1 1 1
    ((Fmt.String "(") :: ((formatTuple' p_) @ [Fmt.String ")"])) end in
let rec formatSplitArgs (Psi, l_) =
let rec formatSplitArgs' =
  begin function
  | [] -> []
  | (m_)::[] -> [Print.formatExp ((F.makectx Psi), m_)]
  | (m_)::l_ ->
      (::) (((::) (Print.formatExp ((F.makectx Psi), m_)) Fmt.String ",") ::
              Fmt.Break)
        formatSplitArgs' l_ end in
if (List.length l_) = 1 then begin Fmt.Hbox (formatSplitArgs' l_) end
else begin
  Fmt.HVbox0 1 1 1
    ((Fmt.String "(") :: ((formatSplitArgs' l_) @ [Fmt.String ")"])) end in
let rec frontToExp =
begin function | Idx k -> I.Root ((I.BVar k), I.Nil) | Exp (u_) -> u_ end in
let rec formatDecs1 =
begin function
| (Psi, Split (xx, ds_), Dot (Ft, s1), l_) ->
    formatDecs1 (Psi, ds_, s1, ((frontToExp Ft) :: l_))
| (Psi, F.Empty, s1, l_) -> l_
| (Psi, ds_, Shift n, l_) ->
    formatDecs1 (Psi, ds_, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), l_) end in
let rec formatDecs0 =
begin function
| (Psi, App ((xx, m_), ds_)) ->
    let (ds'_, s_) = formatDecs0 (Psi, ds_) in (ds'_, (I.App (m_, s_)))
| (Psi, ds_) -> (ds_, I.Nil) end in
let rec formatDecs =
begin function
| (index, Psi, (App ((xx, _), p_) as ds_), (Psi1, s1)) ->
    let (ds'_, s_) = formatDecs0 (Psi, ds_) in
    let l'_ = formatDecs1 (Psi, ds'_, s1, []) in
    let name = nameLookup index in
    Fmt.Hbox
      [formatSplitArgs (Psi1, l'_);
      Fmt.Space;
      Fmt.String "=";
      Fmt.Break;
      Fmt.HVbox
        ((::) ((Fmt.String name) :: Fmt.Break) Print.formatSpine
           ((F.makectx Psi), s_))]
| (index, Psi, New ((CtxBlock (_, g_) as b_), ds_), (Psi1, s1)) ->
    let b'_ = ctxBlockName ((F.makectx Psi), b_) in
    let fmt =
      formatDecs (index, (I.Decl (Psi, (F.Block b'_))), ds_, (Psi1, s1)) in
    Fmt.Vbox [formatCtx (Psi, g_); Fmt.Break; fmt]
| (index, Psi, Lemma (lemma, ds_), (Psi1, s1)) ->
    let (ds'_, s_) = formatDecs0 (Psi, ds_) in
    let l'_ = formatDecs1 (Psi, ds'_, s1, []) in
    let LemmaDec (names, _, _) = F.lemmaLookup lemma in
    Fmt.Hbox
      [formatSplitArgs (Psi1, l'_);
      Fmt.Space;
      Fmt.String "=";
      Fmt.Break;
      Fmt.HVbox
        ((::) ((Fmt.String (List.nth (names, index))) :: Fmt.Break)
           Print.formatSpine ((F.makectx Psi), s_))]
| (index, Psi, Left (_, ds_), (Psi1, s1)) ->
    let fmt = formatDecs (index, Psi, ds_, (Psi1, s1)) in fmt
| (index, Psi, Right (_, ds_), (Psi1, s1)) ->
    let fmt = formatDecs ((index + 1), Psi, ds_, (Psi1, s1)) in fmt end in
let rec formatLet =
begin function
| (Psi, Let (ds_, Case (Opts ((Psi1, s1, (Let _ as p1_))::[]))), fmts) ->
    let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits ds_)) in
    let fmt = formatDecs (0, Psi, ds_, (Psi1', s1)) in
    formatLet (Psi1', p1_, (fmts @ [fmt; Fmt.Break]))
| (Psi, Let (ds_, Case (Opts ((Psi1, s1, p1_)::[]))), fmts) ->
    let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits ds_)) in
    let fmt = formatDecs (0, Psi, ds_, (Psi1', s1)) in
    Fmt.Vbox0 0 1
      [Fmt.String "let";
      Fmt.Break;
      Fmt.Spaces 2;
      Fmt.Vbox0 0 1 (fmts @ [fmt]);
      Fmt.Break;
      Fmt.String "in";
      Fmt.Break;
      Fmt.Spaces 2;
      formatPro3 (Psi1', p1_);
      Fmt.Break;
      Fmt.String "end"] end
and formatPro3 =
  begin function
  | (Psi, (F.Unit as p_)) -> formatTuple (Psi, p_)
  | (Psi, (Inx _ as p_)) -> formatTuple (Psi, p_)
  | (Psi, (Let _ as p_)) -> formatLet (Psi, p_, []) end in
let rec argsToSpine =
begin function
| (s, I.Null, s_) -> s_
| (Shift n, Psi, s_) ->
    argsToSpine ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), Psi, s_)
| (Dot (Ft, s), Decl (Psi, d_), s_) ->
    argsToSpine (s, Psi, (I.App ((frontToExp Ft), s_))) end in
let rec formatHead (index, Psi', s, Psi) =
Fmt.Hbox
  [Fmt.Space;
  Fmt.HVbox
    ((::) ((Fmt.String (nameLookup index)) :: Fmt.Break) Print.formatSpine
       ((F.makectx Psi'), (argsToSpine (s, Psi, I.Nil))))] in
let rec formatPro2 =
begin function
| (index, Psi, []) -> []
| (index, Psi, (Psi', s, p_)::[]) ->
    let Psi'' = psiName (Psi', s, Psi, 0) in
    let fhead = if index = 0 then begin "fun" end else begin "and" end in
  [Fmt.HVbox0 1 5 1
     [Fmt.String fhead;
     formatHead (index, Psi'', s, Psi);
     Fmt.Space;
     Fmt.String "=";
     Fmt.Break;
     formatPro3 (Psi'', p_)];
  Fmt.Break]
| (index, Psi, (Psi', s, p_)::o_) ->
    let Psi'' = psiName (Psi', s, Psi, 0) in
    (formatPro2 (index, Psi, o_)) @
      [Fmt.HVbox0 1 5 1
         [Fmt.String "  |";
         formatHead (index, Psi'', s, Psi);
         Fmt.Space;
         Fmt.String "=";
         Fmt.Break;
         formatPro3 (Psi'', p_)];
      Fmt.Break] end in
let rec formatPro1 =
begin function
| (index, Psi, Lam (d_, p_)) ->
    formatPro1 (index, (I.Decl (Psi, (decName ((F.makectx Psi), d_)))), p_)
| (index, Psi, Case (Opts (os_))) -> formatPro2 (index, Psi, os_)
| (index, Psi, Pair (p1_, p2_)) ->
    (@) (formatPro1 (index, Psi, p1_)) formatPro1 ((index + 1), Psi, p2_) end in
let rec formatPro0 (Psi, Rec (DD, p_)) =
Fmt.Vbox0 0 1 (formatPro1 (0, Psi, p_)) in
((begin Names.varReset I.Null; formatPro0 Args end)
(* blockName (G1, G2) = G2'

           Invariant:
           If   G1 |- G2 ctx
           then G2' = G2 modulo new non-conficting variable names.
        *)
(* ctxBlockName (G1, CB) = CB'

           Invariant:
           If   G1 |- CB ctxblock
           then CB' = CB modulo new non-conficting variable names.
        *)
(* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
(* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        *)
(* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for all x in Psi2 s.t. s(x) = x in Psi1'
        *)
(* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
(* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
(* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
(* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
(* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
(* formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        *)
(* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
(* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
(* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
(* formatPro3 (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
(* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
(* formatHead (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
(* formatPro2 (index, Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
(* formatPro1 (index, Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
(* formatPro0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *))
let rec formatLemmaDec (LemmaDec (names, p_, f_)) =
  Fmt.Vbox0 0 1
    [formatFor (I.Null, f_) names; Fmt.Break; formatPro (I.Null, p_) names]
let rec forToString (Args) names = Fmt.makestring_fmt (formatFor Args names)
let rec proToString (Args) names = Fmt.makestring_fmt (formatPro Args names)
let rec lemmaDecToString (Args) = Fmt.makestring_fmt (formatLemmaDec Args)
let formatFor = formatFor
let formatForBare = formatForBare
let formatPro = formatPro
let formatLemmaDec = formatLemmaDec
let forToString = forToString
let proToString = proToString
let lemmaDecToString = lemmaDecToString end
