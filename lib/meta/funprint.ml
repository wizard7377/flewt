
module type FUNPRINT  =
  sig
    module Formatter : FORMATTER
    val formatForBare : IntSyn.dctx -> FunSyn.__For -> Formatter.format
    val formatFor :
      FunSyn.lfctx -> FunSyn.__For -> string list -> Formatter.format
    val formatPro :
      FunSyn.lfctx -> FunSyn.__Pro -> string list -> Formatter.format
    val formatLemmaDec : FunSyn.__LemmaDec -> Formatter.format
    val forToString : FunSyn.lfctx -> FunSyn.__For -> string list -> string
    val proToString : FunSyn.lfctx -> FunSyn.__Pro -> string list -> string
    val lemmaDecToString : FunSyn.__LemmaDec -> string
  end;;




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
    let rec formatCtxBlock __0__ __1__ =
      match (__0__, __1__) with
      | (__G, (I.Null, s)) -> (__G, s, nil)
      | (__G, (Decl (I.Null, __D), s)) ->
          let __D' = I.decSub (__D, s) in
          let fmt = P.formatDec (__G, __D') in
          ((I.Decl (__G, __D')), (I.dot1 s), [fmt])
      | (__G, (Decl (__G', __D), s)) ->
          let (G'', s'', fmts) = formatCtxBlock (__G, (__G', s)) in
          let D'' = I.decSub (__D, s'') in
          let fmt = P.formatDec (G'', D'') in
          ((I.Decl (G'', D'')), (I.dot1 s''),
            (fmts @ [Fmt.String ","; Fmt.Break; fmt]))
    let rec formatFor' __2__ __3__ =
      match (__2__, __3__) with
      | (__G, (All (LD, __F), s)) ->
          (match LD with
           | Prim (__D) ->
               let __D' = Names.decName (__G, __D) in
               (@) [Fmt.String "{{";
                   P.formatDec (__G, (I.decSub (__D', s)));
                   Fmt.String "}}";
                   Fmt.Break]
                 formatFor' ((I.Decl (__G, __D')), (__F, (I.dot1 s)))
           | Block (CtxBlock (l, __G')) ->
               let (G'', s'', fmts) = formatCtxBlock (__G, (__G', s)) in
               (@) [Fmt.String "{"; Fmt.Hbox fmts; Fmt.String "}"; Fmt.Break]
                 formatFor' (G'', (__F, s'')))
      | (__G, (Ex (__D, __F), s)) ->
          let __D' = Names.decName (__G, __D) in
          (@) [Fmt.String "[[";
              P.formatDec (__G, (I.decSub (__D', s)));
              Fmt.String "]]";
              Fmt.Break]
            formatFor' ((I.Decl (__G, __D')), (__F, (I.dot1 s)))
      | (__G, (F.True, s)) -> [Fmt.String "True"]
    let rec formatFor (Psi) (__F) names =
      let rec nameLookup index = List.nth (names, index) in
      let rec formatFor1 __4__ __5__ __6__ =
        match (__4__, __5__, __6__) with
        | (index, __G, (And (__F1, __F2), s)) ->
            (@) ((formatFor1 (index, __G, (__F1, s))) @ [Fmt.Break])
              formatFor1 ((index + 1), __G, (__F2, s))
        | (index, __G, (__F, s)) ->
            [Fmt.String (nameLookup index);
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            Fmt.HVbox (formatFor' (__G, (__F, s)))] in
      let rec formatFor0 (Args) = Fmt.Vbox0 0 1 (formatFor1 Args) in
      ((Names.varReset I.Null; formatFor0 (0, (F.makectx Psi), (__F, I.id)))
        (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *))
    let rec formatForBare (__G) (__F) =
      Fmt.HVbox (formatFor' (__G, (__F, I.id)))
    let rec formatPro (Args) names =
      let rec nameLookup index = List.nth (names, index) in
      let rec blockName (__G1) (__G2) =
        let rec blockName' __7__ __8__ =
          match (__7__, __8__) with
          | (__G1, I.Null) -> (__G1, I.Null)
          | (__G1, Decl (__G2, __D)) ->
              let (G1', G2') = blockName' (__G1, __G2) in
              let __D' = Names.decName (__G1, __D) in
              ((I.Decl (G1', __D')), (I.Decl (G2', __D'))) in
        let (G1', G2') = blockName' (__G1, __G2) in G2' in
      let rec ctxBlockName (__G1) (CtxBlock (name, __G2)) =
        F.CtxBlock (name, (blockName (__G1, __G2))) in
      let rec decName __9__ __10__ =
        match (__9__, __10__) with
        | (__G, Prim (__D)) -> F.Prim (Names.decName (__G, __D))
        | (__G, Block (CB)) -> F.Block (ctxBlockName (__G, CB)) in
      let rec numberOfSplits (__Ds) =
        let rec numberOfSplits' __11__ __12__ =
          match (__11__, __12__) with
          | (F.Empty, n) -> n
          | (New (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (App (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Lemma (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Split (_, __Ds), n) -> numberOfSplits' (__Ds, (n + 1))
          | (Left (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Right (_, __Ds), n) -> numberOfSplits' (__Ds, n) in
        numberOfSplits' (__Ds, 0) in
      let rec psiName (Psi1) s (Psi2) l =
        let rec nameDec __13__ __14__ =
          match (__13__, __14__) with
          | ((Dec (Some _, _) as D), name) -> __D
          | (Dec (NONE, __V), name) -> I.Dec ((Some name), __V) in
        let rec namePsi __15__ __16__ __17__ =
          match (__15__, __16__, __17__) with
          | (Decl (Psi, Prim (__D)), 1, name) ->
              I.Decl (Psi, (F.Prim (nameDec (__D, name))))
          | (Decl (Psi, (Prim (__D) as LD)), n, name) ->
              I.Decl ((namePsi (Psi, (n - 1), name)), LD)
          | (Decl (Psi, Block (CtxBlock (label, __G))), n, name) ->
              let (Psi', __G') =
                nameG
                  (Psi, __G, n, name, (fun n' -> namePsi (Psi, n', name))) in
              I.Decl (Psi', (F.Block (F.CtxBlock (label, __G'))))
        and nameG __18__ __19__ __20__ __21__ __22__ =
          match (__18__, __19__, __20__, __21__, __22__) with
          | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
          | (Psi, Decl (__G, __D), 1, name, k) ->
              (Psi, (I.Decl (__G, (nameDec (__D, name)))))
          | (Psi, Decl (__G, __D), n, name, k) ->
              let (Psi', __G') = nameG (Psi, __G, (n - 1), name, k) in
              (Psi', (I.Decl (__G', __D))) in
        let rec ignore __23__ __24__ =
          match (__23__, __24__) with
          | (s, 0) -> s
          | (Dot (_, s), k) -> ignore (s, (k - 1))
          | (Shift n, k) ->
              ignore ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), (k - 1)) in
        let rec copyNames __25__ __26__ __27__ =
          match (__25__, __26__, __27__) with
          | (Shift n, (Decl _ as G), Psi1) ->
              copyNames ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __G)
                Psi1
          | (Dot (Exp _, s), Decl (__G, _), Psi1) -> copyNames (s, __G) Psi1
          | (Dot (Idx k, s), Decl (__G, Dec (NONE, _)), Psi1) ->
              copyNames (s, __G) Psi1
          | (Dot (Idx k, s), Decl (__G, Dec (Some name, _)), Psi1) ->
              let Psi1' = namePsi (Psi1, k, name) in copyNames (s, __G) Psi1'
          | (Shift _, I.Null, Psi1) -> Psi1 in
        let rec psiName' =
          function
          | I.Null -> I.Null
          | Decl (Psi, __D) ->
              let Psi' = psiName' Psi in
              I.Decl (Psi', (decName ((F.makectx Psi'), __D))) in
        psiName' (copyNames ((ignore (s, l)), (F.makectx Psi2)) Psi1) in
      let rec merge __28__ __29__ =
        match (__28__, __29__) with
        | (__G1, I.Null) -> __G1
        | (__G1, Decl (__G2, __D)) -> I.Decl ((merge (__G1, __G2)), __D) in
      let rec formatCtx (Psi) (__G) =
        let __G0 = F.makectx Psi in
        let rec formatCtx' =
          function
          | I.Null -> nil
          | Decl (I.Null, Dec (Some name, __V)) ->
              [Fmt.String name; Fmt.String ":"; Print.formatExp (__G0, __V)]
          | Decl (__G, Dec (Some name, __V)) ->
              (formatCtx' __G) @
                [Fmt.String ",";
                Fmt.Break;
                Fmt.String name;
                Fmt.String ":";
                Print.formatExp ((merge (__G0, __G)), __V)] in
        Fmt.Hbox ((Fmt.String "|") :: ((formatCtx' __G) @ [Fmt.String "|"])) in
      let rec formatTuple (Psi) (__P) =
        let rec formatTuple' =
          function
          | F.Unit -> nil
          | Inx (__M, F.Unit) -> [Print.formatExp ((F.makectx Psi), __M)]
          | Inx (__M, __P') ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), __M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatTuple' __P' in
        match __P with
        | Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' __P)
        | _ ->
            Fmt.HVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' __P) @ [Fmt.String ")"])) in
      let rec formatSplitArgs (Psi) (__L) =
        let rec formatSplitArgs' =
          function
          | nil -> nil
          | (__M)::nil -> [Print.formatExp ((F.makectx Psi), __M)]
          | (__M)::__L ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), __M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatSplitArgs' __L in
        if (List.length __L) = 1
        then Fmt.Hbox (formatSplitArgs' __L)
        else
          Fmt.HVbox0 1 1 1
            ((Fmt.String "(") :: ((formatSplitArgs' __L) @ [Fmt.String ")"])) in
      let rec frontToExp =
        function | Idx k -> I.Root ((I.BVar k), I.Nil) | Exp (__U) -> __U in
      let rec formatDecs1 __30__ __31__ __32__ __33__ =
        match (__30__, __31__, __32__, __33__) with
        | (Psi, Split (xx, __Ds), Dot (Ft, s1), __L) ->
            formatDecs1 (Psi, __Ds, s1, ((frontToExp Ft) :: __L))
        | (Psi, F.Empty, s1, __L) -> __L
        | (Psi, __Ds, Shift n, __L) ->
            formatDecs1
              (Psi, __Ds, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __L) in
      let rec formatDecs0 __34__ __35__ =
        match (__34__, __35__) with
        | (Psi, App ((xx, __M), __Ds)) ->
            let (__Ds', __S) = formatDecs0 (Psi, __Ds) in
            (__Ds', (I.App (__M, __S)))
        | (Psi, __Ds) -> (__Ds, I.Nil) in
      let rec formatDecs __36__ __37__ __38__ __39__ =
        match (__36__, __37__, __38__, __39__) with
        | (index, Psi, (App ((xx, _), __P) as Ds), (Psi1, s1)) ->
            let (__Ds', __S) = formatDecs0 (Psi, __Ds) in
            let __L' = formatDecs1 (Psi, __Ds', s1, nil) in
            let name = nameLookup index in
            Fmt.Hbox
              [formatSplitArgs (Psi1, __L');
              Fmt.Space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.HVbox
                ((::) ((Fmt.String name) :: Fmt.Break) Print.formatSpine
                   ((F.makectx Psi), __S))]
        | (index, Psi, New ((CtxBlock (_, __G) as B), __Ds), (Psi1, s1)) ->
            let __B' = ctxBlockName ((F.makectx Psi), __B) in
            let fmt =
              formatDecs
                (index, (I.Decl (Psi, (F.Block __B'))), __Ds, (Psi1, s1)) in
            Fmt.Vbox [formatCtx (Psi, __G); Fmt.Break; fmt]
        | (index, Psi, Lemma (lemma, __Ds), (Psi1, s1)) ->
            let (__Ds', __S) = formatDecs0 (Psi, __Ds) in
            let __L' = formatDecs1 (Psi, __Ds', s1, nil) in
            let LemmaDec (names, _, _) = F.lemmaLookup lemma in
            Fmt.Hbox
              [formatSplitArgs (Psi1, __L');
              Fmt.Space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.HVbox
                ((::) ((Fmt.String (List.nth (names, index))) :: Fmt.Break)
                   Print.formatSpine ((F.makectx Psi), __S))]
        | (index, Psi, Left (_, __Ds), (Psi1, s1)) ->
            let fmt = formatDecs (index, Psi, __Ds, (Psi1, s1)) in fmt
        | (index, Psi, Right (_, __Ds), (Psi1, s1)) ->
            let fmt = formatDecs ((index + 1), Psi, __Ds, (Psi1, s1)) in fmt in
      let rec formatLet __40__ __41__ __42__ =
        match (__40__, __41__, __42__) with
        | (Psi, Let (__Ds, Case (Opts ((Psi1, s1, (Let _ as P1))::nil))),
           fmts) ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits __Ds)) in
            let fmt = formatDecs (0, Psi, __Ds, (Psi1', s1)) in
            formatLet (Psi1', __P1, (fmts @ [fmt; Fmt.Break]))
        | (Psi, Let (__Ds, Case (Opts ((Psi1, s1, __P1)::nil))), fmts) ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits __Ds)) in
            let fmt = formatDecs (0, Psi, __Ds, (Psi1', s1)) in
            Fmt.Vbox0 0 1
              [Fmt.String "let";
              Fmt.Break;
              Fmt.Spaces 2;
              Fmt.Vbox0 0 1 (fmts @ [fmt]);
              Fmt.Break;
              Fmt.String "in";
              Fmt.Break;
              Fmt.Spaces 2;
              formatPro3 (Psi1', __P1);
              Fmt.Break;
              Fmt.String "end"]
      and formatPro3 __43__ __44__ =
        match (__43__, __44__) with
        | (Psi, (F.Unit as P)) -> formatTuple (Psi, __P)
        | (Psi, (Inx _ as P)) -> formatTuple (Psi, __P)
        | (Psi, (Let _ as P)) -> formatLet (Psi, __P, nil) in
      let rec argsToSpine __45__ __46__ __47__ =
        match (__45__, __46__, __47__) with
        | (s, I.Null, __S) -> __S
        | (Shift n, Psi, __S) ->
            argsToSpine
              ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), Psi, __S)
        | (Dot (Ft, s), Decl (Psi, __D), __S) ->
            argsToSpine (s, Psi, (I.App ((frontToExp Ft), __S))) in
      let rec formatHead index (Psi') s (Psi) =
        Fmt.Hbox
          [Fmt.Space;
          Fmt.HVbox
            ((::) ((Fmt.String (nameLookup index)) :: Fmt.Break)
               Print.formatSpine
               ((F.makectx Psi'), (argsToSpine (s, Psi, I.Nil))))] in
      let rec formatPro2 __48__ __49__ __50__ =
        match (__48__, __49__, __50__) with
        | (index, Psi, nil) -> nil
        | (index, Psi, (Psi', s, __P)::nil) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            let fhead = if index = 0 then "fun" else "and" in
            [Fmt.HVbox0 1 5 1
               [Fmt.String fhead;
               formatHead (index, Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPro3 (Psi'', __P)];
            Fmt.Break]
        | (index, Psi, (Psi', s, __P)::__O) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            (formatPro2 (index, Psi, __O)) @
              [Fmt.HVbox0 1 5 1
                 [Fmt.String "  |";
                 formatHead (index, Psi'', s, Psi);
                 Fmt.Space;
                 Fmt.String "=";
                 Fmt.Break;
                 formatPro3 (Psi'', __P)];
              Fmt.Break] in
      let rec formatPro1 __51__ __52__ __53__ =
        match (__51__, __52__, __53__) with
        | (index, Psi, Lam (__D, __P)) ->
            formatPro1
              (index, (I.Decl (Psi, (decName ((F.makectx Psi), __D)))), __P)
        | (index, Psi, Case (Opts (__Os))) -> formatPro2 (index, Psi, __Os)
        | (index, Psi, Pair (__P1, __P2)) ->
            (@) (formatPro1 (index, Psi, __P1)) formatPro1
              ((index + 1), Psi, __P2) in
      let rec formatPro0 (Psi) (Rec (DD, __P)) =
        Fmt.Vbox0 0 1 (formatPro1 (0, Psi, __P)) in
      ((Names.varReset I.Null; formatPro0 Args)
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
    let rec formatLemmaDec (LemmaDec (names, __P, __F)) =
      Fmt.Vbox0 0 1
        [formatFor (I.Null, __F) names;
        Fmt.Break;
        formatPro (I.Null, __P) names]
    let rec forToString (Args) names =
      Fmt.makestring_fmt (formatFor Args names)
    let rec proToString (Args) names =
      Fmt.makestring_fmt (formatPro Args names)
    let rec lemmaDecToString (Args) =
      Fmt.makestring_fmt (formatLemmaDec Args)
    let formatFor = formatFor
    let formatForBare = formatForBare
    let formatPro = formatPro
    let formatLemmaDec = formatLemmaDec
    let forToString = forToString
    let proToString = proToString
    let lemmaDecToString = lemmaDecToString
  end ;;
