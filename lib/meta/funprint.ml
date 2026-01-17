
module type FUNPRINT  =
  sig
    module Formatter :
    ((FORMATTER)(* Printing of functional proof terms *)
    (* Author: Carsten Schuermann *)(*! structure FunSyn : FUNSYN !*))
    val formatForBare : (IntSyn.dctx * FunSyn.__For) -> Formatter.format
    val formatFor :
      (FunSyn.lfctx * FunSyn.__For) -> string list -> Formatter.format
    val formatPro :
      (FunSyn.lfctx * FunSyn.__Pro) -> string list -> Formatter.format
    val formatLemmaDec : FunSyn.__LemmaDec -> Formatter.format
    val forToString : (FunSyn.lfctx * FunSyn.__For) -> string list -> string
    val proToString : (FunSyn.lfctx * FunSyn.__Pro) -> string list -> string
    val lemmaDecToString : FunSyn.__LemmaDec -> string
  end;;




module FunPrint(FunPrint:sig
                           module Formatter : FORMATTER
                           module Names : NAMES
                           module Print :
                           ((PRINT)(* Printing of functional proof terms *)
                           (* Author: Carsten Schuermann *)
                           (*! structure FunSyn' : FUNSYN !*)(*! sharing Names.IntSyn = FunSyn'.IntSyn !*))
                         end) : FUNPRINT =
  struct
    module Formatter =
      ((Formatter)(*! sharing Print.IntSyn = FunSyn'.IntSyn !*)(*! structure FunSyn = FunSyn' !*))
    module F = FunSyn
    module I = IntSyn
    module Fmt = Formatter
    module P = Print
    let rec formatCtxBlock =
      function
      | (G, (I.Null, s)) -> (G, s, nil)
      | (G, (Decl (I.Null, D), s)) ->
          let D' = I.decSub (D, s) in
          let fmt = P.formatDec (G, D') in
          ((I.Decl (G, D')), (I.dot1 s), [fmt])
      | (G, (Decl (G', D), s)) ->
          let (G'', s'', fmts) = formatCtxBlock (G, (G', s)) in
          let D'' = I.decSub (D, s'') in
          let fmt = P.formatDec (G'', D'') in
          ((I.Decl (G'', D'')), (I.dot1 s''),
            (fmts @ [Fmt.String ","; Fmt.Break; fmt]))
    let rec formatFor' =
      function
      | (G, (All (LD, F), s)) ->
          (match LD with
           | Prim (D) ->
               let D' = Names.decName (G, D) in
               (@) [Fmt.String "{{";
                   P.formatDec (G, (I.decSub (D', s)));
                   Fmt.String "}}";
                   Fmt.Break]
                 formatFor' ((I.Decl (G, D')), (F, (I.dot1 s)))
           | Block (CtxBlock (l, G')) ->
               let (G'', s'', fmts) = formatCtxBlock (G, (G', s)) in
               (@) [Fmt.String "{"; Fmt.Hbox fmts; Fmt.String "}"; Fmt.Break]
                 formatFor' (G'', (F, s'')))
      | (G, (Ex (D, F), s)) ->
          let D' = Names.decName (G, D) in
          (@) [Fmt.String "[[";
              P.formatDec (G, (I.decSub (D', s)));
              Fmt.String "]]";
              Fmt.Break]
            formatFor' ((I.Decl (G, D')), (F, (I.dot1 s)))
      | (G, (F.True, s)) -> [Fmt.String "True"]
    let rec formatFor (Psi, F) names =
      let nameLookup index = List.nth (names, index) in
      let formatFor1 =
        function
        | (index, G, (And (F1, F2), s)) ->
            (@) ((formatFor1 (index, G, (F1, s))) @ [Fmt.Break]) formatFor1
              ((index + 1), G, (F2, s))
        | (index, G, (F, s)) ->
            [Fmt.String (nameLookup index);
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            Fmt.HVbox (formatFor' (G, (F, s)))] in
      let formatFor0 (Args) = Fmt.Vbox0 0 1 (formatFor1 Args) in
      Names.varReset I.Null; formatFor0 (0, (F.makectx Psi), (F, I.id))
    let rec formatForBare (G, F) = Fmt.HVbox (formatFor' (G, (F, I.id)))
    let rec formatPro (Args) names =
      let nameLookup index = List.nth (names, index) in
      let blockName (G1, G2) =
        let blockName' =
          function
          | (G1, I.Null) -> (G1, I.Null)
          | (G1, Decl (G2, D)) ->
              let (G1', G2') = blockName' (G1, G2) in
              let D' = Names.decName (G1, D) in
              ((I.Decl (G1', D')), (I.Decl (G2', D'))) in
        let (G1', G2') = blockName' (G1, G2) in G2' in
      let ctxBlockName (G1, CtxBlock (name, G2)) =
        F.CtxBlock (name, (blockName (G1, G2))) in
      let decName =
        function
        | (G, Prim (D)) -> F.Prim (Names.decName (G, D))
        | (G, Block (CB)) -> F.Block (ctxBlockName (G, CB)) in
      let numberOfSplits (Ds) =
        let numberOfSplits' =
          function
          | (F.Empty, n) -> n
          | (New (_, Ds), n) -> numberOfSplits' (Ds, n)
          | (App (_, Ds), n) -> numberOfSplits' (Ds, n)
          | (Lemma (_, Ds), n) -> numberOfSplits' (Ds, n)
          | (Split (_, Ds), n) -> numberOfSplits' (Ds, (n + 1))
          | (Left (_, Ds), n) -> numberOfSplits' (Ds, n)
          | (Right (_, Ds), n) -> numberOfSplits' (Ds, n) in
        numberOfSplits' (Ds, 0) in
      let psiName (Psi1, s, Psi2, l) =
        let nameDec =
          function
          | ((Dec (SOME _, _) as D), name) -> D
          | (Dec (NONE, V), name) -> I.Dec ((SOME name), V) in
        let namePsi =
          function
          | (Decl (Psi, Prim (D)), 1, name) ->
              I.Decl (Psi, (F.Prim (nameDec (D, name))))
          | (Decl (Psi, (Prim (D) as LD)), n, name) ->
              I.Decl ((namePsi (Psi, (n - 1), name)), LD)
          | (Decl (Psi, Block (CtxBlock (label, G))), n, name) ->
              let (Psi', G') =
                nameG
                  (Psi, G, n, name,
                    (function | n' -> namePsi (Psi, n', name))) in
              I.Decl (Psi', (F.Block (F.CtxBlock (label, G'))))
        and nameG =
          function
          | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
          | (Psi, Decl (G, D), 1, name, k) ->
              (Psi, (I.Decl (G, (nameDec (D, name)))))
          | (Psi, Decl (G, D), n, name, k) ->
              let (Psi', G') = nameG (Psi, G, (n - 1), name, k) in
              (Psi', (I.Decl (G', D))) in
        let ignore =
          function
          | (s, 0) -> s
          | (Dot (_, s), k) -> ignore (s, (k - 1))
          | (Shift n, k) ->
              ignore ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), (k - 1)) in
        let copyNames arg__0 arg__1 =
          match (arg__0, arg__1) with
          | ((Shift n, (Decl _ as G)), Psi1) ->
              copyNames ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), G)
                Psi1
          | ((Dot (Exp _, s), Decl (G, _)), Psi1) -> copyNames (s, G) Psi1
          | ((Dot (Idx k, s), Decl (G, Dec (NONE, _))), Psi1) ->
              copyNames (s, G) Psi1
          | ((Dot (Idx k, s), Decl (G, Dec (SOME name, _))), Psi1) ->
              let Psi1' = namePsi (Psi1, k, name) in copyNames (s, G) Psi1'
          | ((Shift _, I.Null), Psi1) -> Psi1 in
        let psiName' =
          function
          | I.Null -> I.Null
          | Decl (Psi, D) ->
              let Psi' = psiName' Psi in
              I.Decl (Psi', (decName ((F.makectx Psi'), D))) in
        psiName' (copyNames ((ignore (s, l)), (F.makectx Psi2)) Psi1) in
      let merge =
        function
        | (G1, I.Null) -> G1
        | (G1, Decl (G2, D)) -> I.Decl ((merge (G1, G2)), D) in
      let formatCtx (Psi, G) =
        let G0 = F.makectx Psi in
        let formatCtx' =
          function
          | I.Null -> nil
          | Decl (I.Null, Dec (SOME name, V)) ->
              [Fmt.String name; Fmt.String ":"; Print.formatExp (G0, V)]
          | Decl (G, Dec (SOME name, V)) ->
              (formatCtx' G) @
                [Fmt.String ",";
                Fmt.Break;
                Fmt.String name;
                Fmt.String ":";
                Print.formatExp ((merge (G0, G)), V)] in
        Fmt.Hbox ((Fmt.String "|") :: ((formatCtx' G) @ [Fmt.String "|"])) in
      let formatTuple (Psi, P) =
        let formatTuple' =
          function
          | F.Unit -> nil
          | Inx (M, F.Unit) -> [Print.formatExp ((F.makectx Psi), M)]
          | Inx (M, P') ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatTuple' P' in
        match P with
        | Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' P)
        | _ ->
            Fmt.HVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"])) in
      let formatSplitArgs (Psi, L) =
        let formatSplitArgs' =
          function
          | nil -> nil
          | (M)::nil -> [Print.formatExp ((F.makectx Psi), M)]
          | (M)::L ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatSplitArgs' L in
        if (List.length L) = 1
        then Fmt.Hbox (formatSplitArgs' L)
        else
          Fmt.HVbox0 1 1 1
            ((Fmt.String "(") :: ((formatSplitArgs' L) @ [Fmt.String ")"])) in
      let frontToExp =
        function | Idx k -> I.Root ((I.BVar k), I.Nil) | Exp (U) -> U in
      let formatDecs1 =
        function
        | (Psi, Split (xx, Ds), Dot (Ft, s1), L) ->
            formatDecs1 (Psi, Ds, s1, ((frontToExp Ft) :: L))
        | (Psi, F.Empty, s1, L) -> L
        | (Psi, Ds, Shift n, L) ->
            formatDecs1
              (Psi, Ds, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), L) in
      let formatDecs0 =
        function
        | (Psi, App ((xx, M), Ds)) ->
            let (Ds', S) = formatDecs0 (Psi, Ds) in (Ds', (I.App (M, S)))
        | (Psi, Ds) -> (Ds, I.Nil) in
      let formatDecs =
        function
        | (index, Psi, (App ((xx, _), P) as Ds), (Psi1, s1)) ->
            let (Ds', S) = formatDecs0 (Psi, Ds) in
            let L' = formatDecs1 (Psi, Ds', s1, nil) in
            let name = nameLookup index in
            Fmt.Hbox
              [formatSplitArgs (Psi1, L');
              Fmt.Space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.HVbox
                ((::) ((Fmt.String name) :: Fmt.Break) Print.formatSpine
                   ((F.makectx Psi), S))]
        | (index, Psi, New ((CtxBlock (_, G) as B), Ds), (Psi1, s1)) ->
            let B' = ctxBlockName ((F.makectx Psi), B) in
            let fmt =
              formatDecs
                (index, (I.Decl (Psi, (F.Block B'))), Ds, (Psi1, s1)) in
            Fmt.Vbox [formatCtx (Psi, G); Fmt.Break; fmt]
        | (index, Psi, Lemma (lemma, Ds), (Psi1, s1)) ->
            let (Ds', S) = formatDecs0 (Psi, Ds) in
            let L' = formatDecs1 (Psi, Ds', s1, nil) in
            let LemmaDec (names, _, _) = F.lemmaLookup lemma in
            Fmt.Hbox
              [formatSplitArgs (Psi1, L');
              Fmt.Space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.HVbox
                ((::) ((Fmt.String (List.nth (names, index))) :: Fmt.Break)
                   Print.formatSpine ((F.makectx Psi), S))]
        | (index, Psi, Left (_, Ds), (Psi1, s1)) ->
            let fmt = formatDecs (index, Psi, Ds, (Psi1, s1)) in fmt
        | (index, Psi, Right (_, Ds), (Psi1, s1)) ->
            let fmt = formatDecs ((index + 1), Psi, Ds, (Psi1, s1)) in fmt in
      let formatLet =
        function
        | (Psi, Let (Ds, Case (Opts ((Psi1, s1, (Let _ as P1))::nil))), fmts)
            ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits Ds)) in
            let fmt = formatDecs (0, Psi, Ds, (Psi1', s1)) in
            formatLet (Psi1', P1, (fmts @ [fmt; Fmt.Break]))
        | (Psi, Let (Ds, Case (Opts ((Psi1, s1, P1)::nil))), fmts) ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits Ds)) in
            let fmt = formatDecs (0, Psi, Ds, (Psi1', s1)) in
            Fmt.Vbox0 0 1
              [Fmt.String "let";
              Fmt.Break;
              Fmt.Spaces 2;
              Fmt.Vbox0 0 1 (fmts @ [fmt]);
              Fmt.Break;
              Fmt.String "in";
              Fmt.Break;
              Fmt.Spaces 2;
              formatPro3 (Psi1', P1);
              Fmt.Break;
              Fmt.String "end"]
      and formatPro3 =
        function
        | (Psi, (F.Unit as P)) -> formatTuple (Psi, P)
        | (Psi, (Inx _ as P)) -> formatTuple (Psi, P)
        | (Psi, (Let _ as P)) -> formatLet (Psi, P, nil) in
      let argsToSpine =
        function
        | (s, I.Null, S) -> S
        | (Shift n, Psi, S) ->
            argsToSpine
              ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), Psi, S)
        | (Dot (Ft, s), Decl (Psi, D), S) ->
            argsToSpine (s, Psi, (I.App ((frontToExp Ft), S))) in
      let formatHead (index, Psi', s, Psi) =
        Fmt.Hbox
          [Fmt.Space;
          Fmt.HVbox
            ((::) ((Fmt.String (nameLookup index)) :: Fmt.Break)
               Print.formatSpine
               ((F.makectx Psi'), (argsToSpine (s, Psi, I.Nil))))] in
      let formatPro2 =
        function
        | (index, Psi, nil) -> nil
        | (index, Psi, (Psi', s, P)::nil) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            let fhead = if index = 0 then "fun" else "and" in
            [Fmt.HVbox0 1 5 1
               [Fmt.String fhead;
               formatHead (index, Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPro3 (Psi'', P)];
            Fmt.Break]
        | (index, Psi, (Psi', s, P)::O) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            (formatPro2 (index, Psi, O)) @
              [Fmt.HVbox0 1 5 1
                 [Fmt.String "  |";
                 formatHead (index, Psi'', s, Psi);
                 Fmt.Space;
                 Fmt.String "=";
                 Fmt.Break;
                 formatPro3 (Psi'', P)];
              Fmt.Break] in
      let formatPro1 =
        function
        | (index, Psi, Lam (D, P)) ->
            formatPro1
              (index, (I.Decl (Psi, (decName ((F.makectx Psi), D)))), P)
        | (index, Psi, Case (Opts (Os))) -> formatPro2 (index, Psi, Os)
        | (index, Psi, Pair (P1, P2)) ->
            (@) (formatPro1 (index, Psi, P1)) formatPro1
              ((index + 1), Psi, P2) in
      let formatPro0 (Psi, Rec (DD, P)) =
        Fmt.Vbox0 0 1 (formatPro1 (0, Psi, P)) in
      Names.varReset I.Null; formatPro0 Args
    let rec formatLemmaDec (LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1
        [formatFor (I.Null, F) names; Fmt.Break; formatPro (I.Null, P) names]
    let rec forToString (Args) names =
      Fmt.makestring_fmt (formatFor Args names)
    let rec proToString (Args) names =
      Fmt.makestring_fmt (formatPro Args names)
    let rec lemmaDecToString (Args) =
      Fmt.makestring_fmt (formatLemmaDec Args)
    let ((formatFor)(* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *)
      (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
      (* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
      (* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *)
      (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *)
      (* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
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
      = formatFor
    let formatForBare = formatForBare
    let formatPro = formatPro
    let formatLemmaDec = formatLemmaDec
    let forToString = forToString
    let proToString = proToString
    let lemmaDecToString = lemmaDecToString
  end ;;
