
(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module type FUNPRINT  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module Formatter : FORMATTER
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




(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module FunPrint(FunPrint:sig
                           (*! structure FunSyn' : FUNSYN !*)
                           module Formatter : FORMATTER
                           module Names : NAMES
                           (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
                           module Print : PRINT
                         end) : FUNPRINT =
  struct
    (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
    (*! structure FunSyn = FunSyn' !*)
    module Formatter = Formatter
    module F = FunSyn
    module I = IntSyn
    module Fmt = Formatter
    module P = Print
    let rec formatCtxBlock =
      function
      | (__g, (I.Null, s)) -> (__g, s, nil)
      | (__g, (Decl (I.Null, __d), s)) ->
          let __d' = I.decSub (__d, s) in
          let fmt = P.formatDec (__g, __d') in
          ((I.Decl (__g, __d')), (I.dot1 s), [fmt])
      | (__g, (Decl (__g', __d), s)) ->
          let (__g'', s'', fmts) = formatCtxBlock (__g, (__g', s)) in
          let __d'' = I.decSub (__d, s'') in
          let fmt = P.formatDec (__g'', __d'') in
          ((I.Decl (__g'', __d'')), (I.dot1 s''),
            (fmts @ [Fmt.String ","; Fmt.Break; fmt]))
    let rec formatFor' =
      function
      | (__g, (All (LD, F), s)) ->
          (match LD with
           | Prim (__d) ->
               let __d' = Names.decName (__g, __d) in
               (@) [Fmt.String "{{";
                   P.formatDec (__g, (I.decSub (__d', s)));
                   Fmt.String "}}";
                   Fmt.Break]
                 formatFor' ((I.Decl (__g, __d')), (F, (I.dot1 s)))
           | Block (CtxBlock (l, __g')) ->
               let (__g'', s'', fmts) = formatCtxBlock (__g, (__g', s)) in
               (@) [Fmt.String "{"; Fmt.hbox fmts; Fmt.String "}"; Fmt.Break]
                 formatFor' (__g'', (F, s'')))
      | (__g, (Ex (__d, F), s)) ->
          let __d' = Names.decName (__g, __d) in
          (@) [Fmt.String "[[";
              P.formatDec (__g, (I.decSub (__d', s)));
              Fmt.String "]]";
              Fmt.Break]
            formatFor' ((I.Decl (__g, __d')), (F, (I.dot1 s)))
      | (__g, (F.True, s)) -> [Fmt.String "True"]
    let rec formatFor (Psi, F) names =
      let rec nameLookup index = List.nth (names, index) in
      let rec formatFor1 =
        function
        | (index, __g, (And (__F1, __F2), s)) ->
            (@) ((formatFor1 (index, __g, (__F1, s))) @ [Fmt.Break]) formatFor1
              ((index + 1), __g, (__F2, s))
        | (index, __g, (F, s)) ->
            [Fmt.String (nameLookup index);
            Fmt.space;
            Fmt.String "::";
            Fmt.space;
            Fmt.hVbox (formatFor' (__g, (F, s)))] in
      let rec formatFor0 (Args) = Fmt.Vbox0 0 1 (formatFor1 Args) in
      Names.varReset I.Null; formatFor0 (0, (F.makectx Psi), (F, I.id))
    let rec formatForBare (__g, F) = Fmt.hVbox (formatFor' (__g, (F, I.id)))
    let rec formatPro (Args) names =
      let rec nameLookup index = List.nth (names, index) in
      let rec blockName (G1, G2) =
        let rec blockName' =
          function
          | (G1, I.Null) -> (G1, I.Null)
          | (G1, Decl (G2, __d)) ->
              let (G1', G2') = blockName' (G1, G2) in
              let __d' = Names.decName (G1, __d) in
              ((I.Decl (G1', __d')), (I.Decl (G2', __d'))) in
        let (G1', G2') = blockName' (G1, G2) in G2' in
      let rec ctxBlockName (G1, CtxBlock (name, G2)) =
        F.CtxBlock (name, (blockName (G1, G2))) in
      let rec decName =
        function
        | (__g, Prim (__d)) -> F.Prim (Names.decName (__g, __d))
        | (__g, Block (CB)) -> F.Block (ctxBlockName (__g, CB)) in
      let rec numberOfSplits (__Ds) =
        let rec numberOfSplits' =
          function
          | (F.Empty, n) -> n
          | (New (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (App (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Lemma (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Split (_, __Ds), n) -> numberOfSplits' (__Ds, (n + 1))
          | (Left (_, __Ds), n) -> numberOfSplits' (__Ds, n)
          | (Right (_, __Ds), n) -> numberOfSplits' (__Ds, n) in
        numberOfSplits' (__Ds, 0) in
      let rec psiName (Psi1, s, Psi2, l) =
        let rec nameDec =
          function
          | ((Dec (Some _, _) as __d), name) -> __d
          | (Dec (None, __v), name) -> I.Dec ((Some name), __v) in
        let rec namePsi =
          function
          | (Decl (Psi, Prim (__d)), 1, name) ->
              I.Decl (Psi, (F.Prim (nameDec (__d, name))))
          | (Decl (Psi, (Prim (__d) as LD)), n, name) ->
              I.Decl ((namePsi (Psi, (n - 1), name)), LD)
          | (Decl (Psi, Block (CtxBlock (label, __g))), n, name) ->
              let (Psi', __g') =
                nameG
                  (Psi, __g, n, name,
                    (function | n' -> namePsi (Psi, n', name))) in
              I.Decl (Psi', (F.Block (F.CtxBlock (label, __g'))))
        and nameG =
          function
          | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
          | (Psi, Decl (__g, __d), 1, name, k) ->
              (Psi, (I.Decl (__g, (nameDec (__d, name)))))
          | (Psi, Decl (__g, __d), n, name, k) ->
              let (Psi', __g') = nameG (Psi, __g, (n - 1), name, k) in
              (Psi', (I.Decl (__g', __d))) in
        let rec ignore =
          function
          | (s, 0) -> s
          | (Dot (_, s), k) -> ignore (s, (k - 1))
          | (Shift n, k) ->
              ignore ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), (k - 1)) in
        let rec copyNames arg__0 arg__1 =
          match (arg__0, arg__1) with
          | ((Shift n, (Decl _ as __g)), Psi1) ->
              copyNames ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __g)
                Psi1
          | ((Dot (Exp _, s), Decl (__g, _)), Psi1) -> copyNames (s, __g) Psi1
          | ((Dot (Idx k, s), Decl (__g, Dec (None, _))), Psi1) ->
              copyNames (s, __g) Psi1
          | ((Dot (Idx k, s), Decl (__g, Dec (Some name, _))), Psi1) ->
              let Psi1' = namePsi (Psi1, k, name) in copyNames (s, __g) Psi1'
          | ((Shift _, I.Null), Psi1) -> Psi1 in
        let rec psiName' =
          function
          | I.Null -> I.Null
          | Decl (Psi, __d) ->
              let Psi' = psiName' Psi in
              I.Decl (Psi', (decName ((F.makectx Psi'), __d))) in
        psiName' (copyNames ((ignore (s, l)), (F.makectx Psi2)) Psi1) in
      let rec merge =
        function
        | (G1, I.Null) -> G1
        | (G1, Decl (G2, __d)) -> I.Decl ((merge (G1, G2)), __d) in
      let rec formatCtx (Psi, __g) =
        let G0 = F.makectx Psi in
        let rec formatCtx' =
          function
          | I.Null -> nil
          | Decl (I.Null, Dec (Some name, __v)) ->
              [Fmt.String name; Fmt.String ":"; Print.formatExp (G0, __v)]
          | Decl (__g, Dec (Some name, __v)) ->
              (formatCtx' __g) @
                [Fmt.String ",";
                Fmt.Break;
                Fmt.String name;
                Fmt.String ":";
                Print.formatExp ((merge (G0, __g)), __v)] in
        Fmt.hbox ((Fmt.String "|") :: ((formatCtx' __g) @ [Fmt.String "|"])) in
      let rec formatTuple (Psi, P) =
        let rec formatTuple' =
          function
          | F.Unit -> nil
          | Inx (M, F.Unit) -> [Print.formatExp ((F.makectx Psi), M)]
          | Inx (M, __P') ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatTuple' __P' in
        match P with
        | Inx (_, F.Unit) -> Fmt.hbox (formatTuple' P)
        | _ ->
            Fmt.hVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"])) in
      let rec formatSplitArgs (Psi, __l) =
        let rec formatSplitArgs' =
          function
          | nil -> nil
          | (M)::nil -> [Print.formatExp ((F.makectx Psi), M)]
          | (M)::__l ->
              (::) (((::) (Print.formatExp ((F.makectx Psi), M)) Fmt.String
                       ",")
                      :: Fmt.Break)
                formatSplitArgs' __l in
        if (List.length __l) = 1
        then Fmt.hbox (formatSplitArgs' __l)
        else
          Fmt.hVbox0 1 1 1
            ((Fmt.String "(") :: ((formatSplitArgs' __l) @ [Fmt.String ")"])) in
      let rec frontToExp =
        function | Idx k -> I.Root ((I.BVar k), I.Nil) | Exp (__u) -> __u in
      let rec formatDecs1 =
        function
        | (Psi, Split (xx, __Ds), Dot (Ft, s1), __l) ->
            formatDecs1 (Psi, __Ds, s1, ((frontToExp Ft) :: __l))
        | (Psi, F.Empty, s1, __l) -> __l
        | (Psi, __Ds, Shift n, __l) ->
            formatDecs1
              (Psi, __Ds, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __l) in
      let rec formatDecs0 =
        function
        | (Psi, App ((xx, M), __Ds)) ->
            let (__Ds', S) = formatDecs0 (Psi, __Ds) in (__Ds', (I.App (M, S)))
        | (Psi, __Ds) -> (__Ds, I.Nil) in
      let rec formatDecs =
        function
        | (index, Psi, (App ((xx, _), P) as __Ds), (Psi1, s1)) ->
            let (__Ds', S) = formatDecs0 (Psi, __Ds) in
            let __l' = formatDecs1 (Psi, __Ds', s1, nil) in
            let name = nameLookup index in
            Fmt.hbox
              [formatSplitArgs (Psi1, __l');
              Fmt.space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.hVbox
                ((::) ((Fmt.String name) :: Fmt.Break) Print.formatSpine
                   ((F.makectx Psi), S))]
        | (index, Psi, New ((CtxBlock (_, __g) as B), __Ds), (Psi1, s1)) ->
            let B' = ctxBlockName ((F.makectx Psi), B) in
            let fmt =
              formatDecs
                (index, (I.Decl (Psi, (F.Block B'))), __Ds, (Psi1, s1)) in
            Fmt.vbox [formatCtx (Psi, __g); Fmt.Break; fmt]
        | (index, Psi, Lemma (lemma, __Ds), (Psi1, s1)) ->
            let (__Ds', S) = formatDecs0 (Psi, __Ds) in
            let __l' = formatDecs1 (Psi, __Ds', s1, nil) in
            let LemmaDec (names, _, _) = F.lemmaLookup lemma in
            Fmt.hbox
              [formatSplitArgs (Psi1, __l');
              Fmt.space;
              Fmt.String "=";
              Fmt.Break;
              Fmt.hVbox
                ((::) ((Fmt.String (List.nth (names, index))) :: Fmt.Break)
                   Print.formatSpine ((F.makectx Psi), S))]
        | (index, Psi, Left (_, __Ds), (Psi1, s1)) ->
            let fmt = formatDecs (index, Psi, __Ds, (Psi1, s1)) in fmt
        | (index, Psi, Right (_, __Ds), (Psi1, s1)) ->
            let fmt = formatDecs ((index + 1), Psi, __Ds, (Psi1, s1)) in fmt in
      let rec formatLet =
        function
        | (Psi, Let (__Ds, Case (Opts ((Psi1, s1, (Let _ as __P1))::nil))), fmts)
            ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits __Ds)) in
            let fmt = formatDecs (0, Psi, __Ds, (Psi1', s1)) in
            formatLet (Psi1', __P1, (fmts @ [fmt; Fmt.Break]))
        | (Psi, Let (__Ds, Case (Opts ((Psi1, s1, __P1)::nil))), fmts) ->
            let Psi1' = psiName (Psi1, s1, Psi, (numberOfSplits __Ds)) in
            let fmt = formatDecs (0, Psi, __Ds, (Psi1', s1)) in
            Fmt.vbox0 0 1
              [Fmt.String "let";
              Fmt.Break;
              Fmt.spaces 2;
              Fmt.vbox0 0 1 (fmts @ [fmt]);
              Fmt.Break;
              Fmt.String "in";
              Fmt.Break;
              Fmt.spaces 2;
              formatPro3 (Psi1', __P1);
              Fmt.Break;
              Fmt.String "end"]
      and formatPro3 =
        function
        | (Psi, (F.Unit as P)) -> formatTuple (Psi, P)
        | (Psi, (Inx _ as P)) -> formatTuple (Psi, P)
        | (Psi, (Let _ as P)) -> formatLet (Psi, P, nil) in
      let rec argsToSpine =
        function
        | (s, I.Null, S) -> S
        | (Shift n, Psi, S) ->
            argsToSpine
              ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), Psi, S)
        | (Dot (Ft, s), Decl (Psi, __d), S) ->
            argsToSpine (s, Psi, (I.App ((frontToExp Ft), S))) in
      let rec formatHead (index, Psi', s, Psi) =
        Fmt.hbox
          [Fmt.space;
          Fmt.hVbox
            ((::) ((Fmt.String (nameLookup index)) :: Fmt.Break)
               Print.formatSpine
               ((F.makectx Psi'), (argsToSpine (s, Psi, I.Nil))))] in
      let rec formatPro2 =
        function
        | (index, Psi, nil) -> nil
        | (index, Psi, (Psi', s, P)::nil) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            let fhead = if index = 0 then "fun" else "and" in
            [Fmt.hVbox0 1 5 1
               [Fmt.String fhead;
               formatHead (index, Psi'', s, Psi);
               Fmt.space;
               Fmt.String "=";
               Fmt.Break;
               formatPro3 (Psi'', P)];
            Fmt.Break]
        | (index, Psi, (Psi', s, P)::O) ->
            let Psi'' = psiName (Psi', s, Psi, 0) in
            (formatPro2 (index, Psi, O)) @
              [Fmt.hVbox0 1 5 1
                 [Fmt.String "  |";
                 formatHead (index, Psi'', s, Psi);
                 Fmt.space;
                 Fmt.String "=";
                 Fmt.Break;
                 formatPro3 (Psi'', P)];
              Fmt.Break] in
      let rec formatPro1 =
        function
        | (index, Psi, Lam (__d, P)) ->
            formatPro1
              (index, (I.Decl (Psi, (decName ((F.makectx Psi), __d)))), P)
        | (index, Psi, Case (Opts (__Os))) -> formatPro2 (index, Psi, __Os)
        | (index, Psi, Pair (__P1, __P2)) ->
            (@) (formatPro1 (index, Psi, __P1)) formatPro1
              ((index + 1), Psi, __P2) in
      let rec formatPro0 (Psi, Rec (DD, P)) =
        Fmt.vbox0 0 1 (formatPro1 (0, Psi, P)) in
      Names.varReset I.Null; formatPro0 Args
    let rec formatLemmaDec (LemmaDec (names, P, F)) =
      Fmt.vbox0 0 1
        [formatFor (I.Null, F) names; Fmt.Break; formatPro (I.Null, P) names]
    let rec forToString (Args) names =
      Fmt.makestring_fmt (formatFor Args names)
    let rec proToString (Args) names =
      Fmt.makestring_fmt (formatPro Args names)
    let rec lemmaDecToString (Args) =
      Fmt.makestring_fmt (formatLemmaDec Args)
    (* Invariant:

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
    (* formatCtxBlock (__g, (G1, s1)) = (__g', s', fmts')

       Invariant:
       If   |- __g ctx
       and  __g |- G1 ctx
       and  G2 |- s1 : __g
       then __g' = G2, G1 [s1]
       and  __g' |- s' : __g, G1
       and  fmts is a format list of G1[s1]
    *)
    (* formatFor' (__g, (F, s)) = fmts'

       Invariant:
       If   |- __g ctx
       and  __g |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
    (* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = __F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *)
    (* formatFor1 (index, __g, (F, s)) = fmts'

           Invariant:
           If   |- __g ctx
           and  __g |- s : Psi
           and  Psi |- __F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *)
    (* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (__P1, __P2, .. Pn) in F
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
    (* decName (__g, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
    (* numberOfSplits __Ds = n'

           Invariant:
           If   Psi, Delta |- __Ds :: Psi', Delta'
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
    (* merge (G1, G2) = __g'

           Invariant:
           __g' = G1, G2
        *)
    (* formatCtx (Psi, __g) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- __g ctx
           then fmt' is a pretty print format of __g
        *)
    (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
    (* formatSplitArgs (Psi, __l) = fmt'

           Invariant:
           If   |- Psi ctx
           and  __l = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
    (* frontToExp (Ft) = __u'

           Invariant:
           __g |- Ft = __u' : __v   for a __g, __v
        *)
    (* formatDecs1 (Psi, __Ds, s, __l) = __l'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- __Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                __l = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then __l' extends __l
           s.t. __l = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        *)
    (* formatDecs0 (Psi, __Ds) = (__Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- __Ds : Psi', Delta'
           and  __Ds = App M1 ... App Mn __Ds'   (where __Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- __Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
    (* formatDecs (index, Psi, __Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- __Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of __Ds
        *)
    (* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case __P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for __P'
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
    (* formatPro2 (index, Psi, __l) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- __l a list of cases
           then fmts' list of pretty print formats of __l
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
        *)
    let formatFor = formatFor
    let formatForBare = formatForBare
    let formatPro = formatPro
    let formatLemmaDec = formatLemmaDec
    let forToString = forToString
    let proToString = proToString
    let lemmaDecToString = lemmaDecToString
  end ;;
