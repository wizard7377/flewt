
module type TOMEGAPRINT  =
  sig
    module Formatter : FORMATTER
    exception Error of string 
    val formatFor :
      Tomega.__Dec IntSyn.__Ctx -> Tomega.__For -> Formatter.format
    val forToString : Tomega.__Dec IntSyn.__Ctx -> Tomega.__For -> string
    val formatFun :
      (string list * Tomega.lemma list) -> Tomega.__Prg -> Formatter.format
    val formatPrg :
      Tomega.__Dec IntSyn.__Ctx -> Tomega.__Prg -> Formatter.format
    val funToString :
      (string list * Tomega.lemma list) -> Tomega.__Prg -> string
    val evarReset : unit -> unit
    val evarName : string -> Tomega.__Prg
    val nameEVar : Tomega.__Prg -> string
    val prgToString : Tomega.__Dec IntSyn.__Ctx -> Tomega.__Prg -> string
    val nameCtx : Tomega.__Dec IntSyn.__Ctx -> Tomega.__Dec IntSyn.__Ctx
    val formatCtx : Tomega.__Dec IntSyn.__Ctx -> Formatter.format
    val ctxToString : Tomega.__Dec IntSyn.__Ctx -> string
  end;;




module TomegaPrint(TomegaPrint:sig
                                 module Formatter : FORMATTER
                                 module Names : NAMES
                                 module Print : PRINT
                               end) : TOMEGAPRINT =
  struct
    module Formatter = Formatter
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module Fmt = Formatter
    module P = Print
    let (evarList : T.__Prg list ref) = ref nil
    let rec evarReset () = evarList := nil
    let rec evarName n =
      let rec evarName' =
        function
        | nil -> raise (Error "not found")
        | (EVar (_, _, _, _, _, (EVar (_, __G, r, _) as X)) as Y)::__L ->
            if (Names.evarName (__G, __X)) = n then __Y else evarName' __L in
      evarName' (!evarList)
    let rec nameEVar (EVar (_, _, _, _, _, (EVar (_, __G, r, _) as X))) =
      Names.evarName (__G, __X)
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
    let rec constName c = I.conDecName (I.sgnLookup c)
    let rec formatWorld =
      function
      | nil -> []
      | c::[] -> [Fmt.String (constName c)]
      | c::cids ->
          (@) [Fmt.String (constName c); Fmt.String ","; Fmt.Break]
            formatWorld cids
    let rec formatFor' __2__ __3__ =
      match (__2__, __3__) with
      | (Psi, All ((__D, T.Explicit), __F)) ->
          (match __D with
           | UDec (__D) ->
               let __G = T.coerceCtx Psi in
               let __D' = Names.decName (__G, __D) in
               (@) [Fmt.String "all {";
                   P.formatDec (__G, __D');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec __D'))), __F))
      | (Psi, All ((__D, T.Implicit), __F)) ->
          (match __D with
           | UDec (__D) ->
               let __G = T.coerceCtx Psi in
               let __D' = Names.decName (__G, __D) in
               (@) [Fmt.String "all^ {";
                   P.formatDec (__G, __D');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec __D'))), __F))
      | (Psi, Ex ((__D, T.Explicit), __F)) ->
          let __G = T.coerceCtx Psi in
          let __D' = Names.decName (__G, __D) in
          (@) [Fmt.String "exists {";
              P.formatDec (__G, __D');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec __D'))), __F)
      | (Psi, Ex ((__D, T.Implicit), __F)) ->
          let __G = T.coerceCtx Psi in
          let __D' = Names.decName (__G, __D) in
          (@) [Fmt.String "exists^ {";
              P.formatDec (__G, __D');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec __D'))), __F)
      | (Psi, And (__F1, __F2)) ->
          [Fmt.String "(";
          Fmt.HVbox (formatFor' (Psi, __F1));
          Fmt.String ")";
          Fmt.Break;
          Fmt.String "/\\";
          Fmt.Space;
          Fmt.String "(";
          Fmt.HVbox (formatFor' (Psi, __F2));
          Fmt.String ")"]
      | (Psi, T.True) -> [Fmt.String "true"]
      | (Psi, World (Worlds (__L), __F)) ->
          (@) [Fmt.String "world (";
              Fmt.HVbox (formatWorld __L);
              Fmt.String ")";
              Fmt.Break]
            formatFor' (Psi, __F)
    let rec formatFor (__G) (__F) =
      Fmt.HVbox (formatFor' (__G, (T.forSub (__F, T.id))))
    let rec forToString (Psi) (__F) =
      Fmt.makestring_fmt (formatFor (Psi, __F))
    let rec decName __4__ __5__ =
      match (__4__, __5__) with
      | (__G, UDec (__D)) -> T.UDec (Names.decName (__G, __D))
      | (__G, PDec (None, __F, TC1, TC2)) ->
          T.PDec ((Some "xx"), __F, TC1, TC2)
      | (__G, __D) -> __D(* needs to be integrated with Names *)
    let rec psiName (Psi1) s (Psi2) l =
      let rec nameDec __6__ __7__ =
        match (__6__, __7__) with
        | ((Dec (Some _, _) as D), name) -> __D
        | (Dec (None, __V), name) -> I.Dec ((Some name), __V) in
      let rec namePsi __8__ __9__ __10__ =
        match (__8__, __9__, __10__) with
        | (Decl (Psi, UDec (__D)), 1, name) ->
            I.Decl (Psi, (T.UDec (nameDec (__D, name))))
        | (Decl (Psi, (UDec (__D) as LD)), n, name) ->
            I.Decl ((namePsi (Psi, (n - 1), name)), LD)
      and nameG __11__ __12__ __13__ __14__ __15__ =
        match (__11__, __12__, __13__, __14__, __15__) with
        | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
        | (Psi, Decl (__G, __D), 1, name, k) ->
            (Psi, (I.Decl (__G, (nameDec (__D, name)))))
        | (Psi, Decl (__G, __D), n, name, k) ->
            let (Psi', __G') = nameG (Psi, __G, (n - 1), name, k) in
            (Psi', (I.Decl (__G', __D))) in
      let rec ignore __16__ __17__ =
        match (__16__, __17__) with
        | (s, 0) -> s
        | (Dot (_, s), k) -> ignore (s, (k - 1))
        | (Shift n, k) ->
            ignore ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), (k - 1)) in
      let rec copyNames __18__ __19__ __20__ =
        match (__18__, __19__, __20__) with
        | (Shift n, (Decl _ as G), Psi1) ->
            copyNames ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), __G)
              Psi1
        | (Dot (Exp _, s), Decl (__G, _), Psi1) -> copyNames (s, __G) Psi1
        | (Dot (Idx k, s), Decl (__G, UDec (Dec (None, _))), Psi1) ->
            copyNames (s, __G) Psi1
        | (Dot (Idx k, s), Decl (__G, UDec (Dec (Some name, _))), Psi1) ->
            let Psi1' = namePsi (Psi1, k, name) in copyNames (s, __G) Psi1'
        | (Dot (Prg k, s), Decl (__G, PDec (None, _, _, _)), Psi1) ->
            copyNames (s, __G) Psi1
        | (Dot (Prg k, s), Decl (__G, PDec (Some name, _, _, _)), Psi1) ->
            copyNames (s, __G) Psi1
        | (Shift _, I.Null, Psi1) -> Psi1 in
      let rec psiName' =
        function
        | I.Null -> I.Null
        | Decl (Psi, __D) ->
            let Psi' = psiName' Psi in
            I.Decl (Psi', (decName ((T.coerceCtx Psi'), __D))) in
      psiName' ((Psi1)
        (* copyNames  (ignore (s, l),  Psi2) *))
    let rec fmtSpine __21__ __22__ __23__ =
      match (__21__, __22__, __23__) with
      | (callname, Psi, T.Nil) -> []
      | (callname, Psi, AppExp (__U, __S)) ->
          (::) (Fmt.HVbox
                  (Print.formatSpine
                     ((T.coerceCtx Psi), (I.App (__U, I.Nil)))))
            fmtSpine' callname (Psi, __S)
      | (callname, Psi, AppPrg (__P, __S)) ->
          (::) (formatPrg3 callname (Psi, __P)) fmtSpine' callname (Psi, __S)
      (* Print.formatExp (T.coerceCtx Psi, U) *)
    let rec fmtSpine' __24__ __25__ __26__ =
      match (__24__, __25__, __26__) with
      | (callname, Psi, T.Nil) -> []
      | (callname, Psi, __S) -> (::) Fmt.Break fmtSpine callname (Psi, __S)
    let rec argsToSpine __27__ __28__ __29__ =
      match (__27__, __28__, __29__) with
      | (s, 0, __S) -> __S
      | (Shift n, k, __S) ->
          argsToSpine ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), k, __S)
      | (Dot (Idx n, s), k, __S) ->
          argsToSpine
            (s, (k - 1), (T.AppExp ((I.Root ((I.BVar n), I.Nil)), __S)))
      | (Dot (Exp (__U), s), k, __S) ->
          argsToSpine (s, (k - 1), (T.AppExp (__U, __S)))
      | (Dot (Prg (__P), s), k, __S) ->
          argsToSpine (s, (k - 1), (T.AppPrg (__P, __S)))
    let rec formatTuple (Psi) (__P) =
      let rec formatTuple' =
        function
        | T.Unit -> nil
        | PairExp (__M, T.Unit) -> [Print.formatExp ((T.coerceCtx Psi), __M)]
        | PairExp (__M, __P') ->
            (::) (((::) (Print.formatExp ((T.coerceCtx Psi), __M)) Fmt.String
                     ",")
                    :: Fmt.Break)
              formatTuple' __P' in
      match __P with
      | PairExp (_, T.Unit) -> Fmt.Hbox (formatTuple' __P)
      | _ ->
          Fmt.HVbox0 1 1 1
            ((Fmt.String "(") :: ((formatTuple' __P) @ [Fmt.String ")"]))
    let rec formatRedex __30__ __31__ __32__ __33__ =
      match (__30__, __31__, __32__, __33__) with
      | (callname, Psi, Var k, __S) ->
          let PDec (Some name, _, _, _) = I.ctxLookup (Psi, k) in
          let Fspine = fmtSpine callname (Psi, __S) in
          Fmt.Hbox
            [Fmt.Space;
            Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, Psi, Const l, __S) ->
          let ValDec (name, _, _) = T.lemmaLookup l in
          let Fspine = fmtSpine callname (Psi, __S) in
          Fmt.Hbox
            [Fmt.Space;
            Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, Psi, Redex (Const l, _), __S) ->
          let name = callname l in
          let Fspine = fmtSpine callname (Psi, __S) in
          ((Fmt.Hbox
              [Fmt.Space;
              Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)])
            (* val T.ValDec (name, _, _) = T.lemmaLookup l *))(* mutual recursion, k is the projection function *)
      (* lemma application *)(* no mutual recursion, recursive call *)
    let rec formatCase callname max (Psi') s (Psi) =
      let __S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', __S) in
      Fmt.Hbox [Fmt.HVbox Fspine]
    let rec formatCases __34__ __35__ __36__ __37__ =
      match (__34__, __35__, __36__, __37__) with
      | (max, Psi, nil, callname) -> nil
      | (max, Psi, (Psi', s, __P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          [Fmt.HVbox0 1 5 1
             [formatCase callname (max, Psi'', s, Psi);
             Fmt.Space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', __P)];
          Fmt.Break]
      | (max, Psi, (Psi', s, __P)::__O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          (formatCases (max, Psi, __O, callname)) @
            [Fmt.HVbox0 1 5 1
               [Fmt.String "|";
               Fmt.Space;
               formatCase callname (max, Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', __P)];
            Fmt.Break]
    let rec formatPrg3 __38__ __39__ __40__ =
      match (__38__, __39__, __40__) with
      | (callname, Psi, T.Unit) -> Fmt.String "<>"
      | (callname, Psi, PairExp (__U, __P)) ->
          Fmt.HVbox
            [Fmt.String "<";
            Print.formatExp ((T.coerceCtx Psi), __U);
            Fmt.String ",";
            Fmt.Break;
            formatPrg3 callname (Psi, __P);
            Fmt.String ">"]
      | (callname, Psi, (Let _ as P)) -> formatLet callname (Psi, __P, nil)
      | (callname, Psi, (LetPairExp (__D1, __D2, __P1, __P2) as P)) ->
          formatLet callname (Psi, __P, nil)
      | (callname, Psi, (LetUnit (__P1, __P2) as P)) ->
          formatLet callname (Psi, __P, nil)
      | (callname, Psi, (New (Lam (UDec (BDec (l, (c, s))), _)) as P)) ->
          formatNew callname (Psi, __P, nil)
      | (callname, Psi, Redex (__P, __S)) ->
          formatRedex callname (Psi, __P, __S)
      | (callname, Psi, Lam ((UDec (__D') as D), __P)) ->
          Fmt.HVbox
            [Fmt.String "lam";
            Fmt.Space;
            Fmt.String "(";
            Print.formatDec ((T.coerceCtx Psi), __D');
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, __D)), __P)]
      | (callname, Psi, Rec ((PDec (Some name, __F, None, None) as D), __P))
          ->
          Fmt.HVbox
            [Fmt.String "fix*";
            Fmt.Space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, __F);
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, __D)), __P)]
      | (callname, Psi, Rec
         ((PDec (Some name, __F, Some (TC1), Some (TC2)) as D), __P)) ->
          Fmt.HVbox
            [Fmt.String "fix";
            Fmt.Space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, __F);
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, __D)), __P)]
      | (callname, Psi, PClo (__P, t)) ->
          Fmt.HVbox [formatPrg3 callname (Psi, __P); Fmt.String "..."]
      | (callname, Psi,
         (EVar (_, { contents = Some (__P) }, _, _, _, _) as X)) ->
          formatPrg3 callname (Psi, __P)
      | (callname, Psi, (EVar (_, { contents = None }, _, _, _, _) as X)) ->
          Fmt.String (nameEVar __X)
      | (callname, Psi, Case (Cases (__Cs))) ->
          Fmt.HVbox
            (((::) ((Fmt.String "case") :: Fmt.Break) formatCases
                (1, Psi, __Cs, callname))
               @ [Fmt.String "."])
      | (callname, Psi, Var n) ->
          let PDec (Some n, _, _, _) = I.ctxLookup (Psi, n) in Fmt.String n
      | (callname, _) -> Fmt.String "missing case"(* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *)
      (* formatTuple (Psi, P) *)(* formatTuple (Psi, P) *)
    let rec formatNew __41__ __42__ __43__ __44__ =
      match (__41__, __42__, __43__, __44__) with
      | (callname, Psi, New (Lam (UDec (BDec (l, (c, s)) as D), __P)), fmts)
          ->
          let __G = T.coerceCtx Psi in
          let __D' = Names.decName (__G, __D) in
          formatNew callname
            ((I.Decl (Psi, (T.UDec __D'))), __P,
              (((::) Fmt.Break Fmt.HVbox [Print.formatDec (__G, __D')]) ::
                 fmts))
      | (callname, Psi, __P, fmts) ->
          Fmt.Vbox0 0 1
            [Fmt.String "new";
            Fmt.Vbox0 0 1 fmts;
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname (Psi, __P);
            Fmt.Break;
            Fmt.String "end"]
    let rec formatLet __45__ __46__ __47__ __48__ =
      match (__45__, __46__, __47__, __48__) with
      | (callname, Psi, Let
         (__D, __P1, Case (Cases ((Psi1, s1, (Let _ as P2))::nil))), fmts) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let __F1 = Fmt.HVbox [formatPrg3 callname (Psi, __P1)] in
          let __S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, __S) in
          let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
          let Fbody = Fmt.HVbox [__F1] in
          let fmt =
            Fmt.HVbox
              [Fmt.HVbox
                 [Fmt.String "val";
                 Fmt.Space;
                 Fpattern;
                 Fmt.Space;
                 Fmt.String "="];
              Fmt.Break;
              Fbody] in
          ((formatLet callname (Psi1', __P2, (fmts @ [Fmt.Break; fmt])))
            (* was I.ctxLength Psi - max  --cs *)(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *))
      | (callname, Psi, Let
         (__D, __P1, Case (Cases ((Psi1, s1, __P2)::nil))), fmts) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let __F1 = Fmt.HVbox [formatPrg3 callname (Psi, __P1)] in
          let __S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, __S) in
          let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
          let Fbody = Fmt.HVbox [__F1] in
          let fmt =
            Fmt.HVbox
              [Fmt.HVbox
                 [Fmt.String "val";
                 Fmt.Space;
                 Fpattern;
                 Fmt.Space;
                 Fmt.String "="];
              Fmt.Break;
              Fbody] in
          ((Fmt.Vbox0 0 1
              [Fmt.String "let";
              Fmt.Vbox0 2 1 (fmts @ [Fmt.Break; fmt]);
              Fmt.Break;
              Fmt.String "in";
              Fmt.Break;
              Fmt.Spaces 2;
              formatPrg3 callname (Psi1', __P2);
              Fmt.Break;
              Fmt.String "end"])
            (* was I.ctxLength Psi - max  --cs *)(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
            (*            val fmt =  formatDecs (0, Psi, Ds, (Psi1', s1)) *))
      | (callname, Psi, Let (__D, __P1, Case (Cases (__L))), nil) ->
          let rec fmtCaseRest =
            function
            | [] -> []
            | (Psi1, s1, __P2)::__L ->
                let Psi1' = psiName (Psi1, s1, Psi, 1) in
                let __S = argsToSpine (s1, 1, T.Nil) in
                let Fspine = fmtSpine callname (Psi1, __S) in
                let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
                (@) [Fmt.HVbox
                       [Fmt.Space;
                       Fmt.String "|";
                       Fmt.Space;
                       Fpattern;
                       Fmt.Space;
                       Fmt.String "-->"];
                    Fmt.Spaces 2;
                    Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', __P2)];
                    Fmt.Break]
                  fmtCaseRest __L in
          let rec fmtCase ((Psi1, s1, __P2)::__L) =
            let Psi1' = psiName (Psi1, s1, Psi, 1) in
            let __S = argsToSpine (s1, 1, T.Nil) in
            let Fspine = fmtSpine callname (Psi1, __S) in
            let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
            Fmt.Vbox0 0 1
              ((@) [Fmt.HVbox
                      [Fmt.String "of";
                      Fmt.Space;
                      Fpattern;
                      Fmt.Space;
                      Fmt.String "-->"];
                   Fmt.Spaces 2;
                   Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', __P2)];
                   Fmt.Break]
                 fmtCaseRest __L) in
          let __F1 = Fmt.HVbox [formatPrg3 callname (Psi, __P1)] in
          let Fbody = Fmt.HVbox [__F1] in
          let fmt = fmtCase __L in
          Fmt.Vbox0 0 1
            (([Fmt.String "case (";
              Fbody;
              Fmt.Space;
              Fmt.String ")";
              Fmt.Break;
              fmt])
            (* need space since there is one before Fbody *))
      | (callname, Psi, (Let (__D, __P1, Case (Cases (__L))) as R), fmts) ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Vbox0 0 1 (fmts @ [Fmt.Break]);
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatLet callname (Psi, __R, nil);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, Psi,
         (Let ((PDec (Some name, __F, _, _) as D), __P1, __P2) as R), fmts)
          ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.Vbox0 0 1
              [Fmt.String name;
              Fmt.Space;
              Fmt.String "=";
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname ((I.Decl (Psi, __D)), __P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, Psi,
         (LetPairExp
            ((Dec (Some n1, _) as D1), (PDec (Some n2, __F, _, _) as D2),
             __P1, __P2)
            as R),
         fmts) ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.Spaces 2;
            Fmt.Vbox0 0 1
              [Fmt.String "(";
              Fmt.String n1;
              Fmt.String ",";
              Fmt.Space;
              Fmt.String n2;
              Fmt.String ")";
              Fmt.Space;
              Fmt.String "=";
              Fmt.Space;
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname
              ((I.Decl ((I.Decl (Psi, (T.UDec __D1))), __D2)), __P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, Psi, (LetUnit (__P1, __P2) as R), fmts) ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.Spaces 2;
            Fmt.Vbox0 0 1
              [Fmt.String "()";
              Fmt.Space;
              Fmt.String "=";
              Fmt.Space;
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname (Psi, __P2);
            Fmt.Break;
            Fmt.String "end"](* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)
    let rec formatHead callname name (max, index) (Psi') s (Psi) =
      let __S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', __S) in
      ((Fmt.Hbox
          [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)])
        (*            val T.PDec (Some name, _) = I.ctxLookup (Psi, index) *)
        (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *))
    let rec formatPrg2 __49__ __50__ __51__ __52__ __53__ =
      match (__49__, __50__, __51__, __52__, __53__) with
      | (name, (max, index), Psi, nil, callname) -> nil
      | (name, (max, index), Psi, (Psi', s, __P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let fhead = if (=) index I.ctxLength Psi then "fun" else "and" in
          [Fmt.HVbox0 1 5 1
             [Fmt.String fhead;
             formatHead callname (name, (max, index), Psi'', s, Psi);
             Fmt.Space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', __P)];
          Fmt.Break]
      | (name, (max, index), Psi, (Psi', s, __P)::__O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          (formatPrg2 (name, (max, index), Psi, __O, callname)) @
            [Fmt.HVbox0 1 5 1
               [Fmt.String "  |";
               formatHead callname (name, (max, index), Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', __P)];
            Fmt.Break]
    let rec formatPrg11 __54__ __55__ __56__ __57__ __58__ =
      match (__54__, __55__, __56__, __57__, __58__) with
      | (name, (max, index), Psi, Lam (__D, __P), callname) ->
          formatPrg11
            (name, (max, (index + 1)),
              (I.Decl (Psi, (decName ((T.coerceCtx Psi), __D)))), __P,
              callname)
      | (name, (max, index), Psi, Case (Cases (__Os)), callname) ->
          formatPrg2 (name, (max, index), Psi, __Os, callname)
    let rec formatPrg1 __59__ __60__ __61__ __62__ __63__ =
      match (__59__, __60__, __61__, __62__, __63__) with
      | (name::names, (max, index), Psi, PairPrg (__P1, __P2), callname) ->
          (@) (formatPrg11 (name, (max, index), Psi, __P1, callname))
            formatPrg1 (names, (max, (index - 1)), Psi, __P2, callname)
      | (name::[], (max, index), Psi, __P, callname) ->
          formatPrg11 (name, (max, index), Psi, __P, callname)
    let rec lookup (name::names) (proj::projs) lemma =
      if lemma = proj then name else lookup (names, projs) lemma
    let rec formatPrg0 (names, projs) (Rec
      ((PDec (Some _, __F, _, _) as D), __P)) =
      let max = 1 in
      ((Fmt.Vbox0 0 1
          (formatPrg1
             (names, (max, max), (I.Decl (I.Null, __D)), __P,
               (fun lemma -> lookup (names, projs) lemma))))
        (* number of ih. *))
    let rec formatFun (Args) = Names.varReset I.Null; formatPrg0 Args
    let rec funToString (Args) = Fmt.makestring_fmt (formatFun Args)
    let rec prgToString (Args) =
      Fmt.makestring_fmt (formatPrg3 (fun _ -> "?") Args)
    let rec nameCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, UDec (__D)) ->
          I.Decl
            ((nameCtx Psi),
              (T.UDec (Names.decName ((T.coerceCtx Psi), __D))))
      | Decl (Psi, PDec (None, __F, TC1, TC2)) ->
          let Psi' = nameCtx Psi in
          let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec None)) in
          I.Decl (Psi', (T.PDec (x, __F, TC1, TC2)))
      | Decl (Psi, (PDec (Some n, __F, _, _) as D)) ->
          I.Decl ((nameCtx Psi), __D)
    let rec flag = function | None -> "" | Some _ -> "*"
    let rec formatCtx =
      function
      | I.Null -> []
      | Decl (I.Null, UDec (__D)) ->
          if (!Global.chatter) >= 4
          then [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, __D)]]
          else [Print.formatDec (I.Null, __D)]
      | Decl (I.Null, PDec (Some s, __F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.Space;
               Fmt.String ((^) "::" flag TC1);
               Fmt.Space;
               formatFor (I.Null, __F)]]
          else
            [Fmt.String s;
            Fmt.Space;
            Fmt.String ((^) "::" flag TC1);
            Fmt.Space;
            formatFor (I.Null, __F)]
      | Decl (Psi, UDec (__D)) ->
          let __G = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox [Fmt.Break; Print.formatDec (__G, __D)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__G, __D)]
      | Decl (Psi, PDec (Some s, __F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String ((^) "::" flag TC1);
                 Fmt.Space;
                 formatFor (Psi, __F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.Space;
              Fmt.String ((^) "::" flag TC1);
              Fmt.Space;
              formatFor (Psi, __F)]
    let rec ctxToString (Psi) =
      Fmt.makestring_fmt (Fmt.HVbox (formatCtx Psi))
    let formatFor = formatFor
    let forToString = forToString
    let formatFun = formatFun
    let formatPrg = formatPrg3 (fun _ -> "?")
    let evarName = evarName
    let evarReset = evarReset
    let nameEVar = nameEVar
    let prgToString = prgToString
    let funToString = funToString
    let nameCtx = nameCtx
    let formatCtx (Psi) = Fmt.HVbox (formatCtx Psi)
    let ctxToString = ctxToString
  end ;;
