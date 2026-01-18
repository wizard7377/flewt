
(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module type TOMEGAPRINT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA  !*)
    module Formatter : FORMATTER
    exception Error of string 
    val formatFor :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__For) -> Formatter.format
    val forToString : (Tomega.__Dec IntSyn.__Ctx * Tomega.__For) -> string
    val formatFun :
      ((string list * Tomega.lemma list) * Tomega.__Prg) -> Formatter.format
    val formatPrg :
      (Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg) -> Formatter.format
    (*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)
    val funToString :
      ((string list * Tomega.lemma list) * Tomega.__Prg) -> string
    (* funToString ((names, projs), P)  = s
     cids is the list of mututal recursive type families.  (could also be names)
     projs are the projection functions used internally,  They must be in the
     same order as names.  The nth name corresponds to the nth projection function
  *)
    val evarReset : unit -> unit
    val evarName : string -> Tomega.__Prg
    val nameEVar : Tomega.__Prg -> string
    val prgToString : (Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg) -> string
    val nameCtx : Tomega.__Dec IntSyn.__Ctx -> Tomega.__Dec IntSyn.__Ctx
    val formatCtx : Tomega.__Dec IntSyn.__Ctx -> Formatter.format
    val ctxToString : Tomega.__Dec IntSyn.__Ctx -> string
  end;;




(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module TomegaPrint(TomegaPrint:sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure Tomega' : TOMEGA !*)
                                 (*! sharing Tomega'.IntSyn = IntSyn' !*)
                                 (*   structure Normalize : NORMALIZE *)
                                 (*! sharing Normalize.IntSyn = IntSyn' !*)
                                 (*! sharing Normalize.Tomega = Tomega' !*)
                                 module Formatter : FORMATTER
                                 module Names : NAMES
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 module Print : PRINT
                               end) : TOMEGAPRINT =
  struct
    (*! sharing Print.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module Formatter = Formatter
    exception Error of string 
    (* is just here because we don't have a
     module yet for names. move later
     --cs Tue Apr 27 12:04:45 2004 *)
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
        | (EVar (_, _, _, _, _, (EVar (_, G, r, _) as X)) as Y)::L ->
            if (Names.evarName (G, X)) = n then Y else evarName' L in
      evarName' (!evarList)
    let rec nameEVar (EVar (_, _, _, _, _, (EVar (_, G, r, _) as X))) =
      Names.evarName (G, X)
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
    let rec constName c = I.conDecName (I.sgnLookup c)
    let rec formatWorld =
      function
      | nil -> []
      | c::[] -> [Fmt.String (constName c)]
      | c::cids ->
          (@) [Fmt.String (constName c); Fmt.String ","; Fmt.Break]
            formatWorld cids
    let rec formatFor' =
      function
      | (Psi, All ((D, T.Explicit), F)) ->
          (match D with
           | UDec (D) ->
               let G = T.coerceCtx Psi in
               let D' = Names.decName (G, D) in
               (@) [Fmt.String "all {";
                   P.formatDec (G, D');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec D'))), F))
      | (Psi, All ((D, T.Implicit), F)) ->
          (match D with
           | UDec (D) ->
               let G = T.coerceCtx Psi in
               let D' = Names.decName (G, D) in
               (@) [Fmt.String "all^ {";
                   P.formatDec (G, D');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec D'))), F))
      | (Psi, Ex ((D, T.Explicit), F)) ->
          let G = T.coerceCtx Psi in
          let D' = Names.decName (G, D) in
          (@) [Fmt.String "exists {";
              P.formatDec (G, D');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec D'))), F)
      | (Psi, Ex ((D, T.Implicit), F)) ->
          let G = T.coerceCtx Psi in
          let D' = Names.decName (G, D) in
          (@) [Fmt.String "exists^ {";
              P.formatDec (G, D');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec D'))), F)
      | (Psi, And (F1, F2)) ->
          [Fmt.String "(";
          Fmt.HVbox (formatFor' (Psi, F1));
          Fmt.String ")";
          Fmt.Break;
          Fmt.String "/\\";
          Fmt.Space;
          Fmt.String "(";
          Fmt.HVbox (formatFor' (Psi, F2));
          Fmt.String ")"]
      | (Psi, T.True) -> [Fmt.String "true"]
      | (Psi, World (Worlds (L), F)) ->
          (@) [Fmt.String "world (";
              Fmt.HVbox (formatWorld L);
              Fmt.String ")";
              Fmt.Break]
            formatFor' (Psi, F)
    let rec formatFor (G, F) =
      Fmt.HVbox (formatFor' (G, (T.forSub (F, T.id))))
    let rec forToString (Psi, F) = Fmt.makestring_fmt (formatFor (Psi, F))
    let rec decName =
      function
      | (G, UDec (D)) -> T.UDec (Names.decName (G, D))
      | (G, PDec (NONE, F, TC1, TC2)) -> T.PDec ((SOME "xx"), F, TC1, TC2)
      | (G, D) -> D
    let rec psiName (Psi1, s, Psi2, l) =
      let rec nameDec =
        function
        | ((Dec (SOME _, _) as D), name) -> D
        | (Dec (NONE, V), name) -> I.Dec ((SOME name), V) in
      let rec namePsi =
        function
        | (Decl (Psi, UDec (D)), 1, name) ->
            I.Decl (Psi, (T.UDec (nameDec (D, name))))
        | (Decl (Psi, (UDec (D) as LD)), n, name) ->
            I.Decl ((namePsi (Psi, (n - 1), name)), LD)
      and nameG =
        function
        | (Psi, I.Null, n, name, k) -> ((k n), I.Null)
        | (Psi, Decl (G, D), 1, name, k) ->
            (Psi, (I.Decl (G, (nameDec (D, name)))))
        | (Psi, Decl (G, D), n, name, k) ->
            let (Psi', G') = nameG (Psi, G, (n - 1), name, k) in
            (Psi', (I.Decl (G', D))) in
      let rec ignore =
        function
        | (s, 0) -> s
        | (Dot (_, s), k) -> ignore (s, (k - 1))
        | (Shift n, k) ->
            ignore ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), (k - 1)) in
      let rec copyNames arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ((Shift n, (Decl _ as G)), Psi1) ->
            copyNames ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), G) Psi1
        | ((Dot (Exp _, s), Decl (G, _)), Psi1) -> copyNames (s, G) Psi1
        | ((Dot (Idx k, s), Decl (G, UDec (Dec (NONE, _)))), Psi1) ->
            copyNames (s, G) Psi1
        | ((Dot (Idx k, s), Decl (G, UDec (Dec (SOME name, _)))), Psi1) ->
            let Psi1' = namePsi (Psi1, k, name) in copyNames (s, G) Psi1'
        | ((Dot (Prg k, s), Decl (G, PDec (NONE, _, _, _))), Psi1) ->
            copyNames (s, G) Psi1
        | ((Dot (Prg k, s), Decl (G, PDec (SOME name, _, _, _))), Psi1) ->
            copyNames (s, G) Psi1
        | ((Shift _, I.Null), Psi1) -> Psi1 in
      let rec psiName' =
        function
        | I.Null -> I.Null
        | Decl (Psi, D) ->
            let Psi' = psiName' Psi in
            I.Decl (Psi', (decName ((T.coerceCtx Psi'), D))) in
      psiName' Psi1
    let rec fmtSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, T.Nil)) -> []
      | (callname, (Psi, AppExp (U, S))) ->
          (::) (Fmt.HVbox
                  (Print.formatSpine ((T.coerceCtx Psi), (I.App (U, I.Nil)))))
            fmtSpine' callname (Psi, S)
      | (callname, (Psi, AppPrg (P, S))) ->
          (::) (formatPrg3 callname (Psi, P)) fmtSpine' callname (Psi, S)
    let rec fmtSpine' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, T.Nil)) -> []
      | (callname, (Psi, S)) -> (::) Fmt.Break fmtSpine callname (Psi, S)
    let rec argsToSpine =
      function
      | (s, 0, S) -> S
      | (Shift n, k, S) ->
          argsToSpine ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), k, S)
      | (Dot (Idx n, s), k, S) ->
          argsToSpine
            (s, (k - 1), (T.AppExp ((I.Root ((I.BVar n), I.Nil)), S)))
      | (Dot (Exp (U), s), k, S) ->
          argsToSpine (s, (k - 1), (T.AppExp (U, S)))
      | (Dot (Prg (P), s), k, S) ->
          argsToSpine (s, (k - 1), (T.AppPrg (P, S)))
    let rec formatTuple (Psi, P) =
      let rec formatTuple' =
        function
        | T.Unit -> nil
        | PairExp (M, T.Unit) -> [Print.formatExp ((T.coerceCtx Psi), M)]
        | PairExp (M, P') ->
            (::) (((::) (Print.formatExp ((T.coerceCtx Psi), M)) Fmt.String
                     ",")
                    :: Fmt.Break)
              formatTuple' P' in
      match P with
      | PairExp (_, T.Unit) -> Fmt.Hbox (formatTuple' P)
      | _ ->
          Fmt.HVbox0 1 1 1
            ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"]))
    let rec formatRedex arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, Var k, S)) ->
          let PDec (SOME name, _, _, _) = I.ctxLookup (Psi, k) in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.Hbox
            [Fmt.Space;
            Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, (Psi, Const l, S)) ->
          let ValDec (name, _, _) = T.lemmaLookup l in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.Hbox
            [Fmt.Space;
            Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, (Psi, Redex (Const l, _), S)) ->
          let name = callname l in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.Hbox
            [Fmt.Space;
            Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
    let rec formatCase callname (max, Psi', s, Psi) =
      let S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', S) in Fmt.Hbox [Fmt.HVbox Fspine]
    let rec formatCases =
      function
      | (max, Psi, nil, callname) -> nil
      | (max, Psi, (Psi', s, P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          [Fmt.HVbox0 1 5 1
             [formatCase callname (max, Psi'', s, Psi);
             Fmt.Space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', P)];
          Fmt.Break]
      | (max, Psi, (Psi', s, P)::O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          (formatCases (max, Psi, O, callname)) @
            [Fmt.HVbox0 1 5 1
               [Fmt.String "|";
               Fmt.Space;
               formatCase callname (max, Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', P)];
            Fmt.Break]
    let rec formatPrg3 arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, T.Unit)) -> Fmt.String "<>"
      | (callname, (Psi, PairExp (U, P))) ->
          Fmt.HVbox
            [Fmt.String "<";
            Print.formatExp ((T.coerceCtx Psi), U);
            Fmt.String ",";
            Fmt.Break;
            formatPrg3 callname (Psi, P);
            Fmt.String ">"]
      | (callname, (Psi, (Let _ as P))) -> formatLet callname (Psi, P, nil)
      | (callname, (Psi, (LetPairExp (D1, D2, P1, P2) as P))) ->
          formatLet callname (Psi, P, nil)
      | (callname, (Psi, (LetUnit (P1, P2) as P))) ->
          formatLet callname (Psi, P, nil)
      | (callname, (Psi, (New (Lam (UDec (BDec (l, (c, s))), _)) as P))) ->
          formatNew callname (Psi, P, nil)
      | (callname, (Psi, Redex (P, S))) -> formatRedex callname (Psi, P, S)
      | (callname, (Psi, Lam ((UDec (D') as D), P))) ->
          Fmt.HVbox
            [Fmt.String "lam";
            Fmt.Space;
            Fmt.String "(";
            Print.formatDec ((T.coerceCtx Psi), D');
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, D)), P)]
      | (callname, (Psi, Rec ((PDec (SOME name, F, NONE, NONE) as D), P))) ->
          Fmt.HVbox
            [Fmt.String "fix*";
            Fmt.Space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, F);
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, D)), P)]
      | (callname,
         (Psi, Rec ((PDec (SOME name, F, SOME (TC1), SOME (TC2)) as D), P)))
          ->
          Fmt.HVbox
            [Fmt.String "fix";
            Fmt.Space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, F);
            Fmt.String ")";
            Fmt.Space;
            formatPrg3 callname ((I.Decl (Psi, D)), P)]
      | (callname, (Psi, PClo (P, t))) ->
          Fmt.HVbox [formatPrg3 callname (Psi, P); Fmt.String "..."]
      | (callname, (Psi, (EVar (_, ref (SOME (P)), _, _, _, _) as X))) ->
          formatPrg3 callname (Psi, P)
      | (callname, (Psi, (EVar (_, ref (NONE), _, _, _, _) as X))) ->
          Fmt.String (nameEVar X)
      | (callname, (Psi, Case (Cases (Cs)))) ->
          Fmt.HVbox
            (((::) ((Fmt.String "case") :: Fmt.Break) formatCases
                (1, Psi, Cs, callname))
               @ [Fmt.String "."])
      | (callname, (Psi, Var n)) ->
          let PDec (SOME n, _, _, _) = I.ctxLookup (Psi, n) in Fmt.String n
      | (callname, _) -> Fmt.String "missing case"
    let rec formatNew arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, New (Lam (UDec (BDec (l, (c, s)) as D), P)), fmts))
          ->
          let G = T.coerceCtx Psi in
          let D' = Names.decName (G, D) in
          formatNew callname
            ((I.Decl (Psi, (T.UDec D'))), P,
              (((::) Fmt.Break Fmt.HVbox [Print.formatDec (G, D')]) :: fmts))
      | (callname, (Psi, P, fmts)) ->
          Fmt.Vbox0 0 1
            [Fmt.String "new";
            Fmt.Vbox0 0 1 fmts;
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname (Psi, P);
            Fmt.Break;
            Fmt.String "end"]
    let rec formatLet arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname,
         (Psi, Let (D, P1, Case (Cases ((Psi1, s1, (Let _ as P2))::nil))),
          fmts)) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in
          let S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, S) in
          let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
          let Fbody = Fmt.HVbox [F1] in
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
          formatLet callname (Psi1', P2, (fmts @ [Fmt.Break; fmt]))
      | (callname,
         (Psi, Let (D, P1, Case (Cases ((Psi1, s1, P2)::nil))), fmts)) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in
          let S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, S) in
          let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
          let Fbody = Fmt.HVbox [F1] in
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
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Vbox0 2 1 (fmts @ [Fmt.Break; fmt]);
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname (Psi1', P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, (Psi, Let (D, P1, Case (Cases (L))), nil)) ->
          let rec fmtCaseRest =
            function
            | [] -> []
            | (Psi1, s1, P2)::L ->
                let Psi1' = psiName (Psi1, s1, Psi, 1) in
                let S = argsToSpine (s1, 1, T.Nil) in
                let Fspine = fmtSpine callname (Psi1, S) in
                let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
                (@) [Fmt.HVbox
                       [Fmt.Space;
                       Fmt.String "|";
                       Fmt.Space;
                       Fpattern;
                       Fmt.Space;
                       Fmt.String "-->"];
                    Fmt.Spaces 2;
                    Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)];
                    Fmt.Break]
                  fmtCaseRest L in
          let rec fmtCase ((Psi1, s1, P2)::L) =
            let Psi1' = psiName (Psi1, s1, Psi, 1) in
            let S = argsToSpine (s1, 1, T.Nil) in
            let Fspine = fmtSpine callname (Psi1, S) in
            let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
            Fmt.Vbox0 0 1
              ((@) [Fmt.HVbox
                      [Fmt.String "of";
                      Fmt.Space;
                      Fpattern;
                      Fmt.Space;
                      Fmt.String "-->"];
                   Fmt.Spaces 2;
                   Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)];
                   Fmt.Break]
                 fmtCaseRest L) in
          let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in
          let Fbody = Fmt.HVbox [F1] in
          let fmt = fmtCase L in
          Fmt.Vbox0 0 1
            [Fmt.String "case (";
            Fbody;
            Fmt.Space;
            Fmt.String ")";
            Fmt.Break;
            fmt]
      | (callname, (Psi, (Let (D, P1, Case (Cases (L))) as R), fmts)) ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Vbox0 0 1 (fmts @ [Fmt.Break]);
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatLet callname (Psi, R, nil);
            Fmt.Break;
            Fmt.String "end"]
      | (callname,
         (Psi, (Let ((PDec (SOME name, F, _, _) as D), P1, P2) as R), fmts))
          ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.Vbox0 0 1
              [Fmt.String name;
              Fmt.Space;
              Fmt.String "=";
              formatPrg3 callname (Psi, P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname ((I.Decl (Psi, D)), P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname,
         (Psi,
          (LetPairExp
             ((Dec (SOME n1, _) as D1), (PDec (SOME n2, F, _, _) as D2), P1,
              P2)
             as R),
          fmts)) ->
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
              formatPrg3 callname (Psi, P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname
              ((I.Decl ((I.Decl (Psi, (T.UDec D1))), D2)), P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, (Psi, (LetUnit (P1, P2) as R), fmts)) ->
          Fmt.Vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.Spaces 2;
            Fmt.Vbox0 0 1
              [Fmt.String "()";
              Fmt.Space;
              Fmt.String "=";
              Fmt.Space;
              formatPrg3 callname (Psi, P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.Spaces 2;
            formatPrg3 callname (Psi, P2);
            Fmt.Break;
            Fmt.String "end"]
    let rec formatHead callname (name, (max, index), Psi', s, Psi) =
      let S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', S) in
      Fmt.Hbox
        [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
    let rec formatPrg2 =
      function
      | (name, (max, index), Psi, nil, callname) -> nil
      | (name, (max, index), Psi, (Psi', s, P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let fhead = if (=) index I.ctxLength Psi then "fun" else "and" in
          [Fmt.HVbox0 1 5 1
             [Fmt.String fhead;
             formatHead callname (name, (max, index), Psi'', s, Psi);
             Fmt.Space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', P)];
          Fmt.Break]
      | (name, (max, index), Psi, (Psi', s, P)::O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          (formatPrg2 (name, (max, index), Psi, O, callname)) @
            [Fmt.HVbox0 1 5 1
               [Fmt.String "  |";
               formatHead callname (name, (max, index), Psi'', s, Psi);
               Fmt.Space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', P)];
            Fmt.Break]
    let rec formatPrg11 =
      function
      | (name, (max, index), Psi, Lam (D, P), callname) ->
          formatPrg11
            (name, (max, (index + 1)),
              (I.Decl (Psi, (decName ((T.coerceCtx Psi), D)))), P, callname)
      | (name, (max, index), Psi, Case (Cases (Os)), callname) ->
          formatPrg2 (name, (max, index), Psi, Os, callname)
    let rec formatPrg1 =
      function
      | (name::names, (max, index), Psi, PairPrg (P1, P2), callname) ->
          (@) (formatPrg11 (name, (max, index), Psi, P1, callname))
            formatPrg1 (names, (max, (index - 1)), Psi, P2, callname)
      | (name::[], (max, index), Psi, P, callname) ->
          formatPrg11 (name, (max, index), Psi, P, callname)
    let rec lookup (name::names, proj::projs) lemma =
      if lemma = proj then name else lookup (names, projs) lemma
    let rec formatPrg0
      ((names, projs), Rec ((PDec (SOME _, F, _, _) as D), P)) =
      let max = 1 in
      Fmt.Vbox0 0 1
        (formatPrg1
           (names, (max, max), (I.Decl (I.Null, D)), P,
             (function | lemma -> lookup (names, projs) lemma)))
    let rec formatFun (Args) = Names.varReset I.Null; formatPrg0 Args
    let rec funToString (Args) = Fmt.makestring_fmt (formatFun Args)
    let rec prgToString (Args) =
      Fmt.makestring_fmt (formatPrg3 (function | _ -> "?") Args)
    let rec nameCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, UDec (D)) ->
          I.Decl
            ((nameCtx Psi), (T.UDec (Names.decName ((T.coerceCtx Psi), D))))
      | Decl (Psi, PDec (NONE, F, TC1, TC2)) ->
          let Psi' = nameCtx Psi in
          let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec NONE)) in
          I.Decl (Psi', (T.PDec (x, F, TC1, TC2)))
      | Decl (Psi, (PDec (SOME n, F, _, _) as D)) ->
          I.Decl ((nameCtx Psi), D)
    let rec flag = function | NONE -> "" | SOME _ -> "*"
    let rec formatCtx =
      function
      | I.Null -> []
      | Decl (I.Null, UDec (D)) ->
          if (!Global.chatter) >= 4
          then [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, D)]]
          else [Print.formatDec (I.Null, D)]
      | Decl (I.Null, PDec (SOME s, F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.Space;
               Fmt.String ((^) "::" flag TC1);
               Fmt.Space;
               formatFor (I.Null, F)]]
          else
            [Fmt.String s;
            Fmt.Space;
            Fmt.String ((^) "::" flag TC1);
            Fmt.Space;
            formatFor (I.Null, F)]
      | Decl (Psi, UDec (D)) ->
          let G = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox [Fmt.Break; Print.formatDec (G, D)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (G, D)]
      | Decl (Psi, PDec (SOME s, F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String ((^) "::" flag TC1);
                 Fmt.Space;
                 formatFor (Psi, F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.Space;
              Fmt.String ((^) "::" flag TC1);
              Fmt.Space;
              formatFor (Psi, F)]
    let rec ctxToString (Psi) =
      Fmt.makestring_fmt (Fmt.HVbox (formatCtx Psi))
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
    (* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
    (*      fun nameLookup index = List.nth (names, index) *)
    (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
    (* needs to be integrated with Names *)
    (*       numberOfSplits Ds = n'

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
    (* copyNames  (ignore (s, l),  Psi2) *)
    (*

         merge (G1, G2) = G'

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
    (* fmtSpine callname (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
    (* Print.formatExp (T.coerceCtx Psi, U) *)
    (*
         frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
    (* this is a patch -cs
                                                            works only with one exists quantifier
                                                            we cannot use LF spines, we need to
                                                            use tomega spines.

                                                            Next step program printer for tomega spines
                                                            Then change this code. *)
    (* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
    (* Idx will always be expanded into Expressions and never into programs
                 is this a problem? -- cs *)
    (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
    (* no mutual recursion, recursive call *)
    (* lemma application *)
    (* mutual recursion, k is the projection function *)
    (* val T.ValDec (name, _, _) = T.lemmaLookup l *)
    (* formatCases ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
    (* formatPrg3 callname  (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
    (* formatTuple (Psi, P) *)
    (* formatTuple (Psi, P) *)
    (* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *)
    (* formatLet callname (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
    (* was I.ctxLength Psi - max  --cs *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
    (* was I.ctxLength Psi - max  --cs *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
    (*            val fmt =  formatDecs (0, Psi, Ds, (Psi1', s1)) *)
    (* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)
    (* need space since there is one before Fbody *)
    (* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
    (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *)
    (* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
    (* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
    (* formatPrg0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
    (*      fun formatPrg0 (T.Rec (T.PDec (SOME _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi    number of ih. *)
    (* number of ih. *)
    (*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPrg (I.Null, P) names]
*)
    (*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *)
    (*    fun prgToString Args names = "not yet implemented " *)
    (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
    let formatFor = formatFor
    let forToString = forToString
    let formatFun = formatFun
    let formatPrg = formatPrg3 (function | _ -> "?")
    (*    val formatLemmaDec = formatLemmaDec *)
    let evarName = evarName
    let evarReset = evarReset
    let nameEVar = nameEVar
    let prgToString = prgToString
    let funToString = funToString
    let nameCtx = nameCtx
    let formatCtx = function | Psi -> Fmt.HVbox (formatCtx Psi)
    let ctxToString = ctxToString
  end ;;
