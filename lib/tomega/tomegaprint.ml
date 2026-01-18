
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
        | (EVar (_, _, _, _, _, (EVar (_, __g, r, _) as x)) as y)::__l ->
            if (Names.evarName (__g, x)) = n then y else evarName' __l in
      evarName' (!evarList)
    let rec nameEVar (EVar (_, _, _, _, _, (EVar (_, __g, r, _) as x))) =
      Names.evarName (__g, x)
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
      | (Psi, All ((__d, T.Explicit), F)) ->
          (match __d with
           | UDec (__d) ->
               let __g = T.coerceCtx Psi in
               let __d' = Names.decName (__g, __d) in
               (@) [Fmt.String "all {";
                   P.formatDec (__g, __d');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec __d'))), F))
      | (Psi, All ((__d, T.Implicit), F)) ->
          (match __d with
           | UDec (__d) ->
               let __g = T.coerceCtx Psi in
               let __d' = Names.decName (__g, __d) in
               (@) [Fmt.String "all^ {";
                   P.formatDec (__g, __d');
                   Fmt.String "}";
                   Fmt.Break]
                 formatFor' ((I.Decl (Psi, (T.UDec __d'))), F))
      | (Psi, Ex ((__d, T.Explicit), F)) ->
          let __g = T.coerceCtx Psi in
          let __d' = Names.decName (__g, __d) in
          (@) [Fmt.String "exists {";
              P.formatDec (__g, __d');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec __d'))), F)
      | (Psi, Ex ((__d, T.Implicit), F)) ->
          let __g = T.coerceCtx Psi in
          let __d' = Names.decName (__g, __d) in
          (@) [Fmt.String "exists^ {";
              P.formatDec (__g, __d');
              Fmt.String "}";
              Fmt.Break]
            formatFor' ((I.Decl (Psi, (T.UDec __d'))), F)
      | (Psi, And (__F1, __F2)) ->
          [Fmt.String "(";
          Fmt.hVbox (formatFor' (Psi, __F1));
          Fmt.String ")";
          Fmt.Break;
          Fmt.String "/\\";
          Fmt.space;
          Fmt.String "(";
          Fmt.hVbox (formatFor' (Psi, __F2));
          Fmt.String ")"]
      | (Psi, T.True) -> [Fmt.String "true"]
      | (Psi, World (Worlds (__l), F)) ->
          (@) [Fmt.String "world (";
              Fmt.hVbox (formatWorld __l);
              Fmt.String ")";
              Fmt.Break]
            formatFor' (Psi, F)
    let rec formatFor (__g, F) =
      Fmt.hVbox (formatFor' (__g, (T.forSub (F, T.id))))
    let rec forToString (Psi, F) = Fmt.makestring_fmt (formatFor (Psi, F))
    let rec decName =
      function
      | (__g, UDec (__d)) -> T.UDec (Names.decName (__g, __d))
      | (__g, PDec (None, F, TC1, TC2)) -> T.PDec ((Some "xx"), F, TC1, TC2)
      | (__g, __d) -> __d
    let rec psiName (Psi1, s, Psi2, l) =
      let rec nameDec =
        function
        | ((Dec (Some _, _) as __d), name) -> __d
        | (Dec (None, __v), name) -> I.Dec ((Some name), __v) in
      let rec namePsi =
        function
        | (Decl (Psi, UDec (__d)), 1, name) ->
            I.Decl (Psi, (T.UDec (nameDec (__d, name))))
        | (Decl (Psi, (UDec (__d) as LD)), n, name) ->
            I.Decl ((namePsi (Psi, (n - 1), name)), LD)
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
            ignore ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), (k - 1)) in
      let rec copyNames arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ((Shift n, (Decl _ as __g)), Psi1) ->
            copyNames ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), __g) Psi1
        | ((Dot (Exp _, s), Decl (__g, _)), Psi1) -> copyNames (s, __g) Psi1
        | ((Dot (Idx k, s), Decl (__g, UDec (Dec (None, _)))), Psi1) ->
            copyNames (s, __g) Psi1
        | ((Dot (Idx k, s), Decl (__g, UDec (Dec (Some name, _)))), Psi1) ->
            let Psi1' = namePsi (Psi1, k, name) in copyNames (s, __g) Psi1'
        | ((Dot (Prg k, s), Decl (__g, PDec (None, _, _, _))), Psi1) ->
            copyNames (s, __g) Psi1
        | ((Dot (Prg k, s), Decl (__g, PDec (Some name, _, _, _))), Psi1) ->
            copyNames (s, __g) Psi1
        | ((Shift _, I.Null), Psi1) -> Psi1 in
      let rec psiName' =
        function
        | I.Null -> I.Null
        | Decl (Psi, __d) ->
            let Psi' = psiName' Psi in
            I.Decl (Psi', (decName ((T.coerceCtx Psi'), __d))) in
      psiName' Psi1
    let rec fmtSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, T.Nil)) -> []
      | (callname, (Psi, AppExp (__u, S))) ->
          (::) (Fmt.hVbox
                  (Print.formatSpine ((T.coerceCtx Psi), (I.App (__u, I.Nil)))))
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
      | (Dot (Exp (__u), s), k, S) ->
          argsToSpine (s, (k - 1), (T.AppExp (__u, S)))
      | (Dot (Prg (P), s), k, S) ->
          argsToSpine (s, (k - 1), (T.AppPrg (P, S)))
    let rec formatTuple (Psi, P) =
      let rec formatTuple' =
        function
        | T.Unit -> nil
        | PairExp (M, T.Unit) -> [Print.formatExp ((T.coerceCtx Psi), M)]
        | PairExp (M, __P') ->
            (::) (((::) (Print.formatExp ((T.coerceCtx Psi), M)) Fmt.String
                     ",")
                    :: Fmt.Break)
              formatTuple' __P' in
      match P with
      | PairExp (_, T.Unit) -> Fmt.hbox (formatTuple' P)
      | _ ->
          Fmt.hVbox0 1 1 1
            ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"]))
    let rec formatRedex arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, Var k, S)) ->
          let PDec (Some name, _, _, _) = I.ctxLookup (Psi, k) in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.hbox
            [Fmt.space;
            Fmt.hVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, (Psi, Const l, S)) ->
          let ValDec (name, _, _) = T.lemmaLookup l in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.hbox
            [Fmt.space;
            Fmt.hVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
      | (callname, (Psi, Redex (Const l, _), S)) ->
          let name = callname l in
          let Fspine = fmtSpine callname (Psi, S) in
          Fmt.hbox
            [Fmt.space;
            Fmt.hVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
    let rec formatCase callname (max, Psi', s, Psi) =
      let S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', S) in Fmt.hbox [Fmt.hVbox Fspine]
    let rec formatCases =
      function
      | (max, Psi, nil, callname) -> nil
      | (max, Psi, (Psi', s, P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          [Fmt.hVbox0 1 5 1
             [formatCase callname (max, Psi'', s, Psi);
             Fmt.space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', P)];
          Fmt.Break]
      | (max, Psi, (Psi', s, P)::O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let _ = Names.varReset I.Null in
          (formatCases (max, Psi, O, callname)) @
            [Fmt.hVbox0 1 5 1
               [Fmt.String "|";
               Fmt.space;
               formatCase callname (max, Psi'', s, Psi);
               Fmt.space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', P)];
            Fmt.Break]
    let rec formatPrg3 arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, T.Unit)) -> Fmt.String "<>"
      | (callname, (Psi, PairExp (__u, P))) ->
          Fmt.hVbox
            [Fmt.String "<";
            Print.formatExp ((T.coerceCtx Psi), __u);
            Fmt.String ",";
            Fmt.Break;
            formatPrg3 callname (Psi, P);
            Fmt.String ">"]
      | (callname, (Psi, (Let _ as P))) -> formatLet callname (Psi, P, nil)
      | (callname, (Psi, (LetPairExp (D1, D2, __P1, __P2) as P))) ->
          formatLet callname (Psi, P, nil)
      | (callname, (Psi, (LetUnit (__P1, __P2) as P))) ->
          formatLet callname (Psi, P, nil)
      | (callname, (Psi, (New (Lam (UDec (BDec (l, (c, s))), _)) as P))) ->
          formatNew callname (Psi, P, nil)
      | (callname, (Psi, Redex (P, S))) -> formatRedex callname (Psi, P, S)
      | (callname, (Psi, Lam ((UDec (__d') as __d), P))) ->
          Fmt.hVbox
            [Fmt.String "lam";
            Fmt.space;
            Fmt.String "(";
            Print.formatDec ((T.coerceCtx Psi), __d');
            Fmt.String ")";
            Fmt.space;
            formatPrg3 callname ((I.Decl (Psi, __d)), P)]
      | (callname, (Psi, Rec ((PDec (Some name, F, None, None) as __d), P))) ->
          Fmt.hVbox
            [Fmt.String "fix*";
            Fmt.space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, F);
            Fmt.String ")";
            Fmt.space;
            formatPrg3 callname ((I.Decl (Psi, __d)), P)]
      | (callname,
         (Psi, Rec ((PDec (Some name, F, Some (TC1), Some (TC2)) as __d), P)))
          ->
          Fmt.hVbox
            [Fmt.String "fix";
            Fmt.space;
            Fmt.String "(";
            Fmt.String name;
            Fmt.String ":";
            formatFor (Psi, F);
            Fmt.String ")";
            Fmt.space;
            formatPrg3 callname ((I.Decl (Psi, __d)), P)]
      | (callname, (Psi, PClo (P, t))) ->
          Fmt.hVbox [formatPrg3 callname (Psi, P); Fmt.String "..."]
      | (callname, (Psi, (EVar (_, ref (Some (P)), _, _, _, _) as x))) ->
          formatPrg3 callname (Psi, P)
      | (callname, (Psi, (EVar (_, ref (None), _, _, _, _) as x))) ->
          Fmt.String (nameEVar x)
      | (callname, (Psi, Case (Cases (__Cs)))) ->
          Fmt.hVbox
            (((::) ((Fmt.String "case") :: Fmt.Break) formatCases
                (1, Psi, __Cs, callname))
               @ [Fmt.String "."])
      | (callname, (Psi, Var n)) ->
          let PDec (Some n, _, _, _) = I.ctxLookup (Psi, n) in Fmt.String n
      | (callname, _) -> Fmt.String "missing case"
    let rec formatNew arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname, (Psi, New (Lam (UDec (BDec (l, (c, s)) as __d), P)), fmts))
          ->
          let __g = T.coerceCtx Psi in
          let __d' = Names.decName (__g, __d) in
          formatNew callname
            ((I.Decl (Psi, (T.UDec __d'))), P,
              (((::) Fmt.Break Fmt.hVbox [Print.formatDec (__g, __d')]) :: fmts))
      | (callname, (Psi, P, fmts)) ->
          Fmt.Vbox0 0 1
            [Fmt.String "new";
            Fmt.vbox0 0 1 fmts;
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatPrg3 callname (Psi, P);
            Fmt.Break;
            Fmt.String "end"]
    let rec formatLet arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (callname,
         (Psi, Let (__d, __P1, Case (Cases ((Psi1, s1, (Let _ as __P2))::nil))),
          fmts)) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let __F1 = Fmt.hVbox [formatPrg3 callname (Psi, __P1)] in
          let S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, S) in
          let Fpattern = Fmt.hVbox [Fmt.hbox Fspine] in
          let Fbody = Fmt.hVbox [__F1] in
          let fmt =
            Fmt.hVbox
              [Fmt.hVbox
                 [Fmt.String "val";
                 Fmt.space;
                 Fpattern;
                 Fmt.space;
                 Fmt.String "="];
              Fmt.Break;
              Fbody] in
          formatLet callname (Psi1', __P2, (fmts @ [Fmt.Break; fmt]))
      | (callname,
         (Psi, Let (__d, __P1, Case (Cases ((Psi1, s1, __P2)::nil))), fmts)) ->
          let Psi1' = psiName (Psi1, s1, Psi, 1) in
          let __F1 = Fmt.hVbox [formatPrg3 callname (Psi, __P1)] in
          let S = argsToSpine (s1, 1, T.Nil) in
          let Fspine = fmtSpine callname (Psi1, S) in
          let Fpattern = Fmt.hVbox [Fmt.hbox Fspine] in
          let Fbody = Fmt.hVbox [__F1] in
          let fmt =
            Fmt.hVbox
              [Fmt.hVbox
                 [Fmt.String "val";
                 Fmt.space;
                 Fpattern;
                 Fmt.space;
                 Fmt.String "="];
              Fmt.Break;
              Fbody] in
          Fmt.vbox0 0 1
            [Fmt.String "let";
            Fmt.vbox0 2 1 (fmts @ [Fmt.Break; fmt]);
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatPrg3 callname (Psi1', __P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, (Psi, Let (__d, __P1, Case (Cases (__l))), nil)) ->
          let rec fmtCaseRest =
            function
            | [] -> []
            | (Psi1, s1, __P2)::__l ->
                let Psi1' = psiName (Psi1, s1, Psi, 1) in
                let S = argsToSpine (s1, 1, T.Nil) in
                let Fspine = fmtSpine callname (Psi1, S) in
                let Fpattern = Fmt.hVbox [Fmt.hbox Fspine] in
                (@) [Fmt.hVbox
                       [Fmt.space;
                       Fmt.String "|";
                       Fmt.space;
                       Fpattern;
                       Fmt.space;
                       Fmt.String "-->"];
                    Fmt.spaces 2;
                    Fmt.vbox0 0 1 [formatPrg3 callname (Psi1', __P2)];
                    Fmt.Break]
                  fmtCaseRest __l in
          let rec fmtCase ((Psi1, s1, __P2)::__l) =
            let Psi1' = psiName (Psi1, s1, Psi, 1) in
            let S = argsToSpine (s1, 1, T.Nil) in
            let Fspine = fmtSpine callname (Psi1, S) in
            let Fpattern = Fmt.hVbox [Fmt.hbox Fspine] in
            Fmt.vbox0 0 1
              ((@) [Fmt.hVbox
                      [Fmt.String "of";
                      Fmt.space;
                      Fpattern;
                      Fmt.space;
                      Fmt.String "-->"];
                   Fmt.spaces 2;
                   Fmt.vbox0 0 1 [formatPrg3 callname (Psi1', __P2)];
                   Fmt.Break]
                 fmtCaseRest __l) in
          let __F1 = Fmt.hVbox [formatPrg3 callname (Psi, __P1)] in
          let Fbody = Fmt.hVbox [__F1] in
          let fmt = fmtCase __l in
          Fmt.vbox0 0 1
            [Fmt.String "case (";
            Fbody;
            Fmt.space;
            Fmt.String ")";
            Fmt.Break;
            fmt]
      | (callname, (Psi, (Let (__d, __P1, Case (Cases (__l))) as R), fmts)) ->
          Fmt.vbox0 0 1
            [Fmt.String "let";
            Fmt.vbox0 0 1 (fmts @ [Fmt.Break]);
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatLet callname (Psi, R, nil);
            Fmt.Break;
            Fmt.String "end"]
      | (callname,
         (Psi, (Let ((PDec (Some name, F, _, _) as __d), __P1, __P2) as R), fmts))
          ->
          Fmt.vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.vbox0 0 1
              [Fmt.String name;
              Fmt.space;
              Fmt.String "=";
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatPrg3 callname ((I.Decl (Psi, __d)), __P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname,
         (Psi,
          (LetPairExp
             ((Dec (Some n1, _) as D1), (PDec (Some n2, F, _, _) as D2), __P1,
              __P2)
             as R),
          fmts)) ->
          Fmt.vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.spaces 2;
            Fmt.vbox0 0 1
              [Fmt.String "(";
              Fmt.String n1;
              Fmt.String ",";
              Fmt.space;
              Fmt.String n2;
              Fmt.String ")";
              Fmt.space;
              Fmt.String "=";
              Fmt.space;
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatPrg3 callname
              ((I.Decl ((I.Decl (Psi, (T.UDec D1))), D2)), __P2);
            Fmt.Break;
            Fmt.String "end"]
      | (callname, (Psi, (LetUnit (__P1, __P2) as R), fmts)) ->
          Fmt.vbox0 0 1
            [Fmt.String "let";
            Fmt.Break;
            Fmt.spaces 2;
            Fmt.vbox0 0 1
              [Fmt.String "()";
              Fmt.space;
              Fmt.String "=";
              Fmt.space;
              formatPrg3 callname (Psi, __P1)];
            Fmt.Break;
            Fmt.String "in";
            Fmt.Break;
            Fmt.spaces 2;
            formatPrg3 callname (Psi, __P2);
            Fmt.Break;
            Fmt.String "end"]
    let rec formatHead callname (name, (max, index), Psi', s, Psi) =
      let S = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
      let Fspine = fmtSpine callname (Psi', S) in
      Fmt.hbox
        [Fmt.space; Fmt.hVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
    let rec formatPrg2 =
      function
      | (name, (max, index), Psi, nil, callname) -> nil
      | (name, (max, index), Psi, (Psi', s, P)::nil, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          let fhead = if (=) index I.ctxLength Psi then "fun" else "and" in
          [Fmt.hVbox0 1 5 1
             [Fmt.String fhead;
             formatHead callname (name, (max, index), Psi'', s, Psi);
             Fmt.space;
             Fmt.String "=";
             Fmt.Break;
             formatPrg3 callname (Psi'', P)];
          Fmt.Break]
      | (name, (max, index), Psi, (Psi', s, P)::O, callname) ->
          let Psi'' = psiName (Psi', s, Psi, 0) in
          (formatPrg2 (name, (max, index), Psi, O, callname)) @
            [Fmt.hVbox0 1 5 1
               [Fmt.String "  |";
               formatHead callname (name, (max, index), Psi'', s, Psi);
               Fmt.space;
               Fmt.String "=";
               Fmt.Break;
               formatPrg3 callname (Psi'', P)];
            Fmt.Break]
    let rec formatPrg11 =
      function
      | (name, (max, index), Psi, Lam (__d, P), callname) ->
          formatPrg11
            (name, (max, (index + 1)),
              (I.Decl (Psi, (decName ((T.coerceCtx Psi), __d)))), P, callname)
      | (name, (max, index), Psi, Case (Cases (__Os)), callname) ->
          formatPrg2 (name, (max, index), Psi, __Os, callname)
    let rec formatPrg1 =
      function
      | (name::names, (max, index), Psi, PairPrg (__P1, __P2), callname) ->
          (@) (formatPrg11 (name, (max, index), Psi, __P1, callname))
            formatPrg1 (names, (max, (index - 1)), Psi, __P2, callname)
      | (name::[], (max, index), Psi, P, callname) ->
          formatPrg11 (name, (max, index), Psi, P, callname)
    let rec lookup (name::names, proj::projs) lemma =
      if lemma = proj then name else lookup (names, projs) lemma
    let rec formatPrg0
      ((names, projs), Rec ((PDec (Some _, F, _, _) as __d), P)) =
      let max = 1 in
      Fmt.vbox0 0 1
        (formatPrg1
           (names, (max, max), (I.Decl (I.Null, __d)), P,
             (function | lemma -> lookup (names, projs) lemma)))
    let rec formatFun (Args) = Names.varReset I.Null; formatPrg0 Args
    let rec funToString (Args) = Fmt.makestring_fmt (formatFun Args)
    let rec prgToString (Args) =
      Fmt.makestring_fmt (formatPrg3 (function | _ -> "?") Args)
    let rec nameCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, UDec (__d)) ->
          I.Decl
            ((nameCtx Psi), (T.UDec (Names.decName ((T.coerceCtx Psi), __d))))
      | Decl (Psi, PDec (None, F, TC1, TC2)) ->
          let Psi' = nameCtx Psi in
          let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec None)) in
          I.Decl (Psi', (T.PDec (x, F, TC1, TC2)))
      | Decl (Psi, (PDec (Some n, F, _, _) as __d)) ->
          I.Decl ((nameCtx Psi), __d)
    let rec flag = function | None -> "" | Some _ -> "*"
    let rec formatCtx =
      function
      | I.Null -> []
      | Decl (I.Null, UDec (__d)) ->
          if (!Global.chatter) >= 4
          then [Fmt.hVbox [Fmt.Break; Print.formatDec (I.Null, __d)]]
          else [Print.formatDec (I.Null, __d)]
      | Decl (I.Null, PDec (Some s, F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.hVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.space;
               Fmt.String ((^) "::" flag TC1);
               Fmt.space;
               formatFor (I.Null, F)]]
          else
            [Fmt.String s;
            Fmt.space;
            Fmt.String ((^) "::" flag TC1);
            Fmt.space;
            formatFor (I.Null, F)]
      | Decl (Psi, UDec (__d)) ->
          let __g = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.hVbox [Fmt.Break; Print.formatDec (__g, __d)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__g, __d)]
      | Decl (Psi, PDec (Some s, F, TC1, TC2)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.hVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.space;
                 Fmt.String ((^) "::" flag TC1);
                 Fmt.space;
                 formatFor (Psi, F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.space;
              Fmt.String ((^) "::" flag TC1);
              Fmt.space;
              formatFor (Psi, F)]
    let rec ctxToString (Psi) =
      Fmt.makestring_fmt (Fmt.hVbox (formatCtx Psi))
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
    (* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (__P1, __P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
    (*      fun nameLookup index = List.nth (names, index) *)
    (* decName (__g, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
    (* needs to be integrated with Names *)
    (*       numberOfSplits __Ds = n'

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
    (* copyNames  (ignore (s, l),  Psi2) *)
    (*

         merge (G1, G2) = __g'

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
    (* fmtSpine callname (__g, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context __g which approximates __g', where __g' |- S[s] is valid
  *)
    (* Print.formatExp (T.coerceCtx Psi, __u) *)
    (*
         frontToExp (Ft) = __u'

           Invariant:
           __g |- Ft = __u' : __v   for a __g, __v
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
    (* formatCases ((max, index), Psi, __l) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- __l a list of cases
           then fmts' list of pretty print formats of __l
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
           and  Psi; Delta |- P = Let . Case __P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for __P'
        *)
    (* was I.ctxLength Psi - max  --cs *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
    (* was I.ctxLength Psi - max  --cs *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
    (*            val fmt =  formatDecs (0, Psi, __Ds, (Psi1', s1)) *)
    (* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)
    (* need space since there is one before Fbody *)
    (* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
    (*            val T.PDec (Some name, _) = I.ctxLookup (Psi, index) *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *)
    (* formatPrg2 ((max, index), Psi, __l) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- __l a list of cases
           then fmts' list of pretty print formats of __l
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
    (*      fun formatPrg0 (T.Rec (T.PDec (Some _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi    number of ih. *)
    (* number of ih. *)
    (*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
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
    let formatCtx = function | Psi -> Fmt.hVbox (formatCtx Psi)
    let ctxToString = ctxToString
  end ;;
