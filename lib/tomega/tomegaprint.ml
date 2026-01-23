module type TOMEGAPRINT  =
  sig
    module Formatter : FORMATTER
    exception Error of string 
    val formatFor :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.for_) -> Formatter.format
    val forToString : (Tomega.dec_ IntSyn.ctx_ * Tomega.for_) -> string
    val formatFun :
      ((string list * Tomega.lemma list) * Tomega.prg_) -> Formatter.format
    val formatPrg :
      (Tomega.dec_ IntSyn.ctx_ * Tomega.prg_) -> Formatter.format
    val funToString :
      ((string list * Tomega.lemma list) * Tomega.prg_) -> string
    val evarReset : unit -> unit
    val evarName : string -> Tomega.prg_
    val nameEVar : Tomega.prg_ -> string
    val prgToString : (Tomega.dec_ IntSyn.ctx_ * Tomega.prg_) -> string
    val nameCtx : Tomega.dec_ IntSyn.ctx_ -> Tomega.dec_ IntSyn.ctx_
    val formatCtx : Tomega.dec_ IntSyn.ctx_ -> Formatter.format
    val ctxToString : Tomega.dec_ IntSyn.ctx_ -> string
  end


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
    let (evarList : T.prg_ list ref) = ref []
    let rec evarReset () = evarList := []
    let rec evarName n =
      let rec evarName' =
        begin function
        | [] -> raise (Error "not found")
        | (EVar (_, _, _, _, _, (EVar (_, g_, r, _) as x_)) as y_)::l_ ->
            if (Names.evarName (g_, x_)) = n then begin y_ end
            else begin evarName' l_ end end in
  evarName' !evarList
let rec nameEVar (EVar (_, _, _, _, _, (EVar (_, g_, r, _) as x_))) =
  Names.evarName (g_, x_)
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
let rec constName c = I.conDecName (I.sgnLookup c)
let rec formatWorld =
  begin function
  | [] -> []
  | c::[] -> [Fmt.String (constName c)]
  | c::cids ->
      (@) [Fmt.String (constName c); Fmt.String ","; Fmt.Break] formatWorld
        cids end
let rec formatFor' =
  begin function
  | (Psi, All ((d_, T.Explicit), f_)) ->
      (begin match d_ with
       | UDec (d_) ->
           let g_ = T.coerceCtx Psi in
           let d'_ = Names.decName (g_, d_) in
           (@) [Fmt.String "all {";
               P.formatDec (g_, d'_);
               Fmt.String "}";
               Fmt.Break]
             formatFor' ((I.Decl (Psi, (T.UDec d'_))), f_) end)
  | (Psi, All ((d_, T.Implicit), f_)) ->
      (begin match d_ with
       | UDec (d_) ->
           let g_ = T.coerceCtx Psi in
           let d'_ = Names.decName (g_, d_) in
           (@) [Fmt.String "all^ {";
               P.formatDec (g_, d'_);
               Fmt.String "}";
               Fmt.Break]
             formatFor' ((I.Decl (Psi, (T.UDec d'_))), f_) end)
  | (Psi, Ex ((d_, T.Explicit), f_)) ->
      let g_ = T.coerceCtx Psi in
      let d'_ = Names.decName (g_, d_) in
      (@) [Fmt.String "exists {";
          P.formatDec (g_, d'_);
          Fmt.String "}";
          Fmt.Break]
        formatFor' ((I.Decl (Psi, (T.UDec d'_))), f_)
  | (Psi, Ex ((d_, T.Implicit), f_)) ->
      let g_ = T.coerceCtx Psi in
      let d'_ = Names.decName (g_, d_) in
      (@) [Fmt.String "exists^ {";
          P.formatDec (g_, d'_);
          Fmt.String "}";
          Fmt.Break]
        formatFor' ((I.Decl (Psi, (T.UDec d'_))), f_)
  | (Psi, And (f1_, f2_)) ->
      [Fmt.String "(";
      Fmt.HVbox (formatFor' (Psi, f1_));
      Fmt.String ")";
      Fmt.Break;
      Fmt.String "/\\";
      Fmt.Space;
      Fmt.String "(";
      Fmt.HVbox (formatFor' (Psi, f2_));
      Fmt.String ")"]
  | (Psi, T.True) -> [Fmt.String "true"]
  | (Psi, World (Worlds (l_), f_)) ->
      (@) [Fmt.String "world (";
          Fmt.HVbox (formatWorld l_);
          Fmt.String ")";
          Fmt.Break]
        formatFor' (Psi, f_) end
let rec formatFor (g_, f_) =
  Fmt.HVbox (formatFor' (g_, (T.forSub (f_, T.id))))
let rec forToString (Psi, f_) = Fmt.makestring_fmt (formatFor (Psi, f_))
let rec decName =
  begin function
  | (g_, UDec (d_)) -> T.UDec (Names.decName (g_, d_))
  | (g_, PDec (None, f_, TC1, TC2)) -> T.PDec ((Some "xx"), f_, TC1, TC2)
  | (g_, d_) -> d_ end(* needs to be integrated with Names *)
let rec psiName (Psi1, s, Psi2, l) =
  let rec nameDec =
    begin function
    | ((Dec (Some _, _) as d_), name) -> d_
    | (Dec (None, v_), name) -> I.Dec ((Some name), v_) end in
let rec namePsi =
  begin function
  | (Decl (Psi, UDec (d_)), 1, name) ->
      I.Decl (Psi, (T.UDec (nameDec (d_, name))))
  | (Decl (Psi, (UDec (d_) as LD)), n, name) ->
      I.Decl ((namePsi (Psi, (n - 1), name)), LD) end
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
      ignore ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), (k - 1)) end in
let rec copyNames arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | ((Shift n, (Decl _ as g_)), Psi1) ->
      copyNames ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), g_) Psi1
  | ((Dot (Exp _, s), Decl (g_, _)), Psi1) -> copyNames (s, g_) Psi1
  | ((Dot (Idx k, s), Decl (g_, UDec (Dec (None, _)))), Psi1) ->
      copyNames (s, g_) Psi1
  | ((Dot (Idx k, s), Decl (g_, UDec (Dec (Some name, _)))), Psi1) ->
      let Psi1' = namePsi (Psi1, k, name) in copyNames (s, g_) Psi1'
  | ((Dot (Prg k, s), Decl (g_, PDec (None, _, _, _))), Psi1) ->
      copyNames (s, g_) Psi1
  | ((Dot (Prg k, s), Decl (g_, PDec (Some name, _, _, _))), Psi1) ->
      copyNames (s, g_) Psi1
  | ((Shift _, I.Null), Psi1) -> Psi1 end in
let rec psiName' =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, d_) ->
      let Psi' = psiName' Psi in
      I.Decl (Psi', (decName ((T.coerceCtx Psi'), d_))) end in
psiName' ((Psi1)(* copyNames  (ignore (s, l),  Psi2) *))
let rec fmtSpine arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (callname, (Psi, T.Nil)) -> []
  | (callname, (Psi, AppExp (u_, s_))) ->
      (::) (Fmt.HVbox
              (Print.formatSpine ((T.coerceCtx Psi), (I.App (u_, I.Nil)))))
        fmtSpine' callname (Psi, s_)
  | (callname, (Psi, AppPrg (p_, s_))) ->
      (::) (formatPrg3 callname (Psi, p_)) fmtSpine' callname (Psi, s_) end
(* Print.formatExp (T.coerceCtx Psi, U) *)
let rec fmtSpine' arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (callname, (Psi, T.Nil)) -> []
  | (callname, (Psi, s_)) -> (::) Fmt.Break fmtSpine callname (Psi, s_) end
let rec argsToSpine =
  begin function
  | (s, 0, s_) -> s_
  | (Shift n, k, s_) ->
      argsToSpine ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), k, s_)
  | (Dot (Idx n, s), k, s_) ->
      argsToSpine (s, (k - 1), (T.AppExp ((I.Root ((I.BVar n), I.Nil)), s_)))
  | (Dot (Exp (u_), s), k, s_) ->
      argsToSpine (s, (k - 1), (T.AppExp (u_, s_)))
  | (Dot (Prg (p_), s), k, s_) ->
      argsToSpine (s, (k - 1), (T.AppPrg (p_, s_))) end
let rec formatTuple (Psi, p_) =
  let rec formatTuple' =
    begin function
    | T.Unit -> []
    | PairExp (m_, T.Unit) -> [Print.formatExp ((T.coerceCtx Psi), m_)]
    | PairExp (m_, p'_) ->
        (::) (((::) (Print.formatExp ((T.coerceCtx Psi), m_)) Fmt.String ",")
                :: Fmt.Break)
          formatTuple' p'_ end in
begin match p_ with
| PairExp (_, T.Unit) -> Fmt.Hbox (formatTuple' p_)
| _ ->
    Fmt.HVbox0 1 1 1
      ((Fmt.String "(") :: ((formatTuple' p_) @ [Fmt.String ")"])) end
let rec formatRedex arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (callname, (Psi, Var k, s_)) ->
      let PDec (Some name, _, _, _) = I.ctxLookup (Psi, k) in
      let Fspine = fmtSpine callname (Psi, s_) in
      Fmt.Hbox
        [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
  | (callname, (Psi, Const l, s_)) ->
      let ValDec (name, _, _) = T.lemmaLookup l in
      let Fspine = fmtSpine callname (Psi, s_) in
      Fmt.Hbox
        [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)]
  | (callname, (Psi, Redex (Const l, _), s_)) ->
      let name = callname l in
      let Fspine = fmtSpine callname (Psi, s_) in
      ((Fmt.Hbox
          [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)])
        (* val T.ValDec (name, _, _) = T.lemmaLookup l *)) end
(* mutual recursion, k is the projection function *)
(* lemma application *)(* no mutual recursion, recursive call *)
let rec formatCase callname (max, Psi', s, Psi) =
  let s_ = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
  let Fspine = fmtSpine callname (Psi', s_) in Fmt.Hbox [Fmt.HVbox Fspine]
let rec formatCases =
  begin function
  | (max, Psi, [], callname) -> []
  | (max, Psi, (Psi', s, p_)::[], callname) ->
      let Psi'' = psiName (Psi', s, Psi, 0) in
      let _ = Names.varReset I.Null in
      [Fmt.HVbox0 1 5 1
         [formatCase callname (max, Psi'', s, Psi);
         Fmt.Space;
         Fmt.String "=";
         Fmt.Break;
         formatPrg3 callname (Psi'', p_)];
      Fmt.Break]
  | (max, Psi, (Psi', s, p_)::o_, callname) ->
      let Psi'' = psiName (Psi', s, Psi, 0) in
      let _ = Names.varReset I.Null in
      (formatCases (max, Psi, o_, callname)) @
        [Fmt.HVbox0 1 5 1
           [Fmt.String "|";
           Fmt.Space;
           formatCase callname (max, Psi'', s, Psi);
           Fmt.Space;
           Fmt.String "=";
           Fmt.Break;
           formatPrg3 callname (Psi'', p_)];
        Fmt.Break] end
let rec formatPrg3 arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (callname, (Psi, T.Unit)) -> Fmt.String "<>"
  | (callname, (Psi, PairExp (u_, p_))) ->
      Fmt.HVbox
        [Fmt.String "<";
        Print.formatExp ((T.coerceCtx Psi), u_);
        Fmt.String ",";
        Fmt.Break;
        formatPrg3 callname (Psi, p_);
        Fmt.String ">"]
  | (callname, (Psi, (Let _ as p_))) -> formatLet callname (Psi, p_, [])
  | (callname, (Psi, (LetPairExp (d1_, d2_, p1_, p2_) as p_))) ->
      formatLet callname (Psi, p_, [])
  | (callname, (Psi, (LetUnit (p1_, p2_) as p_))) ->
      formatLet callname (Psi, p_, [])
  | (callname, (Psi, (New (Lam (UDec (BDec (l, (c, s))), _)) as p_))) ->
      formatNew callname (Psi, p_, [])
  | (callname, (Psi, Redex (p_, s_))) -> formatRedex callname (Psi, p_, s_)
  | (callname, (Psi, Lam ((UDec (d'_) as d_), p_))) ->
      Fmt.HVbox
        [Fmt.String "lam";
        Fmt.Space;
        Fmt.String "(";
        Print.formatDec ((T.coerceCtx Psi), d'_);
        Fmt.String ")";
        Fmt.Space;
        formatPrg3 callname ((I.Decl (Psi, d_)), p_)]
  | (callname, (Psi, Rec ((PDec (Some name, f_, None, None) as d_), p_))) ->
      Fmt.HVbox
        [Fmt.String "fix*";
        Fmt.Space;
        Fmt.String "(";
        Fmt.String name;
        Fmt.String ":";
        formatFor (Psi, f_);
        Fmt.String ")";
        Fmt.Space;
        formatPrg3 callname ((I.Decl (Psi, d_)), p_)]
  | (callname,
     (Psi, Rec ((PDec (Some name, f_, Some (TC1), Some (TC2)) as d_), p_)))
      ->
      Fmt.HVbox
        [Fmt.String "fix";
        Fmt.Space;
        Fmt.String "(";
        Fmt.String name;
        Fmt.String ":";
        formatFor (Psi, f_);
        Fmt.String ")";
        Fmt.Space;
        formatPrg3 callname ((I.Decl (Psi, d_)), p_)]
  | (callname, (Psi, PClo (p_, t))) ->
      Fmt.HVbox [formatPrg3 callname (Psi, p_); Fmt.String "..."]
  | (callname, (Psi, (EVar (_, { contents = Some (p_) }, _, _, _, _) as x_)))
      -> formatPrg3 callname (Psi, p_)
  | (callname, (Psi, (EVar (_, { contents = None }, _, _, _, _) as x_))) ->
      Fmt.String (nameEVar x_)
  | (callname, (Psi, Case (Cases (cs_)))) ->
      Fmt.HVbox
        (((::) ((Fmt.String "case") :: Fmt.Break) formatCases
            (1, Psi, cs_, callname))
           @ [Fmt.String "."])
  | (callname, (Psi, Var n)) ->
      let PDec (Some n, _, _, _) = I.ctxLookup (Psi, n) in Fmt.String n
  | (callname, _) -> Fmt.String "missing case" end(* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *)
(* formatTuple (Psi, P) *)(* formatTuple (Psi, P) *)
let rec formatNew arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (callname, (Psi, New (Lam (UDec (BDec (l, (c, s)) as d_), p_)), fmts)) ->
      let g_ = T.coerceCtx Psi in
      let d'_ = Names.decName (g_, d_) in
      formatNew callname
        ((I.Decl (Psi, (T.UDec d'_))), p_,
          (((::) Fmt.Break Fmt.HVbox [Print.formatDec (g_, d'_)]) :: fmts))
  | (callname, (Psi, p_, fmts)) ->
      Fmt.Vbox0 0 1
        [Fmt.String "new";
        Fmt.Vbox0 0 1 fmts;
        Fmt.Break;
        Fmt.String "in";
        Fmt.Break;
        Fmt.Spaces 2;
        formatPrg3 callname (Psi, p_);
        Fmt.Break;
        Fmt.String "end"] end
let rec formatLet arg__12 arg__13 =
  begin match (arg__12, arg__13) with
  | (callname,
     (Psi, Let (d_, p1_, Case (Cases ((Psi1, s1, (Let _ as p2_))::[]))),
      fmts)) ->
      let Psi1' = psiName (Psi1, s1, Psi, 1) in
      let f1_ = Fmt.HVbox [formatPrg3 callname (Psi, p1_)] in
      let s_ = argsToSpine (s1, 1, T.Nil) in
      let Fspine = fmtSpine callname (Psi1, s_) in
      let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
      let Fbody = Fmt.HVbox [f1_] in
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
      ((formatLet callname (Psi1', p2_, (fmts @ [Fmt.Break; fmt])))
        (* was I.ctxLength Psi - max  --cs *)(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *))
  | (callname,
     (Psi, Let (d_, p1_, Case (Cases ((Psi1, s1, p2_)::[]))), fmts)) ->
      let Psi1' = psiName (Psi1, s1, Psi, 1) in
      let f1_ = Fmt.HVbox [formatPrg3 callname (Psi, p1_)] in
      let s_ = argsToSpine (s1, 1, T.Nil) in
      let Fspine = fmtSpine callname (Psi1, s_) in
      let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
      let Fbody = Fmt.HVbox [f1_] in
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
          formatPrg3 callname (Psi1', p2_);
          Fmt.Break;
          Fmt.String "end"])
        (* was I.ctxLength Psi - max  --cs *)(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
        (*            val fmt =  formatDecs (0, Psi, Ds, (Psi1', s1)) *))
  | (callname, (Psi, Let (d_, p1_, Case (Cases (l_))), [])) ->
      let rec fmtCaseRest =
        begin function
        | [] -> []
        | (Psi1, s1, p2_)::l_ ->
            let Psi1' = psiName (Psi1, s1, Psi, 1) in
            let s_ = argsToSpine (s1, 1, T.Nil) in
            let Fspine = fmtSpine callname (Psi1, s_) in
            let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
            (@) [Fmt.HVbox
                   [Fmt.Space;
                   Fmt.String "|";
                   Fmt.Space;
                   Fpattern;
                   Fmt.Space;
                   Fmt.String "-->"];
                Fmt.Spaces 2;
                Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', p2_)];
                Fmt.Break]
              fmtCaseRest l_ end in
    let rec fmtCase ((Psi1, s1, p2_)::l_) =
      let Psi1' = psiName (Psi1, s1, Psi, 1) in
      let s_ = argsToSpine (s1, 1, T.Nil) in
      let Fspine = fmtSpine callname (Psi1, s_) in
      let Fpattern = Fmt.HVbox [Fmt.Hbox Fspine] in
      Fmt.Vbox0 0 1
        ((@) [Fmt.HVbox
                [Fmt.String "of";
                Fmt.Space;
                Fpattern;
                Fmt.Space;
                Fmt.String "-->"];
             Fmt.Spaces 2;
             Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', p2_)];
             Fmt.Break]
           fmtCaseRest l_) in
    let f1_ = Fmt.HVbox [formatPrg3 callname (Psi, p1_)] in
    let Fbody = Fmt.HVbox [f1_] in
    let fmt = fmtCase l_ in
    Fmt.Vbox0 0 1
      (([Fmt.String "case (";
        Fbody;
        Fmt.Space;
        Fmt.String ")";
        Fmt.Break;
        fmt])
      (* need space since there is one before Fbody *))
  | (callname, (Psi, (Let (d_, p1_, Case (Cases (l_))) as r_), fmts)) ->
      Fmt.Vbox0 0 1
        [Fmt.String "let";
        Fmt.Vbox0 0 1 (fmts @ [Fmt.Break]);
        Fmt.Break;
        Fmt.String "in";
        Fmt.Break;
        Fmt.Spaces 2;
        formatLet callname (Psi, r_, []);
        Fmt.Break;
        Fmt.String "end"]
  | (callname,
     (Psi, (Let ((PDec (Some name, f_, _, _) as d_), p1_, p2_) as r_), fmts))
      ->
      Fmt.Vbox0 0 1
        [Fmt.String "let";
        Fmt.Break;
        Fmt.Vbox0 0 1
          [Fmt.String name;
          Fmt.Space;
          Fmt.String "=";
          formatPrg3 callname (Psi, p1_)];
        Fmt.Break;
        Fmt.String "in";
        Fmt.Break;
        Fmt.Spaces 2;
        formatPrg3 callname ((I.Decl (Psi, d_)), p2_);
        Fmt.Break;
        Fmt.String "end"]
  | (callname,
     (Psi,
      (LetPairExp
         ((Dec (Some n1, _) as d1_), (PDec (Some n2, f_, _, _) as d2_), p1_,
          p2_)
         as r_),
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
          formatPrg3 callname (Psi, p1_)];
        Fmt.Break;
        Fmt.String "in";
        Fmt.Break;
        Fmt.Spaces 2;
        formatPrg3 callname
          ((I.Decl ((I.Decl (Psi, (T.UDec d1_))), d2_)), p2_);
        Fmt.Break;
        Fmt.String "end"]
  | (callname, (Psi, (LetUnit (p1_, p2_) as r_), fmts)) ->
      Fmt.Vbox0 0 1
        [Fmt.String "let";
        Fmt.Break;
        Fmt.Spaces 2;
        Fmt.Vbox0 0 1
          [Fmt.String "()";
          Fmt.Space;
          Fmt.String "=";
          Fmt.Space;
          formatPrg3 callname (Psi, p1_)];
        Fmt.Break;
        Fmt.String "in";
        Fmt.Break;
        Fmt.Spaces 2;
        formatPrg3 callname (Psi, p2_);
        Fmt.Break;
        Fmt.String "end"] end(* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)
let rec formatHead callname (name, (max, index), Psi', s, Psi) =
  let s_ = argsToSpine (s, ((I.ctxLength Psi) - max), T.Nil) in
  let Fspine = fmtSpine callname (Psi', s_) in
  ((Fmt.Hbox
      [Fmt.Space; Fmt.HVbox (((Fmt.String name) :: Fmt.Break) :: Fspine)])
    (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *))
let rec formatPrg2 =
  begin function
  | (name, (max, index), Psi, [], callname) -> []
  | (name, (max, index), Psi, (Psi', s, p_)::[], callname) ->
      let Psi'' = psiName (Psi', s, Psi, 0) in
      let fhead = if (=) index I.ctxLength Psi then begin "fun" end
        else begin "and" end in
    [Fmt.HVbox0 1 5 1
       [Fmt.String fhead;
       formatHead callname (name, (max, index), Psi'', s, Psi);
       Fmt.Space;
       Fmt.String "=";
       Fmt.Break;
       formatPrg3 callname (Psi'', p_)];
    Fmt.Break]
  | (name, (max, index), Psi, (Psi', s, p_)::o_, callname) ->
      let Psi'' = psiName (Psi', s, Psi, 0) in
      (formatPrg2 (name, (max, index), Psi, o_, callname)) @
        [Fmt.HVbox0 1 5 1
           [Fmt.String "  |";
           formatHead callname (name, (max, index), Psi'', s, Psi);
           Fmt.Space;
           Fmt.String "=";
           Fmt.Break;
           formatPrg3 callname (Psi'', p_)];
        Fmt.Break] end
let rec formatPrg11 =
  begin function
  | (name, (max, index), Psi, Lam (d_, p_), callname) ->
      formatPrg11
        (name, (max, (index + 1)),
          (I.Decl (Psi, (decName ((T.coerceCtx Psi), d_)))), p_, callname)
  | (name, (max, index), Psi, Case (Cases (os_)), callname) ->
      formatPrg2 (name, (max, index), Psi, os_, callname) end
let rec formatPrg1 =
  begin function
  | (name::names, (max, index), Psi, PairPrg (p1_, p2_), callname) ->
      (@) (formatPrg11 (name, (max, index), Psi, p1_, callname)) formatPrg1
        (names, (max, (index - 1)), Psi, p2_, callname)
  | (name::[], (max, index), Psi, p_, callname) ->
      formatPrg11 (name, (max, index), Psi, p_, callname) end
let rec lookup (name::names, proj::projs) lemma =
  if lemma = proj then begin name end
  else begin lookup (names, projs) lemma end
let rec formatPrg0
  ((names, projs), Rec ((PDec (Some _, f_, _, _) as d_), p_)) =
  let max = 1 in
  ((Fmt.Vbox0 0 1
      (formatPrg1
         (names, (max, max), (I.Decl (I.Null, d_)), p_,
           (begin function | lemma -> lookup (names, projs) lemma end))))
  (* number of ih. *))
let rec formatFun (Args) = begin Names.varReset I.Null; formatPrg0 Args end
let rec funToString (Args) = Fmt.makestring_fmt (formatFun Args)
let rec prgToString (Args) =
  Fmt.makestring_fmt (formatPrg3 (begin function | _ -> "?" end) Args)
let rec nameCtx =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, UDec (d_)) ->
      I.Decl
        ((nameCtx Psi), (T.UDec (Names.decName ((T.coerceCtx Psi), d_))))
  | Decl (Psi, PDec (None, f_, TC1, TC2)) ->
      let Psi' = nameCtx Psi in
      let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec None)) in
      I.Decl (Psi', (T.PDec (x, f_, TC1, TC2)))
  | Decl (Psi, (PDec (Some n, f_, _, _) as d_)) -> I.Decl ((nameCtx Psi), d_) end
let rec flag = begin function | None -> "" | Some _ -> "*" end
let rec formatCtx =
  begin function
  | I.Null -> []
  | Decl (I.Null, UDec (d_)) ->
      if !Global.chatter >= 4
      then begin [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, d_)]] end
      else begin [Print.formatDec (I.Null, d_)] end
  | Decl (I.Null, PDec (Some s, f_, TC1, TC2)) ->
      if !Global.chatter >= 4
      then
        begin [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String ((^) "::" flag TC1);
                 Fmt.Space;
                 formatFor (I.Null, f_)]] end
      else begin
        [Fmt.String s;
        Fmt.Space;
        Fmt.String ((^) "::" flag TC1);
        Fmt.Space;
        formatFor (I.Null, f_)] end
| Decl (Psi, UDec (d_)) ->
    let g_ = T.coerceCtx Psi in
    if !Global.chatter >= 4
    then
      begin ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox [Fmt.Break; Print.formatDec (g_, d_)]] end
      else begin
        ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
          [Fmt.Break; Print.formatDec (g_, d_)] end
| Decl (Psi, PDec (Some s, f_, TC1, TC2)) ->
    if !Global.chatter >= 4
    then
      begin ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String ((^) "::" flag TC1);
                 Fmt.Space;
                 formatFor (Psi, f_)]] end
    else begin
      ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
        [Fmt.Break;
        Fmt.String s;
        Fmt.Space;
        Fmt.String ((^) "::" flag TC1);
        Fmt.Space;
        formatFor (Psi, f_)] end end
let rec ctxToString (Psi) = Fmt.makestring_fmt (Fmt.HVbox (formatCtx Psi))
let formatFor = formatFor
let forToString = forToString
let formatFun = formatFun
let formatPrg = formatPrg3 (begin function | _ -> "?" end)
let evarName = evarName
let evarReset = evarReset
let nameEVar = nameEVar
let prgToString = prgToString
let funToString = funToString
let nameCtx = nameCtx
let formatCtx = begin function | Psi -> Fmt.HVbox (formatCtx Psi) end
let ctxToString = ctxToString end
