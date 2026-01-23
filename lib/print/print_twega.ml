module type PRINT_TWEGA  =
  sig val printSgn : unit -> unit val printSgnToFile : string -> unit end


module PrintTwega(PrintTwega:sig
                               module Whnf : WHNF
                               module Abstract : ABSTRACT
                               module Constraints : CONSTRAINTS
                               module Names : NAMES
                               module Formatter' : FORMATTER
                             end) : PRINT_TWEGA =
  struct
    module Formatter = Formatter'
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (Int.toString n)
    let rec sexp fmts = F.Hbox [Str "("; F.HVbox fmts; Str ")"]
    let rec fmtCon =
      begin function
      | (g_, BVar n) -> sexp [Str "tw~bvar"; F.Break; Integer n]
      | (g_, Const cid) -> sexp [Str "tw~const"; F.Break; Integer cid]
      | (g_, Def cid) -> sexp [Str "tw~def"; F.Break; Integer cid] end
    let rec fmtUni =
      begin function | I.Type -> Str "tw*type" | I.Kind -> Str "tw*kind" end
  let rec fmtExpW =
    begin function
    | (g_, (Uni (l_), s)) -> sexp [Str "tw~uni"; F.Break; fmtUni l_]
    | (g_, (Pi (((Dec (_, v1_) as d_), p_), v2_), s)) ->
        (((begin match p_ with
           | I.Maybe ->
               let d'_ = Names.decLUName (g_, d_) in
               let g'_ = I.Decl (g_, d'_) in
               ((sexp
                   [Str "tw~pi";
                   F.Break;
                   fmtDec (g_, (d'_, s));
                   F.Break;
                   Str "tw*maybe";
                   F.Break;
                   fmtExp (g'_, (v2_, (I.dot1 s)))])
                 (* could sometimes be EName *))
           | I.No ->
               let g'_ = I.Decl (g_, d_) in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (g_, (d_, s));
                 F.Break;
                 Str "tw*no";
                 F.Break;
                 fmtExp (g'_, (v2_, (I.dot1 s)))] end))
    (* if Pi is dependent but anonymous, invent name here *))
    | (g_, (Root (h_, s_), s)) ->
        sexp
          [Str "tw~root";
          F.Break;
          fmtCon (g_, h_);
          F.Break;
          fmtSpine (g_, (s_, s))]
    | (g_, (Lam (d_, u_), s)) ->
        let d'_ = Names.decLUName (g_, d_) in
        let g'_ = I.Decl (g_, d'_) in
        sexp
          [Str "tw~lam";
          F.Break;
          fmtDec (g_, (d'_, s));
          F.Break;
          fmtExp (g'_, (u_, (I.dot1 s)))] end
let rec fmtExp (g_, (u_, s)) = fmtExpW (g_, (Whnf.whnf (u_, s)))
let rec fmtSpine =
  begin function
  | (g_, (I.Nil, _)) -> Str "tw*empty-spine"
  | (g_, (SClo (s_, s'), s)) -> fmtSpine (g_, (s_, (I.comp (s', s))))
  | (g_, (App (u_, s_), s)) ->
      sexp
        [Str "tw~app";
        F.Break;
        fmtExp (g_, (u_, s));
        F.Break;
        fmtSpine (g_, (s_, s))] end
let rec fmtDec =
  begin function
  | (g_, (Dec (None, v_), s)) ->
      sexp [Str "tw~decl"; F.Break; Str "nil"; F.Break; fmtExp (g_, (v_, s))]
  | (g_, (Dec (Some x, v_), s)) ->
      sexp [Str "tw~decl"; F.Break; Name x; F.Break; fmtExp (g_, (v_, s))] end
let rec fmtConDec =
  begin function
  | ConDec (name, parent, imp, _, v_, l_) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "tw~defConst";
        F.Space;
        Name name;
        F.Break;
        Integer imp;
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_]
  | SkoDec (name, parent, imp, v_, l_) ->
      Str (("%% Skipping Skolem constant " ^ name) ^ " %%")
  | ConDef (name, parent, imp, u_, v_, l_, _) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "tw~defConst";
        F.Space;
        Name name;
        F.Break;
        Integer imp;
        F.Break;
        fmtExp (I.Null, (u_, I.id));
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_]
  | AbbrevDef (name, parent, imp, u_, v_, l_) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "tw~defConst";
        F.Space;
        Name name;
        F.Break;
        Integer imp;
        F.Break;
        fmtExp (I.Null, (u_, I.id));
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_] end
let rec fmtEqn (Eqn (g_, u1_, u2_)) =
  sexp
    [Str "tw*eqn";
    F.Break;
    fmtExp (g_, (u1_, I.id));
    F.Break;
    fmtExp (g_, (u2_, I.id))](* print context?? *)
let rec fmtEqnName (Eqn (g_, u1_, u2_)) =
  fmtEqn (I.Eqn ((Names.ctxLUName g_), u1_, u2_))
let rec formatDec (g_, d_) = fmtDec (g_, (d_, I.id))
let rec formatExp (g_, u_) = fmtExp (g_, (u_, I.id))
let rec formatSpine (g_, s_) = fmtSpine (g_, (s_, I.id))
let rec formatConDec condec = fmtConDec condec
let rec formatEqn (e_) = fmtEqn e_
let rec decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_))
let rec expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_))
let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
let rec eqnToString (e_) = F.makestring_fmt (formatEqn e_)
let rec printSgn () =
  IntSyn.sgnApp
    (begin function
     | cid ->
         (begin print
                  (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
          print "\n" end) end)
let rec printSgnToFile filename =
  let file = TextIO.openOut filename in
  let _ =
    IntSyn.sgnApp
      (begin function
       | cid ->
           (begin TextIO.output
                    (file,
                      (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
            TextIO.output (file, "\n") end) end) in
let _ = TextIO.closeOut file in () end
