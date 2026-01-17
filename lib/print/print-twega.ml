
module type PRINT_TWEGA  =
  sig
    val printSgn :
      unit ->
        ((unit)(* Author: Frank Pfenning *)(* Printing Signatures *))
    val printSgnToFile : string -> unit
  end;;




module PrintTwega(PrintTwega:sig
                               module Whnf : WHNF
                               module Abstract : ABSTRACT
                               module Constraints : CONSTRAINTS
                               module Names : NAMES
                               module Formatter' :
                               ((FORMATTER)(* Printing *)
                               (* Author: Frank Pfenning *)
                               (* Modified: Jeff Polakow *)
                               (*! structure IntSyn' : INTSYN !*)
                               (*! sharing Whnf.IntSyn = IntSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn' !*)
                               (*! sharing Constraints.IntSyn = IntSyn' !*)
                               (*! sharing Names.IntSyn = IntSyn' !*))
                             end) : PRINT_TWEGA =
  struct
    module Formatter =
      ((Formatter')(*! structure IntSyn = IntSyn' !*))
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (Int.toString n)
    let rec sexp fmts = F.Hbox [Str "("; F.HVbox fmts; Str ")"]
    let rec fmtCon =
      function
      | (g, BVar n) -> sexp [Str "tw~bvar"; F.Break; Integer n]
      | (g, Const cid) -> sexp [Str "tw~const"; F.Break; Integer cid]
      | (g, Def cid) -> sexp [Str "tw~def"; F.Break; Integer cid]
    let rec fmtUni =
      function | I.Type -> Str "tw*type" | I.Kind -> Str "tw*kind"
    let rec fmtExpW =
      function
      | (g, (Uni (L), s)) -> sexp [Str "tw~uni"; F.Break; fmtUni L]
      | (g, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (g, D) in
               let g' = I.Decl (g, D') in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (g, (D', s));
                 F.Break;
                 Str "tw*maybe";
                 F.Break;
                 fmtExp (g', (V2, (I.dot1 s)))]
           | I.No ->
               let g' = I.Decl (g, D) in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (g, (D, s));
                 F.Break;
                 Str "tw*no";
                 F.Break;
                 fmtExp (g', (V2, (I.dot1 s)))])
      | (g, (Root (H, S), s)) ->
          sexp
            [Str "tw~root";
            F.Break;
            fmtCon (g, H);
            F.Break;
            fmtSpine (g, (S, s))]
      | (g, (Lam (D, U), s)) ->
          let D' = Names.decLUName (g, D) in
          let g' = I.Decl (g, D') in
          sexp
            [Str "tw~lam";
            F.Break;
            fmtDec (g, (D', s));
            F.Break;
            fmtExp (g', (U, (I.dot1 s)))]
    let rec fmtExp (g, (U, s)) = fmtExpW (g, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (g, (I.Nil, _)) -> Str "tw*empty-spine"
      | (g, (SClo (S, s'), s)) -> fmtSpine (g, (S, (I.comp (s', s))))
      | (g, (App (U, S), s)) ->
          sexp
            [Str "tw~app";
            F.Break;
            fmtExp (g, (U, s));
            F.Break;
            fmtSpine (g, (S, s))]
    let rec fmtDec =
      function
      | (g, (Dec (NONE, V), s)) ->
          sexp
            [Str "tw~decl"; F.Break; Str "nil"; F.Break; fmtExp (g, (V, s))]
      | (g, (Dec (SOME x, V), s)) ->
          sexp [Str "tw~decl"; F.Break; Name x; F.Break; fmtExp (g, (V, s))]
    let rec fmtConDec =
      function
      | ConDec (name, parent, imp, _, V, L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L]
      | SkoDec (name, parent, imp, V, L) ->
          Str (("%% Skipping Skolem constant " ^ name) ^ " %%")
      | ConDef (name, parent, imp, U, V, L, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L]
      | AbbrevDef (name, parent, imp, U, V, L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L]
    let rec fmtEqn (Eqn (g, u1, u2)) =
      sexp
        [Str "tw*eqn";
        F.Break;
        fmtExp (g, (u1, I.id));
        F.Break;
        fmtExp (g, (u2, I.id))]
    let rec fmtEqnName (Eqn (g, u1, u2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName g), u1, u2))
    let rec formatDec
      (((g)(* Shorthands *)(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
       (* I.Skonst, I.FVar cases should be impossible *)
       (* fmtUni (L) = "L" *)(* fmtExpW (g, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       g is a "printing context" (names in it are unique, but
            types may be incorrect) approximating g'
       g'' |- U : V   g' |- s : g''  (so  g' |- U[s] : V[s])
       (U,s) in whnf
  *)
       (* if Pi is dependent but anonymous, invent name here *)(* could sometimes be EName *)
       (* I.EClo, I.Redex, I.EVar not possible *)(* fmtSpine (g, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context g which approximates g', where g' |- S[s] is valid
  *)
       (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
       (* fmtEqn assumes that g is a valid printing context *)(* print context?? *)
       (* fmtEqnName and fmtEqns do not assume that g is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
       (* In the functions below, g must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)),
       D)
      = fmtDec (g, (D, I.id))
    let rec formatExp (g, U) = fmtExp (g, (U, I.id))
    let rec formatSpine (g, S) = fmtSpine (g, (S, I.id))
    let rec formatConDec condec = fmtConDec condec
    let rec formatEqn (E) = fmtEqn E
    let rec decToString (g, D) = F.makestring_fmt (formatDec (g, D))
    let rec expToString (g, U) = F.makestring_fmt (formatExp (g, U))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec eqnToString (E) = F.makestring_fmt (formatEqn E)
    let rec printSgn () =
      IntSyn.sgnApp
        (function
         | cid ->
             (print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
              print "\n"))
    let rec printSgnToFile filename =
      let file = TextIO.openOut filename in
      let _ =
        IntSyn.sgnApp
          (function
           | cid ->
               (TextIO.output
                  (file,
                    (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
                TextIO.output (file, "\n"))) in
      let _ = TextIO.closeOut file in ()
  end ;;
