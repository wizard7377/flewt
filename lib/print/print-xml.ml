
module type PRINT_XML  =
  sig
    val printSgn :
      unit ->
        ((unit)(* modified: Carsten Schuermann *)(* Author: Frank Pfenning *)
        (* Printing Signatures *))
    val printSgnToFile : string -> string -> unit
  end;;




module PrintXML(PrintXML:sig
                           module Whnf : WHNF
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module Names : NAMES
                           module Formatter' :
                           ((FORMATTER)(* Printing *)
                           (* Author: Frank Pfenning *)
                           (* Modified: Jeff Polakow *)
                           (* Modified: Carsten Schuermann *)(*! structure IntSyn' : INTSYN !*)
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Abstract.IntSyn = IntSyn' !*)
                           (*! sharing Constraints.IntSyn = IntSyn' !*)
                           (*! sharing Names.IntSyn = IntSyn' !*))
                         end) : PRINT_XML =
  struct
    module Formatter =
      ((Formatter')(*! structure IntSyn = IntSyn' !*))
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (((^) "\"" Int.toString n) ^ "\"")
    let rec sexp fmts = F.Hbox [F.HVbox fmts]
    let rec fmtCon =
      function
      | (g, BVar n) ->
          let Dec (SOME n, _) = I.ctxDec (g, n) in
          sexp [Str (("<Var name = \"" ^ n) ^ "\"/>")]
      | (g, Const cid) ->
          sexp
            [Str "<Const name=\"";
            Str (I.conDecName (I.sgnLookup cid));
            Str "\"/>"]
      | (g, Def cid) ->
          sexp [Str "<Def>"; F.Break; Integer cid; Str "</Def>"]
      | (g, FgnConst (csid, condec)) -> sexp [Str "FngConst"]
    let rec fmtUni =
      function | I.Type -> Str "<Type/>" | I.Kind -> Str "<Kind/>"
    let rec fmtExpW =
      function
      | (g, (Uni (L), s)) ->
          sexp [Str "<Uni>"; F.Break; fmtUni L; Str "</Uni>"]
      | (g, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (g, D) in
               let g' = I.Decl (g, D') in
               sexp
                 [Str "<Pi>";
                 F.Break;
                 fmtDec (g, (D', s));
                 F.Break;
                 fmtExp (g', (V2, (I.dot1 s)));
                 Str "</Pi>"]
           | I.No ->
               let g' = I.Decl (g, D) in
               sexp
                 [Str "<Arrow>";
                 F.Break;
                 fmtDec' (g, (D, s));
                 F.Break;
                 fmtExp (g', (V2, (I.dot1 s)));
                 Str "</Arrow>"])
      | (g, (Root (H, S), s)) ->
          (match fmtSpine (g, (S, s)) with
           | NONE -> fmtCon (g, H)
           | SOME fmts ->
               F.HVbox
                 [Str "<App>";
                 fmtCon (g, H);
                 F.Break;
                 sexp fmts;
                 Str "</App>"])
      | (g, (Lam (D, U), s)) ->
          let D' = Names.decLUName (g, D) in
          let g' = I.Decl (g, D') in
          sexp
            [Str "<Lam>";
            F.Break;
            fmtDec (g, (D', s));
            F.Break;
            fmtExp (g', (U, (I.dot1 s)));
            Str "</Lam>"]
      | (g, (FgnExp (csid, F), s)) -> sexp [Str "FgnExp"]
    let rec fmtExp (g, (U, s)) = fmtExpW (g, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (g, (I.Nil, _)) -> NONE
      | (g, (SClo (S, s'), s)) -> fmtSpine (g, (S, (I.comp (s', s))))
      | (g, (App (U, S), s)) ->
          (match fmtSpine (g, (S, s)) with
           | NONE -> SOME [fmtExp (g, (U, s))]
           | SOME fmts -> SOME ([fmtExp (g, (U, s)); F.Break] @ fmts))
    let rec fmtDec =
      function
      | (g, (Dec (NONE, V), s)) ->
          sexp [Str "<Dec>"; F.Break; fmtExp (g, (V, s)); Str "</Dec>"]
      | (g, (Dec (SOME x, V), s)) ->
          sexp
            [Str "<Dec name =";
            Name x;
            Str ">";
            F.Break;
            fmtExp (g, (V, s));
            Str "</Dec>"]
    let rec fmtDec' =
      function
      | (g, (Dec (NONE, V), s)) -> sexp [fmtExp (g, (V, s))]
      | (g, (Dec (SOME x, V), s)) -> sexp [fmtExp (g, (V, s))]
    let rec fmtConDec =
      function
      | ConDec (name, parent, imp, _, V, L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Condec name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Condec>"]
      | SkoDec (name, parent, imp, V, L) ->
          Str (("<! Skipping Skolem constant " ^ name) ^ ">")
      | ConDef (name, parent, imp, U, V, L, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Condef name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Condef>"]
      | AbbrevDef (name, parent, imp, U, V, L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Abbrevdef name=";
            Name name;
            Str ">";
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Abbrevdef>"]
      | BlockDec (name, _, _, _) ->
          Str (("<! Skipping Skolem constant " ^ name) ^ ">")
    let rec fmtEqn (Eqn (g, u1, u2)) =
      sexp
        [Str "<Equation>";
        F.Break;
        fmtExp (g, (u1, I.id));
        F.Break;
        fmtExp (g, (u2, I.id));
        Str "</Equation>"]
    let rec fmtEqnName (Eqn (g, u1, u2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName g), u1, u2))
    let rec formatDec
      (((g)(* Shorthands *)(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
       (* FIX -cs Fri Jan 28 17:45:35 2005*)(* I.Skonst, I.FVar cases should be impossible *)
       (* fmtUni (L) = "L" *)(* fmtExpW (g, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       g is a "printing context" (names in it are unique, but
            types may be incorrect) approximating g'
       g'' |- U : V   g' |- s : g''  (so  g' |- U[s] : V[s])
       (U,s) in whnf
  *)
       (* if Pi is dependent but anonymous, invent name here *)(* could sometimes be EName *)
       (* Str "tw*maybe", F.Break, *)(* Str "tw*no", F.Break,*)
       (* FIX -cs Fri Jan 28 17:45:43 2005 *)(* I.EClo, I.Redex, I.EVar not possible *)
       (* fmtSpine (g, (S, s)) = fmts
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
    let rec formatConDec
      ((condec)(*  fun formatSpine (g, S) = sexp (fmtSpine (g, (S, I.id))) *))
      = fmtConDec condec
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
    let rec printSgnToFile path filename =
      let file = TextIO.openOut (path ^ filename) in
      let _ =
        TextIO.output
          (file,
            "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- nsgmls ex.xml -->\n<!DOCTYPE Signature SYSTEM \"lf.dtd\">\n<Signature>") in
      let _ =
        IntSyn.sgnApp
          (function
           | cid ->
               (TextIO.output
                  (file,
                    (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
                TextIO.output (file, "\n"))) in
      let _ = TextIO.output (file, "</Signature>") in
      let _ = TextIO.closeOut file in ()
  end ;;
