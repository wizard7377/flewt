
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
      | (G, BVar n) ->
          let Dec (SOME n, _) = I.ctxDec (G, n) in
          sexp [Str (("<Var name = \"" ^ n) ^ "\"/>")]
      | (G, Const cid) ->
          sexp
            [Str "<Const name=\"";
            Str (I.conDecName (I.sgnLookup cid));
            Str "\"/>"]
      | (G, Def cid) ->
          sexp [Str "<Def>"; F.Break; Integer cid; Str "</Def>"]
      | (G, FgnConst (csid, condec)) -> sexp [Str "FngConst"]
    let rec fmtUni =
      function | I.Type -> Str "<Type/>" | I.Kind -> Str "<Kind/>"
    let rec fmtExpW =
      function
      | (G, (Uni (L), s)) ->
          sexp [Str "<Uni>"; F.Break; fmtUni L; Str "</Uni>"]
      | (G, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (G, D) in
               let G' = I.Decl (G, D') in
               sexp
                 [Str "<Pi>";
                 F.Break;
                 fmtDec (G, (D', s));
                 F.Break;
                 fmtExp (G', (V2, (I.dot1 s)));
                 Str "</Pi>"]
           | I.No ->
               let G' = I.Decl (G, D) in
               sexp
                 [Str "<Arrow>";
                 F.Break;
                 fmtDec' (G, (D, s));
                 F.Break;
                 fmtExp (G', (V2, (I.dot1 s)));
                 Str "</Arrow>"])
      | (G, (Root (H, S), s)) ->
          (match fmtSpine (G, (S, s)) with
           | NONE -> fmtCon (G, H)
           | SOME fmts ->
               F.HVbox
                 [Str "<App>";
                 fmtCon (G, H);
                 F.Break;
                 sexp fmts;
                 Str "</App>"])
      | (G, (Lam (D, U), s)) ->
          let D' = Names.decLUName (G, D) in
          let G' = I.Decl (G, D') in
          sexp
            [Str "<Lam>";
            F.Break;
            fmtDec (G, (D', s));
            F.Break;
            fmtExp (G', (U, (I.dot1 s)));
            Str "</Lam>"]
      | (G, (FgnExp (csid, F), s)) -> sexp [Str "FgnExp"]
    let rec fmtExp (G, (U, s)) = fmtExpW (G, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (G, (I.Nil, _)) -> NONE
      | (G, (SClo (S, s'), s)) -> fmtSpine (G, (S, (I.comp (s', s))))
      | (G, (App (U, S), s)) ->
          (match fmtSpine (G, (S, s)) with
           | NONE -> SOME [fmtExp (G, (U, s))]
           | SOME fmts -> SOME ([fmtExp (G, (U, s)); F.Break] @ fmts))
    let rec fmtDec =
      function
      | (G, (Dec (NONE, V), s)) ->
          sexp [Str "<Dec>"; F.Break; fmtExp (G, (V, s)); Str "</Dec>"]
      | (G, (Dec (SOME x, V), s)) ->
          sexp
            [Str "<Dec name =";
            Name x;
            Str ">";
            F.Break;
            fmtExp (G, (V, s));
            Str "</Dec>"]
    let rec fmtDec' =
      function
      | (G, (Dec (NONE, V), s)) -> sexp [fmtExp (G, (V, s))]
      | (G, (Dec (SOME x, V), s)) -> sexp [fmtExp (G, (V, s))]
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
    let rec fmtEqn (Eqn (G, U1, U2)) =
      sexp
        [Str "<Equation>";
        F.Break;
        fmtExp (G, (U1, I.id));
        F.Break;
        fmtExp (G, (U2, I.id));
        Str "</Equation>"]
    let rec fmtEqnName (Eqn (G, U1, U2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName G), U1, U2))
    let rec formatDec
      (((G)(* Shorthands *)(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
       (* FIX -cs Fri Jan 28 17:45:35 2005*)(* I.Skonst, I.FVar cases should be impossible *)
       (* fmtUni (L) = "L" *)(* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
       (* if Pi is dependent but anonymous, invent name here *)(* could sometimes be EName *)
       (* Str "tw*maybe", F.Break, *)(* Str "tw*no", F.Break,*)
       (* FIX -cs Fri Jan 28 17:45:43 2005 *)(* I.EClo, I.Redex, I.EVar not possible *)
       (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
       (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
       (* fmtEqn assumes that G is a valid printing context *)(* print context?? *)
       (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
       (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)),
       D)
      = fmtDec (G, (D, I.id))
    let rec formatExp (G, U) = fmtExp (G, (U, I.id))
    let rec formatConDec
      ((condec)(*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *))
      = fmtConDec condec
    let rec formatEqn (E) = fmtEqn E
    let rec decToString (G, D) = F.makestring_fmt (formatDec (G, D))
    let rec expToString (G, U) = F.makestring_fmt (formatExp (G, U))
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
