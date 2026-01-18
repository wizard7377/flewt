
(* Printing Signatures *)
(* Author: Frank Pfenning *)
module type PRINT_TWEGA  =
  sig val printSgn : unit -> unit val printSgnToFile : string -> unit end;;




(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
module PrintTwega(PrintTwega:sig
                               (*! structure IntSyn' : INTSYN !*)
                               module Whnf : WHNF
                               module Abstract : ABSTRACT
                               module Constraints : CONSTRAINTS
                               module Names : NAMES
                               (*! sharing Whnf.IntSyn = IntSyn' !*)
                               (*! sharing Abstract.IntSyn = IntSyn' !*)
                               (*! sharing Constraints.IntSyn = IntSyn' !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               module Formatter' : FORMATTER
                             end) : PRINT_TWEGA =
  struct
    (*! structure IntSyn = IntSyn' !*)
    module Formatter = Formatter'
    (* Shorthands *)
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (Int.toString n)
    let rec sexp fmts = F.Hbox [Str "("; F.HVbox fmts; Str ")"]
    let rec fmtCon =
      function
      | (G, BVar n) -> sexp [Str "tw~bvar"; F.Break; Integer n]
      | (G, Const cid) -> sexp [Str "tw~const"; F.Break; Integer cid]
      | (G, Def cid) -> sexp [Str "tw~def"; F.Break; Integer cid]
    let rec fmtUni =
      function | I.Type -> Str "tw*type" | I.Kind -> Str "tw*kind"
    let rec fmtExpW =
      function
      | (G, (Uni (L), s)) -> sexp [Str "tw~uni"; F.Break; fmtUni L]
      | (G, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (G, D) in
               let G' = I.Decl (G, D') in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (G, (D', s));
                 F.Break;
                 Str "tw*maybe";
                 F.Break;
                 fmtExp (G', (V2, (I.dot1 s)))]
           | I.No ->
               let G' = I.Decl (G, D) in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (G, (D, s));
                 F.Break;
                 Str "tw*no";
                 F.Break;
                 fmtExp (G', (V2, (I.dot1 s)))])
      | (G, (Root (H, S), s)) ->
          sexp
            [Str "tw~root";
            F.Break;
            fmtCon (G, H);
            F.Break;
            fmtSpine (G, (S, s))]
      | (G, (Lam (D, U), s)) ->
          let D' = Names.decLUName (G, D) in
          let G' = I.Decl (G, D') in
          sexp
            [Str "tw~lam";
            F.Break;
            fmtDec (G, (D', s));
            F.Break;
            fmtExp (G', (U, (I.dot1 s)))]
    let rec fmtExp (G, (U, s)) = fmtExpW (G, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (G, (I.Nil, _)) -> Str "tw*empty-spine"
      | (G, (SClo (S, s'), s)) -> fmtSpine (G, (S, (I.comp (s', s))))
      | (G, (App (U, S), s)) ->
          sexp
            [Str "tw~app";
            F.Break;
            fmtExp (G, (U, s));
            F.Break;
            fmtSpine (G, (S, s))]
    let rec fmtDec =
      function
      | (G, (Dec (NONE, V), s)) ->
          sexp
            [Str "tw~decl"; F.Break; Str "nil"; F.Break; fmtExp (G, (V, s))]
      | (G, (Dec (SOME x, V), s)) ->
          sexp [Str "tw~decl"; F.Break; Name x; F.Break; fmtExp (G, (V, s))]
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
    let rec fmtEqn (Eqn (G, U1, U2)) =
      sexp
        [Str "tw*eqn";
        F.Break;
        fmtExp (G, (U1, I.id));
        F.Break;
        fmtExp (G, (U2, I.id))]
    let rec fmtEqnName (Eqn (G, U1, U2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName G), U1, U2))
    (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
    (* I.Skonst, I.FVar cases should be impossible *)
    (* fmtUni (L) = "L" *)
    (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
    (* if Pi is dependent but anonymous, invent name here *)
    (* could sometimes be EName *)
    (* I.EClo, I.Redex, I.EVar not possible *)
    (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
    (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
    (* fmtEqn assumes that G is a valid printing context *)
    (* print context?? *)
    (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
    (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
    let rec formatDec (G, D) = fmtDec (G, (D, I.id))
    let rec formatExp (G, U) = fmtExp (G, (U, I.id))
    let rec formatSpine (G, S) = fmtSpine (G, (S, I.id))
    let rec formatConDec condec = fmtConDec condec
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
