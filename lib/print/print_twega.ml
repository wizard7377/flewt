
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
    let rec sexp fmts = F.hbox [Str "("; F.hVbox fmts; Str ")"]
    let rec fmtCon =
      function
      | (__g, BVar n) -> sexp [Str "tw~bvar"; F.Break; Integer n]
      | (__g, Const cid) -> sexp [Str "tw~const"; F.Break; Integer cid]
      | (__g, Def cid) -> sexp [Str "tw~def"; F.Break; Integer cid]
    let rec fmtUni =
      function | I.Type -> Str "tw*type" | I.Kind -> Str "tw*kind"
    let rec fmtExpW =
      function
      | (__g, (Uni (__l), s)) -> sexp [Str "tw~uni"; F.Break; fmtUni __l]
      | (__g, (Pi (((Dec (_, V1) as __d), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let __d' = Names.decLUName (__g, __d) in
               let __g' = I.Decl (__g, __d') in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (__g, (__d', s));
                 F.Break;
                 Str "tw*maybe";
                 F.Break;
                 fmtExp (__g', (V2, (I.dot1 s)))]
           | I.No ->
               let __g' = I.Decl (__g, __d) in
               sexp
                 [Str "tw~pi";
                 F.Break;
                 fmtDec (__g, (__d, s));
                 F.Break;
                 Str "tw*no";
                 F.Break;
                 fmtExp (__g', (V2, (I.dot1 s)))])
      | (__g, (Root (H, S), s)) ->
          sexp
            [Str "tw~root";
            F.Break;
            fmtCon (__g, H);
            F.Break;
            fmtSpine (__g, (S, s))]
      | (__g, (Lam (__d, __u), s)) ->
          let __d' = Names.decLUName (__g, __d) in
          let __g' = I.Decl (__g, __d') in
          sexp
            [Str "tw~lam";
            F.Break;
            fmtDec (__g, (__d', s));
            F.Break;
            fmtExp (__g', (__u, (I.dot1 s)))]
    let rec fmtExp (__g, (__u, s)) = fmtExpW (__g, (Whnf.whnf (__u, s)))
    let rec fmtSpine =
      function
      | (__g, (I.Nil, _)) -> Str "tw*empty-spine"
      | (__g, (SClo (S, s'), s)) -> fmtSpine (__g, (S, (I.comp (s', s))))
      | (__g, (App (__u, S), s)) ->
          sexp
            [Str "tw~app";
            F.Break;
            fmtExp (__g, (__u, s));
            F.Break;
            fmtSpine (__g, (S, s))]
    let rec fmtDec =
      function
      | (__g, (Dec (None, __v), s)) ->
          sexp
            [Str "tw~decl"; F.Break; Str "nil"; F.Break; fmtExp (__g, (__v, s))]
      | (__g, (Dec (Some x, __v), s)) ->
          sexp [Str "tw~decl"; F.Break; Name x; F.Break; fmtExp (__g, (__v, s))]
    let rec fmtConDec =
      function
      | ConDec (name, parent, imp, _, __v, __l) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__v, I.id));
            F.Break;
            fmtUni __l]
      | SkoDec (name, parent, imp, __v, __l) ->
          Str (("%% Skipping Skolem constant " ^ name) ^ " %%")
      | ConDef (name, parent, imp, __u, __v, __l, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__u, I.id));
            F.Break;
            fmtExp (I.Null, (__v, I.id));
            F.Break;
            fmtUni __l]
      | AbbrevDef (name, parent, imp, __u, __v, __l) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__u, I.id));
            F.Break;
            fmtExp (I.Null, (__v, I.id));
            F.Break;
            fmtUni __l]
    let rec fmtEqn (Eqn (__g, __U1, __U2)) =
      sexp
        [Str "tw*eqn";
        F.Break;
        fmtExp (__g, (__U1, I.id));
        F.Break;
        fmtExp (__g, (__U2, I.id))]
    let rec fmtEqnName (Eqn (__g, __U1, __U2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName __g), __U1, __U2))
    (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
    (* I.Skonst, I.FVar cases should be impossible *)
    (* fmtUni (__l) = "__l" *)
    (* fmtExpW (__g, (__u, s)) = fmt

     format the expression __u[s].

     Invariants:
       __g is a "printing context" (names in it are unique, but
            types may be incorrect) approximating __g'
       __g'' |- __u : __v   __g' |- s : __g''  (so  __g' |- __u[s] : __v[s])
       (__u,s) in whnf
  *)
    (* if Pi is dependent but anonymous, invent name here *)
    (* could sometimes be EName *)
    (* I.EClo, I.Redex, I.EVar not possible *)
    (* fmtSpine (__g, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context __g which approximates __g', where __g' |- S[s] is valid
  *)
    (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
    (* fmtEqn assumes that __g is a valid printing context *)
    (* print context?? *)
    (* fmtEqnName and fmtEqns do not assume that __g is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
    (* In the functions below, __g must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
    let rec formatDec (__g, __d) = fmtDec (__g, (__d, I.id))
    let rec formatExp (__g, __u) = fmtExp (__g, (__u, I.id))
    let rec formatSpine (__g, S) = fmtSpine (__g, (S, I.id))
    let rec formatConDec condec = fmtConDec condec
    let rec formatEqn (E) = fmtEqn E
    let rec decToString (__g, __d) = F.makestring_fmt (formatDec (__g, __d))
    let rec expToString (__g, __u) = F.makestring_fmt (formatExp (__g, __u))
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
