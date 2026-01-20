
module type PRINT_TWEGA  =
  sig val printSgn : unit -> unit val printSgnToFile : string -> unit end;;




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
    let rec Str0 s n = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (Int.toString n)
    let rec sexp fmts = F.Hbox [Str "("; F.HVbox fmts; Str ")"]
    let rec fmtCon __0__ __1__ =
      match (__0__, __1__) with
      | (__G, BVar n) -> sexp [Str "tw~bvar"; F.Break; Integer n]
      | (__G, Const cid) -> sexp [Str "tw~const"; F.Break; Integer cid]
      | (__G, Def cid) -> sexp [Str "tw~def"; F.Break; Integer cid]
    let rec fmtUni =
      function | I.Type -> Str "tw*type" | I.Kind -> Str "tw*kind"
    let rec fmtExpW __2__ __3__ =
      match (__2__, __3__) with
      | (__G, (Uni (__L), s)) -> sexp [Str "tw~uni"; F.Break; fmtUni __L]
      | (__G, (Pi (((Dec (_, __V1) as D), __P), __V2), s)) ->
          (((match __P with
             | I.Maybe ->
                 let __D' = Names.decLUName (__G, __D) in
                 let __G' = I.Decl (__G, __D') in
                 ((sexp
                     [Str "tw~pi";
                     F.Break;
                     fmtDec (__G, (__D', s));
                     F.Break;
                     Str "tw*maybe";
                     F.Break;
                     fmtExp (__G', (__V2, (I.dot1 s)))])
                   (* could sometimes be EName *))
             | I.No ->
                 let __G' = I.Decl (__G, __D) in
                 sexp
                   [Str "tw~pi";
                   F.Break;
                   fmtDec (__G, (__D, s));
                   F.Break;
                   Str "tw*no";
                   F.Break;
                   fmtExp (__G', (__V2, (I.dot1 s)))]))
          (* if Pi is dependent but anonymous, invent name here *))
      | (__G, (Root (__H, __S), s)) ->
          sexp
            [Str "tw~root";
            F.Break;
            fmtCon (__G, __H);
            F.Break;
            fmtSpine (__G, (__S, s))]
      | (__G, (Lam (__D, __U), s)) ->
          let __D' = Names.decLUName (__G, __D) in
          let __G' = I.Decl (__G, __D') in
          sexp
            [Str "tw~lam";
            F.Break;
            fmtDec (__G, (__D', s));
            F.Break;
            fmtExp (__G', (__U, (I.dot1 s)))]
    let rec fmtExp (__G) (__U, s) = fmtExpW (__G, (Whnf.whnf (__U, s)))
    let rec fmtSpine __4__ __5__ =
      match (__4__, __5__) with
      | (__G, (I.Nil, _)) -> Str "tw*empty-spine"
      | (__G, (SClo (__S, s'), s)) -> fmtSpine (__G, (__S, (I.comp (s', s))))
      | (__G, (App (__U, __S), s)) ->
          sexp
            [Str "tw~app";
            F.Break;
            fmtExp (__G, (__U, s));
            F.Break;
            fmtSpine (__G, (__S, s))]
    let rec fmtDec __6__ __7__ =
      match (__6__, __7__) with
      | (__G, (Dec (None, __V), s)) ->
          sexp
            [Str "tw~decl";
            F.Break;
            Str "nil";
            F.Break;
            fmtExp (__G, (__V, s))]
      | (__G, (Dec (Some x, __V), s)) ->
          sexp
            [Str "tw~decl"; F.Break; Name x; F.Break; fmtExp (__G, (__V, s))]
    let rec fmtConDec =
      function
      | ConDec (name, parent, imp, _, __V, __L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L]
      | SkoDec (name, parent, imp, __V, __L) ->
          Str (("%% Skipping Skolem constant " ^ name) ^ " %%")
      | ConDef (name, parent, imp, __U, __V, __L, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__U, I.id));
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L]
      | AbbrevDef (name, parent, imp, __U, __V, __L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "tw~defConst";
            F.Space;
            Name name;
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__U, I.id));
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L]
    let rec fmtEqn (Eqn (__G, __U1, __U2)) =
      sexp
        [Str "tw*eqn";
        F.Break;
        fmtExp (__G, (__U1, I.id));
        F.Break;
        fmtExp (__G, (__U2, I.id))](* print context?? *)
    let rec fmtEqnName (Eqn (__G, __U1, __U2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName __G), __U1, __U2))
    let rec formatDec (__G) (__D) = fmtDec (__G, (__D, I.id))
    let rec formatExp (__G) (__U) = fmtExp (__G, (__U, I.id))
    let rec formatSpine (__G) (__S) = fmtSpine (__G, (__S, I.id))
    let rec formatConDec condec = fmtConDec condec
    let rec formatEqn (__E) = fmtEqn __E
    let rec decToString (__G) (__D) = F.makestring_fmt (formatDec (__G, __D))
    let rec expToString (__G) (__U) = F.makestring_fmt (formatExp (__G, __U))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec eqnToString (__E) = F.makestring_fmt (formatEqn __E)
    let rec printSgn () =
      IntSyn.sgnApp
        (fun cid ->
           print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
           print "\n")
    let rec printSgnToFile filename =
      let file = TextIO.openOut filename in
      let _ =
        IntSyn.sgnApp
          (fun cid ->
             TextIO.output
               (file,
                 (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
             TextIO.output (file, "\n")) in
      let _ = TextIO.closeOut file in ()
  end ;;
