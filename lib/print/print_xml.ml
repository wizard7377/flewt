
module type PRINT_XML  =
  sig
    val printSgn : unit -> unit
    val printSgnToFile : string -> string -> unit
  end;;




module PrintXML(PrintXML:sig
                           module Whnf : WHNF
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module Names : NAMES
                           module Formatter' : FORMATTER
                         end) : PRINT_XML =
  struct
    module Formatter = Formatter'
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 s n = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (((^) "\"" Int.toString n) ^ "\"")
    let rec sexp fmts = F.Hbox [F.HVbox fmts]
    let rec fmtCon __0__ __1__ =
      match (__0__, __1__) with
      | (__G, BVar n) ->
          let Dec (Some n, _) = I.ctxDec (__G, n) in
          sexp [Str (("<Var name = \"" ^ n) ^ "\"/>")]
      | (__G, Const cid) ->
          sexp
            [Str "<Const name=\"";
            Str (I.conDecName (I.sgnLookup cid));
            Str "\"/>"]
      | (__G, Def cid) ->
          sexp [Str "<Def>"; F.Break; Integer cid; Str "</Def>"]
      | (__G, FgnConst (csid, condec)) -> sexp [Str "FngConst"]
    let rec fmtUni =
      function | I.Type -> Str "<Type/>" | I.Kind -> Str "<Kind/>"
    let rec fmtExpW __2__ __3__ =
      match (__2__, __3__) with
      | (__G, (Uni (__L), s)) ->
          sexp [Str "<Uni>"; F.Break; fmtUni __L; Str "</Uni>"]
      | (__G, (Pi (((Dec (_, __V1) as D), __P), __V2), s)) ->
          (((match __P with
             | I.Maybe ->
                 let __D' = Names.decLUName (__G, __D) in
                 let __G' = I.Decl (__G, __D') in
                 ((sexp
                     (([Str "<Pi>";
                       F.Break;
                       fmtDec (__G, (__D', s));
                       F.Break;
                       fmtExp (__G', (__V2, (I.dot1 s)));
                       Str "</Pi>"])
                     (* Str "tw*maybe", F.Break, *)))
                   (* could sometimes be EName *))
             | I.No ->
                 let __G' = I.Decl (__G, __D) in
                 sexp
                   (([Str "<Arrow>";
                     F.Break;
                     fmtDec' (__G, (__D, s));
                     F.Break;
                     fmtExp (__G', (__V2, (I.dot1 s)));
                     Str "</Arrow>"])
                   (* Str "tw*no", F.Break,*))))
          (* if Pi is dependent but anonymous, invent name here *))
      | (__G, (Root (__H, __S), s)) ->
          (match fmtSpine (__G, (__S, s)) with
           | NONE -> fmtCon (__G, __H)
           | Some fmts ->
               F.HVbox
                 [Str "<App>";
                 fmtCon (__G, __H);
                 F.Break;
                 sexp fmts;
                 Str "</App>"])
      | (__G, (Lam (__D, __U), s)) ->
          let __D' = Names.decLUName (__G, __D) in
          let __G' = I.Decl (__G, __D') in
          sexp
            [Str "<Lam>";
            F.Break;
            fmtDec (__G, (__D', s));
            F.Break;
            fmtExp (__G', (__U, (I.dot1 s)));
            Str "</Lam>"]
      | (__G, (FgnExp (csid, __F), s)) -> sexp [Str "FgnExp"]
    let rec fmtExp (__G) (__U, s) = fmtExpW (__G, (Whnf.whnf (__U, s)))
    let rec fmtSpine __4__ __5__ =
      match (__4__, __5__) with
      | (__G, (I.Nil, _)) -> NONE
      | (__G, (SClo (__S, s'), s)) -> fmtSpine (__G, (__S, (I.comp (s', s))))
      | (__G, (App (__U, __S), s)) ->
          (match fmtSpine (__G, (__S, s)) with
           | NONE -> Some [fmtExp (__G, (__U, s))]
           | Some fmts -> Some ([fmtExp (__G, (__U, s)); F.Break] @ fmts))
    let rec fmtDec __6__ __7__ =
      match (__6__, __7__) with
      | (__G, (Dec (NONE, __V), s)) ->
          sexp [Str "<Dec>"; F.Break; fmtExp (__G, (__V, s)); Str "</Dec>"]
      | (__G, (Dec (Some x, __V), s)) ->
          sexp
            [Str "<Dec name =";
            Name x;
            Str ">";
            F.Break;
            fmtExp (__G, (__V, s));
            Str "</Dec>"]
    let rec fmtDec' __8__ __9__ =
      match (__8__, __9__) with
      | (__G, (Dec (NONE, __V), s)) -> sexp [fmtExp (__G, (__V, s))]
      | (__G, (Dec (Some x, __V), s)) -> sexp [fmtExp (__G, (__V, s))]
    let rec fmtConDec =
      function
      | ConDec (name, parent, imp, _, __V, __L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Condec name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L;
            Str "</Condec>"]
      | SkoDec (name, parent, imp, __V, __L) ->
          Str (("<! Skipping Skolem constant " ^ name) ^ ">")
      | ConDef (name, parent, imp, __U, __V, __L, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Condef name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (__U, I.id));
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L;
            Str "</Condef>"]
      | AbbrevDef (name, parent, imp, __U, __V, __L) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [Str "<Abbrevdef name=";
            Name name;
            Str ">";
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (__U, I.id));
            F.Break;
            fmtExp (I.Null, (__V, I.id));
            F.Break;
            fmtUni __L;
            Str "</Abbrevdef>"]
      | BlockDec (name, _, _, _) ->
          Str (("<! Skipping Skolem constant " ^ name) ^ ">")
    let rec fmtEqn (Eqn (__G, __U1, __U2)) =
      sexp
        [Str "<Equation>";
        F.Break;
        fmtExp (__G, (__U1, I.id));
        F.Break;
        fmtExp (__G, (__U2, I.id));
        Str "</Equation>"](* print context?? *)
    let rec fmtEqnName (Eqn (__G, __U1, __U2)) =
      fmtEqn (I.Eqn ((Names.ctxLUName __G), __U1, __U2))
    let rec formatDec (__G) (__D) = fmtDec (__G, (__D, I.id))
    let rec formatExp (__G) (__U) = fmtExp (__G, (__U, I.id))
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
    let rec printSgnToFile path filename =
      let file = TextIO.openOut (path ^ filename) in
      let _ =
        TextIO.output
          (file,
            "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- nsgmls ex.xml -->\n<!DOCTYPE Signature SYSTEM \"lf.dtd\">\n<Signature>") in
      let _ =
        IntSyn.sgnApp
          (fun cid ->
             TextIO.output
               (file,
                 (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
             TextIO.output (file, "\n")) in
      let _ = TextIO.output (file, "</Signature>") in
      let _ = TextIO.closeOut file in ()
  end ;;
