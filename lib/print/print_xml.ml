module type PRINT_XML  =
  sig
    val printSgn : unit -> unit
    val printSgnToFile : string -> string -> unit
  end


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
    let rec Str0 (s, n) = F.String0 n s
    let rec Name x = F.String (("\"" ^ x) ^ "\"")
    let rec Integer n = F.String (((^) "\"" Int.toString n) ^ "\"")
    let rec sexp fmts = F.Hbox [F.HVbox fmts]
    let rec fmtCon =
      begin function
      | (g_, BVar n) ->
          let Dec (Some n, _) = I.ctxDec (g_, n) in
          sexp [Str (("<Var name = \"" ^ n) ^ "\"/>")]
      | (g_, Const cid) ->
          sexp
            [Str "<Const name=\"";
            Str (I.conDecName (I.sgnLookup cid));
            Str "\"/>"]
      | (g_, Def cid) ->
          sexp [Str "<Def>"; F.Break; Integer cid; Str "</Def>"]
      | (g_, FgnConst (csid, condec)) -> sexp [Str "FngConst"] end
    let rec fmtUni =
      begin function | I.Type -> Str "<Type/>" | I.Kind -> Str "<Kind/>" end
  let rec fmtExpW =
    begin function
    | (g_, (Uni (l_), s)) ->
        sexp [Str "<Uni>"; F.Break; fmtUni l_; Str "</Uni>"]
    | (g_, (Pi (((Dec (_, v1_) as d_), p_), v2_), s)) ->
        (((begin match p_ with
           | I.Maybe ->
               let d'_ = Names.decLUName (g_, d_) in
               let g'_ = I.Decl (g_, d'_) in
               ((sexp
                   (([Str "<Pi>";
                     F.Break;
                     fmtDec (g_, (d'_, s));
                     F.Break;
                     fmtExp (g'_, (v2_, (I.dot1 s)));
                     Str "</Pi>"])
                   (* Str "tw*maybe", F.Break, *)))
                 (* could sometimes be EName *))
           | I.No ->
               let g'_ = I.Decl (g_, d_) in
               sexp
                 (([Str "<Arrow>";
                   F.Break;
                   fmtDec' (g_, (d_, s));
                   F.Break;
                   fmtExp (g'_, (v2_, (I.dot1 s)));
                   Str "</Arrow>"])
                 (* Str "tw*no", F.Break,*)) end))
    (* if Pi is dependent but anonymous, invent name here *))
    | (g_, (Root (h_, s_), s)) ->
        (begin match fmtSpine (g_, (s_, s)) with
         | None -> fmtCon (g_, h_)
         | Some fmts ->
             F.HVbox
               [Str "<App>";
               fmtCon (g_, h_);
               F.Break;
               sexp fmts;
               Str "</App>"] end)
    | (g_, (Lam (d_, u_), s)) ->
        let d'_ = Names.decLUName (g_, d_) in
        let g'_ = I.Decl (g_, d'_) in
        sexp
          [Str "<Lam>";
          F.Break;
          fmtDec (g_, (d'_, s));
          F.Break;
          fmtExp (g'_, (u_, (I.dot1 s)));
          Str "</Lam>"]
    | (g_, (FgnExp (csid, f_), s)) -> sexp [Str "FgnExp"] end
let rec fmtExp (g_, (u_, s)) = fmtExpW (g_, (Whnf.whnf (u_, s)))
let rec fmtSpine =
  begin function
  | (g_, (I.Nil, _)) -> None
  | (g_, (SClo (s_, s'), s)) -> fmtSpine (g_, (s_, (I.comp (s', s))))
  | (g_, (App (u_, s_), s)) ->
      (begin match fmtSpine (g_, (s_, s)) with
       | None -> Some [fmtExp (g_, (u_, s))]
       | Some fmts -> Some ([fmtExp (g_, (u_, s)); F.Break] @ fmts) end) end
let rec fmtDec =
  begin function
  | (g_, (Dec (None, v_), s)) ->
      sexp [Str "<Dec>"; F.Break; fmtExp (g_, (v_, s)); Str "</Dec>"]
  | (g_, (Dec (Some x, v_), s)) ->
      sexp
        [Str "<Dec name =";
        Name x;
        Str ">";
        F.Break;
        fmtExp (g_, (v_, s));
        Str "</Dec>"] end
let rec fmtDec' =
  begin function
  | (g_, (Dec (None, v_), s)) -> sexp [fmtExp (g_, (v_, s))]
  | (g_, (Dec (Some x, v_), s)) -> sexp [fmtExp (g_, (v_, s))] end
let rec fmtConDec =
  begin function
  | ConDec (name, parent, imp, _, v_, l_) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "<Condec name=";
        Name name;
        F.Break;
        Str "implicit=";
        Integer imp;
        Str ">";
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_;
        Str "</Condec>"]
  | SkoDec (name, parent, imp, v_, l_) ->
      Str (("<! Skipping Skolem constant " ^ name) ^ ">")
  | ConDef (name, parent, imp, u_, v_, l_, _) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "<Condef name=";
        Name name;
        F.Break;
        Str "implicit=";
        Integer imp;
        Str ">";
        F.Break;
        fmtExp (I.Null, (u_, I.id));
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_;
        Str "</Condef>"]
  | AbbrevDef (name, parent, imp, u_, v_, l_) ->
      let _ = Names.varReset IntSyn.Null in
      sexp
        [Str "<Abbrevdef name=";
        Name name;
        Str ">";
        F.Break;
        Integer imp;
        F.Break;
        fmtExp (I.Null, (u_, I.id));
        F.Break;
        fmtExp (I.Null, (v_, I.id));
        F.Break;
        fmtUni l_;
        Str "</Abbrevdef>"]
  | BlockDec (name, _, _, _) ->
      Str (("<! Skipping Skolem constant " ^ name) ^ ">") end
let rec fmtEqn (Eqn (g_, u1_, u2_)) =
  sexp
    [Str "<Equation>";
    F.Break;
    fmtExp (g_, (u1_, I.id));
    F.Break;
    fmtExp (g_, (u2_, I.id));
    Str "</Equation>"](* print context?? *)
let rec fmtEqnName (Eqn (g_, u1_, u2_)) =
  fmtEqn (I.Eqn ((Names.ctxLUName g_), u1_, u2_))
let rec formatDec (g_, d_) = fmtDec (g_, (d_, I.id))
let rec formatExp (g_, u_) = fmtExp (g_, (u_, I.id))
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
let rec printSgnToFile path filename =
  let file = TextIO.openOut (path ^ filename) in
  let _ =
    TextIO.output
      (file,
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- nsgmls ex.xml -->\n<!DOCTYPE Signature SYSTEM \"lf.dtd\">\n<Signature>") in
  let _ =
    IntSyn.sgnApp
      (begin function
       | cid ->
           (begin TextIO.output
                    (file,
                      (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid))));
            TextIO.output (file, "\n") end) end) in
  let _ = TextIO.output (file, "</Signature>") in
  let _ = TextIO.closeOut file in () end
