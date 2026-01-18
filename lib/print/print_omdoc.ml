
(* Printing Signatures to OMDoc*)
(* Author: Florian Rabe *)
module type PRINT_OMDOC  =
  sig
    (* printSgn F n exports the current signature as an OMDoc document to the file with path F. If n is true, all constant and variable names are replaced to guarantee uniqueness of names. Otherwise, the user has to make sure that no overloading is used. *)
    val printSgn : string -> bool -> unit
    (* printConst c prints the OMDoc fragment (without name safety) for the constant with cid c. *)
    val printConst : IntSyn.cid -> string
  end;;




(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Florian Rabe *)
module PrintOMDoc(PrintOMDoc:sig
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
                             end) : PRINT_OMDOC =
  struct
    (*! structure IntSyn = IntSyn' !*)
    module Formatter = Formatter'
    (* Shorthands *)
    module I = IntSyn
    let indent = ref 0
    let tabstring = "   "
    let rec tabs n = if n <= 0 then "" else (^) tabstring tabs (n - 1)
    let rec ind_reset () = indent := 0
    let rec ind n = ((!) ((:=) indent) indent) + n
    let rec unind n = ((!) ((:=) indent) indent) - n
    let rec nl_ind () =
      ((!) ((:=) indent) indent) + 1; (^) "\n" tabs (!indent)
    let rec nl_unind () =
      ((!) ((:=) indent) indent) - 1; (^) "\n" tabs (!indent)
    let rec nl () = (^) "\n" tabs (!indent)
    let rec escape s =
      let rec escapelist =
        function
        | nil -> nil
        | '&'::rest -> (String.explode "&amp;") @ (escapelist rest)
        | '<'::rest -> (String.explode "&lt;") @ (escapelist rest)
        | '>'::rest -> (String.explode "&gt;") @ (escapelist rest)
        | c::rest -> c :: (escapelist rest) in
      String.implode (escapelist (String.explode s))
    let namesafe = ref true__
    let rec replace c =
      if (Char.isAlphaNum c) || (Char.contains ":_-." c)
      then String.str c
      else "_"
    let rec Name cid =
      let n = I.conDecName (I.sgnLookup cid) in
      let name = String.translate replace n in
      let start =
        if
          (Char.isAlpha (String.sub (name, 0))) ||
            ((String.sub (name, 0)) = '_')
        then ""
        else "_" in
      if !namesafe then ((start ^ name) ^ "__c") ^ (Int.toString cid) else n
    let rec VarName (x, n) =
      let name = String.translate replace n in
      let start =
        if
          (Char.isAlpha (String.sub (name, 0))) ||
            ((String.sub (name, 0)) = '_')
        then ""
        else "_" in
      if !namesafe then ((start ^ name) ^ "__v") ^ (Int.toString x) else n
    let rec Str s = s
    let rec sexp l = String.concat l
    let rec spineLength =
      function
      | I.Nil -> 0
      | SClo (S, _) -> spineLength S
      | App (_, S) -> 1 + (spineLength S)
    let rec fmtCon =
      function
      | (G, BVar x) ->
          let Dec (SOME n, _) = I.ctxDec (G, x) in
          sexp
            [Str
               (((^) "<om:OMV name=\"" VarName
                   ((((I.ctxLength G) - x) + 1), n))
                  ^ "\"/>")]
      | (G, Const cid) ->
          sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
      | (G, Def cid) ->
          sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
      | (G, FgnConst (csid, condec)) -> sexp [Str "FgnConst"]
    let rec fmtUni =
      function
      | I.Type -> Str "<om:OMS cd=\"twelf\" name=\"type\"/>"
      | I.Kind -> Str "<om:OMS cd=\"twelf\" name=\"kind\"/>"
    let rec fmtExpW =
      function
      | (G, (Uni (L), s), _) -> sexp [fmtUni L]
      | (G, (Pi (((Dec (_, V1) as D), P), V2), s), imp) ->
          (match P with
           | I.Maybe ->
               let Dec (SOME name, V1') as D' = Names.decLUName (G, D) in
               let G' = I.Decl (G, D') in
               let _ = ind 1 in
               let fmtBody =
                 fmtExp (G', (V2, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
               let _ = ind 1 in
               let fmtType = fmtExp (G, (V1', s), 0) in
               let _ = unind 2 in
               let pi = if imp > 0 then "implicit_Pi" else "Pi" in
               let id = VarName ((I.ctxLength G'), name) in
               fmtBinder (pi, name, id, fmtType, fmtBody)
           | I.No ->
               let G' = I.Decl (G, D) in
               sexp
                 [Str "<om:OMA>";
                 nl_ind ();
                 Str "<om:OMS cd=\"twelf\" name=\"arrow\"/>";
                 nl ();
                 fmtExp (G, (V1, s), 0);
                 nl ();
                 fmtExp (G', (V2, (I.dot1 s)), 0);
                 nl_unind ();
                 Str "</om:OMA>"])
      | (G, (Root (H, S), s), _) ->
          let l = spineLength S in
          let out = ref "" in
          let _ =
            if l = 0
            then (^) ((!) ((:=) out) out) fmtCon (G, H)
            else
              (let _ = (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind () in
               let (test, cid) =
                 match H with
                 | Const c -> (true__, c)
                 | Skonst c -> (true__, c)
                 | Def c -> (true__, c)
                 | NSDef c -> (true__, c)
                 | _ -> (false__, 0) in
               let imp = IntSyn.conDecImp (IntSyn.sgnLookup cid) in
               let (test, args) =
                 if test
                 then
                   match Names.getFixity cid with
                   | Infix (_, _) -> (true__, (imp + 2))
                   | _ -> (false__, 0)
                 else (false__, 0) in
               let _ =
                 if test && (l > args)
                 then (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind ()
                 else () in
               ((^) ((^) ((!) ((:=) out) out) fmtCon (G, H)) fmtSpine
                  (G, (S, s), args))
                 ^ "</om:OMA>") in
          !out
      | (G, (Lam (D, U), s), imp) ->
          let Dec (SOME name, V) as D' = Names.decLUName (G, D) in
          let G' = I.Decl (G, D') in
          let _ = ind 1 in
          let fmtBody =
            fmtExp (G', (U, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
          let _ = ind 1 in
          let fmtType = fmtExp (G, (V, s), 0) in
          let _ = unind 2 in
          let lam = if imp > 0 then "implicit_lambda" else "lambda" in
          let id = VarName ((I.ctxLength G'), name) in
          fmtBinder (lam, name, id, fmtType, fmtBody)
      | (G, (FgnExp (csid, F), s), 0) -> sexp [Str "FgnExp"]
    let rec fmtExp (G, (U, s), imp) = fmtExpW (G, (Whnf.whnf (U, s)), imp)
    let rec fmtSpine =
      function
      | (G, (I.Nil, _), _) -> nl_unind ()
      | (G, (SClo (S, s'), s), args) ->
          fmtSpine (G, (S, (I.comp (s', s))), args)
      | (G, (App (U, S), s), args) ->
          let out = ref ((^) (nl ()) fmtExp (G, (U, s), 0)) in
          let _ =
            if (args = 1) && ((spineLength S) > 0)
            then ((^) ((!) ((:=) out) out) nl_unind ()) ^ "</om:OMA>"
            else () in
          (^) (!out) fmtSpine (G, (S, s), (args - 1))
    let rec fmtExpTop (G, (U, s), imp) =
      sexp
        [Str "<om:OMOBJ>";
        nl_ind ();
        fmtExp (G, (U, s), imp);
        nl_unind ();
        Str "</om:OMOBJ>"]
    let rec fmtBinder (binder, varname, varid, typ, body) =
      ((^) (((^) (((^) (((((^) (((^) (((^) (((^) ((((^) (((^) (((((^) "<om:OMBIND>"
                                                                    nl_ind ())
                                                                   ^
                                                                   "<om:OMS cd=\"twelf\" name=\"")
                                                                  ^ binder)
                                                                 ^ "\"/>")
                                                            nl ())
                                                           ^
                                                           "<om:OMBVAR><om:OMATTR>")
                                                      nl_ind ())
                                                     ^
                                                     (if !namesafe
                                                      then
                                                        ((((("<om:OMATP><om:OMS cd=\"omdoc\" name=\"notation\"/><om:OMFOREIGN encoding=\"application/omdoc+xml\">"
                                                               ^
                                                               "<presentation for=\"#")
                                                              ^ varid)
                                                             ^
                                                             "\"><use format=\"twelf\">")
                                                            ^ varname)
                                                           ^
                                                           "</use></presentation>")
                                                          ^
                                                          "</om:OMFOREIGN></om:OMATP>"
                                                      else ""))
                                                    ^ "<om:OMATP>")
                                               nl ())
                                              ^
                                              "<om:OMS cd=\"twelf\" name=\"oftype\"/>")
                                         nl ())
                                        ^ typ)
                                   nl ())
                                  ^ "</om:OMATP>")
                             nl ())
                            ^ "<om:OMV name=\"")
                           ^ varid)
                          ^ "\"/>")
                     nl_unind ())
                    ^ "</om:OMATTR></om:OMBVAR>")
               nl ())
              ^ body)
         nl_unind ())
        ^ "</om:OMBIND>"
    let rec fmtSymbol (name, V, imp) =
      ((^) (((^) ((^) ((^) (((^) (("<symbol name=\"" ^ name) ^ "\">") nl_ind
                               ())
                              ^ "<type system=\"twelf\">")
                         nl_ind ())
                    fmtExpTop (I.Null, (V, I.id), imp))
               nl_unind ())
              ^ "</type>")
         nl_unind ())
        ^ "</symbol>"
    let rec fmtDefinition (name, U, imp) =
      ((^) ((^) ((^) (((("<definition xml:id=\"" ^ name) ^ ".def\" for=\"#")
                         ^ name)
                        ^ "\">")
                   nl_ind ())
              fmtExpTop (I.Null, (U, I.id), imp))
         nl_unind ())
        ^ "</definition>"
    let rec fmtPresentation cid =
      let imp = I.conDecImp (I.sgnLookup cid) in
      let fixity = Names.getFixity cid in
      let fixString =
        (" fixity=\"" ^
           (match fixity with
            | Names.Fixity.Nonfix -> "prefix"
            | Infix (prec, assoc) ->
                (match assoc with
                 | Names.Fixity.Left -> "infixl"
                 | Names.Fixity.Right -> "infixr"
                 | Names.Fixity.None -> "infix")
            | Prefix prec -> "prefix"
            | Postfix prec -> "postfix"))
          ^ "\"" in
      let precString =
        (" precedence=\"" ^ (Int.toString (Names.Fixity.precToIntAsc fixity)))
          ^ "\"" in
      let bracString = " bracket-style=\"lisp\" lbrack=\"(\" rbrack=\")\"" in
      let sepString = " separator=\" \"" in
      let implicitString = (" implicit=\"" ^ (Int.toString imp)) ^ "\"" in
      let useString1 = "<use format=\"twelf\"" in
      let useString2 =
        (">" ^ (escape (I.conDecName (I.sgnLookup cid)))) ^ "</use>" in
      let presString1 = ("<presentation for=\"#" ^ (Name cid)) ^ "\"" in
      let presString2 = "</presentation>" in
      ((^) ((((^) ((((((((((^) (((^) ((((^) (presString1 ^ ">") nl_ind ()) ^
                                         useString1)
                                        ^ useString2)
                                   nl_unind ())
                                  ^ presString2)
                             nl ())
                            ^ presString1)
                           ^ " role=\"applied\"")
                          ^ fixString)
                         ^ precString)
                        ^ bracString)
                       ^ sepString)
                      ^ implicitString)
                     ^ ">")
                nl_ind ())
               ^ useString1)
              ^ useString2)
         nl_unind ())
        ^ presString2
    let rec fmtFixity cid =
      let fixity = Names.getFixity cid in
      let name = I.conDecName (I.sgnLookup cid) in
      if fixity = Names.Fixity.Nonfix
      then ""
      else
        ((^) (((((((^) ((((nl ()) ^ "<private for=\"#") ^ (Name cid)) ^ "\">")
                     nl_ind ())
                    ^ "<data format=\"twelf\"><![CDATA[")
                   ^ (Names.Fixity.toString fixity))
                  ^ " ")
                 ^ name)
                ^ ".]]></data>")
           nl_unind ())
          ^ "</private>"
    let rec fmtConDec =
      function
      | (cid, ConDec (name, parent, imp, _, V, L)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in fmtSymbol (name, V, imp)
      | (_, SkoDec (name, parent, imp, V, L)) ->
          Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->")
      | (cid, ConDef (name, parent, imp, U, V, L, _)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in
          (^) ((^) (fmtSymbol (name, V, imp)) nl ()) fmtDefinition
            (name, U, imp)
      | (cid, AbbrevDef (name, parent, imp, U, V, L)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in
          (^) ((^) (fmtSymbol (name, V, imp)) nl ()) fmtDefinition
            (name, U, imp)
      | (_, BlockDec (name, _, _, _)) ->
          Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->")
    (* The Formatter isn't really helpful for OMDoc output. So the basic functions are reimplemented here.
     indent : current indentatioin width
     nl_ind()() : newline and indent
     nl_unind()() : newline and unindent
     nl() : newline (with current indentation) *)
    (* If namesafe is true during printing, the output is guaranteed to be namesafe (no duplicate names).
    But it doesn't look good. If the user knows that are no overloaded constants, namesafe can be set to false. *)
    (* XML start characters: ":" | "_" | [A-Z] | [a-z], further characters: "-" | "." | [0-9] *)
    (* x must be the number of the varialbe in left ro right order in the context *)
    (* Some original Formatter functions replaced with trivial functions. *)
    (* val Str  = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Integer (n) = ("\"" ^ Int.toString n ^ "\"") *)
    (* fun sexp (fmts) = F.Hbox [F.HVbox fmts] *)
    (* This is probably defined elsewhere, too. It's needed to check how many arguments there will be in an om:OMA element *)
    (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
    (* FIX -cs Fri Jan 28 17:45:35 2005*)
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
    (* temporary indentation *)
    (* no arguments *)
    (* an application *)
    (* If there are more than two explicit arguments to an infix operator,
                   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
                   In this case, the output will not be in normal form. *)
    (* print constant and arguments,
           args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *)
    (* temporary indentation *)
    (* FIX -cs Fri Jan 28 17:45:43 2005 *)
    (* I.EClo, I.Redex, I.EVar not possible *)
    (* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *)
    (* print first argument, 0 is dummy value *)
    (* close application if args reaches 0 *)
    (* print remaining arguments *)
    (* top-level and shared OMDoc output, used in fmtConDec *)
    (* In the presentation information for variables can be omitted since it's their name anyway *)
    (* case identified by @precedence = Names.Fixity.minPrefInt *)
    (* fixity string attached to omdoc file in private element (no escaping, fixity string cannot contain ]]>) *)
    (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
    (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
    let rec formatExp (G, U, imp) = fmtExp (G, (U, I.id), imp)
    (*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)
    let rec formatConDec condec = fmtConDec condec
    (* fun expToString (G, U) = F.makestring_fmt (formatExp (G, U, 0)) *)
    let rec conDecToString condec = formatConDec condec
    let rec fmtConst cid =
      (^) ((^) ((formatConDec (cid, (IntSyn.sgnLookup cid))) ^ "\n")
             fmtPresentation cid)
        fmtFixity cid
    let rec printConst cid = namesafe := false__; fmtConst cid
    let rec printSgn filename ns =
      let _ = namesafe := ns in
      let _ = ind_reset () in
      let file = TextIO.openOut filename in
      let OMDocPrefix =
        ((((((((("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
                   "<!DOCTYPE omdoc PUBLIC \"-//OMDoc//DTD OMDoc V1.2//EN\" ")
                  ^ "\"../../dtd/omdoc.dtd\">\n")
                 ^ "<omdoc xml:id=\"")
                ^ filename)
               ^ "\" ")
              ^ "xmlns=\"http://www.mathweb.org/omdoc\" ")
             ^ "xmlns:om=\"http://www.openmath.org/OpenMath\" ")
            ^ "version=\"1.2\">\n\n")
        (* "\"https://svn.mathweb.org/repos/mathweb.org/branches/omdoc-1.2/dtd/omdoc.dtd\">\n" ^ *)) in
      let _ =
        TextIO.output
          (file, (OMDocPrefix ^ "<theory xml:id=\"global\">\n\n")) in
      let _ =
        IntSyn.sgnApp
          (function
           | cid ->
               (TextIO.output (file, (fmtConst cid));
                TextIO.output (file, "\n\n"))) in
      let _ = TextIO.output (file, "</theory>\n\n</omdoc>") in
      let _ = TextIO.closeOut file in ()
  end ;;
