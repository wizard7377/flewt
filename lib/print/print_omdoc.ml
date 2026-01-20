
module type PRINT_OMDOC  =
  sig
    val printSgn : string -> bool -> unit
    val printConst : IntSyn.cid -> string
  end;;




module PrintOMDoc(PrintOMDoc:sig
                               module Whnf : WHNF
                               module Abstract : ABSTRACT
                               module Constraints : CONSTRAINTS
                               module Names : NAMES
                               module Formatter' : FORMATTER
                             end) : PRINT_OMDOC =
  struct
    module Formatter = Formatter'
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
    let namesafe = ref true
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
    let rec VarName x n =
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
      | SClo (__S, _) -> spineLength __S
      | App (_, __S) -> 1 + (spineLength __S)
    let rec fmtCon __0__ __1__ =
      match (__0__, __1__) with
      | (__G, BVar x) ->
          let Dec (Some n, _) = I.ctxDec (__G, x) in
          sexp
            [Str
               (((^) "<om:OMV name=\"" VarName
                   ((((I.ctxLength __G) - x) + 1), n))
                  ^ "\"/>")]
      | (__G, Const cid) ->
          sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
      | (__G, Def cid) ->
          sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
      | (__G, FgnConst (csid, condec)) -> sexp [Str "FgnConst"]
    let rec fmtUni =
      function
      | I.Type -> Str "<om:OMS cd=\"twelf\" name=\"type\"/>"
      | I.Kind -> Str "<om:OMS cd=\"twelf\" name=\"kind\"/>"
    let rec fmtExpW __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, (Uni (__L), s), _) -> sexp [fmtUni __L]
      | (__G, (Pi (((Dec (_, __V1) as D), __P), __V2), s), imp) ->
          (((match __P with
             | I.Maybe ->
                 let Dec (Some name, V1') as D' = Names.decLUName (__G, __D) in
                 let __G' = I.Decl (__G, __D') in
                 let _ = ind 1 in
                 let fmtBody =
                   fmtExp
                     (__G', (__V2, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
                 let _ = ind 1 in
                 let fmtType = fmtExp (__G, (V1', s), 0) in
                 let _ = unind 2 in
                 let pi = if imp > 0 then "implicit_Pi" else "Pi" in
                 let id = VarName ((I.ctxLength __G'), name) in
                 ((fmtBinder (pi, name, id, fmtType, fmtBody))
                   (* could sometimes be EName *)(* temporary indentation *))
             | I.No ->
                 let __G' = I.Decl (__G, __D) in
                 sexp
                   [Str "<om:OMA>";
                   nl_ind ();
                   Str "<om:OMS cd=\"twelf\" name=\"arrow\"/>";
                   nl ();
                   fmtExp (__G, (__V1, s), 0);
                   nl ();
                   fmtExp (__G', (__V2, (I.dot1 s)), 0);
                   nl_unind ();
                   Str "</om:OMA>"]))
          (* if Pi is dependent but anonymous, invent name here *))
      | (__G, (Root (__H, __S), s), _) ->
          let l = spineLength __S in
          let out = ref "" in
          let _ =
            ((if l = 0
              then (^) ((!) ((:=) out) out) fmtCon (__G, __H)
              else
                (let _ = (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind () in
                 let (test, cid) =
                   match __H with
                   | Const c -> (true, c)
                   | Skonst c -> (true, c)
                   | Def c -> (true, c)
                   | NSDef c -> (true, c)
                   | _ -> (false, 0) in
                 let imp = IntSyn.conDecImp (IntSyn.sgnLookup cid) in
                 let (test, args) =
                   if test
                   then
                     match Names.getFixity cid with
                     | Infix (_, _) -> (true, (imp + 2))
                     | _ -> (false, 0)
                   else (false, 0) in
                 let _ =
                   if test && (l > args)
                   then (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind ()
                   else () in
                 ((((^) ((^) ((!) ((:=) out) out) fmtCon (__G, __H)) fmtSpine
                      (__G, (__S, s), args))
                     ^ "</om:OMA>")
                   (* an application *)(* If there are more than two explicit arguments to an infix operator,
                   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
                   In this case, the output will not be in normal form. *)
                   (* print constant and arguments,
           args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *))))
            (* no arguments *)) in
          !out
      | (__G, (Lam (__D, __U), s), imp) ->
          let Dec (Some name, __V) as D' = Names.decLUName (__G, __D) in
          let __G' = I.Decl (__G, __D') in
          let _ = ind 1 in
          let fmtBody =
            fmtExp (__G', (__U, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
          let _ = ind 1 in
          let fmtType = fmtExp (__G, (__V, s), 0) in
          let _ = unind 2 in
          let lam = if imp > 0 then "implicit_lambda" else "lambda" in
          let id = VarName ((I.ctxLength __G'), name) in
          ((fmtBinder (lam, name, id, fmtType, fmtBody))
            (* temporary indentation *))
      | (__G, (FgnExp (csid, __F), s), 0) -> sexp [Str "FgnExp"]
    let rec fmtExp (__G) (__U, s) imp =
      fmtExpW (__G, (Whnf.whnf (__U, s)), imp)
    let rec fmtSpine __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (__G, (I.Nil, _), _) -> nl_unind ()
      | (__G, (SClo (__S, s'), s), args) ->
          fmtSpine (__G, (__S, (I.comp (s', s))), args)
      | (__G, (App (__U, __S), s), args) ->
          let out = ref ((^) (nl ()) fmtExp (__G, (__U, s), 0)) in
          let _ =
            if (args = 1) && ((spineLength __S) > 0)
            then ((^) ((!) ((:=) out) out) nl_unind ()) ^ "</om:OMA>"
            else () in
          (((^) (!out) fmtSpine (__G, (__S, s), (args - 1)))
            (* print first argument, 0 is dummy value *)
            (* close application if args reaches 0 *)
            (* print remaining arguments *))
    let rec fmtExpTop (__G) (__U, s) imp =
      sexp
        [Str "<om:OMOBJ>";
        nl_ind ();
        fmtExp (__G, (__U, s), imp);
        nl_unind ();
        Str "</om:OMOBJ>"]
    let rec fmtBinder binder varname varid typ body =
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
                                                     ((if !namesafe
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
                                                       else "")
                                                     (* In the presentation information for variables can be omitted since it's their name anyway *)))
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
    let rec fmtSymbol name (__V) imp =
      ((^) (((^) ((^) ((^) (((^) (("<symbol name=\"" ^ name) ^ "\">") nl_ind
                               ())
                              ^ "<type system=\"twelf\">")
                         nl_ind ())
                    fmtExpTop (I.Null, (__V, I.id), imp))
               nl_unind ())
              ^ "</type>")
         nl_unind ())
        ^ "</symbol>"
    let rec fmtDefinition name (__U) imp =
      ((^) ((^) ((^) (((("<definition xml:id=\"" ^ name) ^ ".def\" for=\"#")
                         ^ name)
                        ^ "\">")
                   nl_ind ())
              fmtExpTop (I.Null, (__U, I.id), imp))
         nl_unind ())
        ^ "</definition>"
    let rec fmtPresentation cid =
      let imp = I.conDecImp (I.sgnLookup cid) in
      let fixity = Names.getFixity cid in
      let fixString =
        (" fixity=\"" ^
           ((match fixity with
             | Names.Fixity.Nonfix -> "prefix"
             | Infix (prec, assoc) ->
                 (match assoc with
                  | Names.Fixity.Left -> "infixl"
                  | Names.Fixity.Right -> "infixr"
                  | Names.Fixity.None -> "infix")
             | Prefix prec -> "prefix"
             | Postfix prec -> "postfix")
           (* case identified by @precedence = Names.Fixity.minPrefInt *)))
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
    let rec fmtConDec __8__ __9__ =
      match (__8__, __9__) with
      | (cid, ConDec (name, parent, imp, _, __V, __L)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in fmtSymbol (name, __V, imp)
      | (_, SkoDec (name, parent, imp, __V, __L)) ->
          Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->")
      | (cid, ConDef (name, parent, imp, __U, __V, __L, _)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in
          (^) ((^) (fmtSymbol (name, __V, imp)) nl ()) fmtDefinition
            (name, __U, imp)
      | (cid, AbbrevDef (name, parent, imp, __U, __V, __L)) ->
          let _ = Names.varReset IntSyn.Null in
          let name = Name cid in
          (^) ((^) (fmtSymbol (name, __V, imp)) nl ()) fmtDefinition
            (name, __U, imp)
      | (_, BlockDec (name, _, _, _)) ->
          Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->")
    let rec formatExp (__G) (__U) imp = fmtExp (__G, (__U, I.id), imp)
    let rec formatConDec condec = fmtConDec condec
    let rec conDecToString condec = formatConDec condec
    let rec fmtConst cid =
      (^) ((^) ((formatConDec (cid, (IntSyn.sgnLookup cid))) ^ "\n")
             fmtPresentation cid)
        fmtFixity cid
    let rec printConst cid = namesafe := false; fmtConst cid
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
          (fun cid ->
             TextIO.output (file, (fmtConst cid));
             TextIO.output (file, "\n\n")) in
      let _ = TextIO.output (file, "</theory>\n\n</omdoc>") in
      let _ = TextIO.closeOut file in ()
  end ;;
