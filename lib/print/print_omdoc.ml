module type PRINT_OMDOC  =
  sig
    val printSgn : string -> bool -> unit
    val printConst : IntSyn.cid -> string
  end


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
    let rec tabs n = if n <= 0 then begin "" end
      else begin (^) tabstring tabs (n - 1) end
  let rec ind_reset () = indent := 0
  let rec ind n = ((!) ((:=) indent) indent) + n
  let rec unind n = ((!) ((:=) indent) indent) - n
  let rec nl_ind () =
    begin ((!) ((:=) indent) indent) + 1; (^) "\n" tabs !indent end
let rec nl_unind () =
  begin ((!) ((:=) indent) indent) - 1; (^) "\n" tabs !indent end
let rec nl () = (^) "\n" tabs !indent
let rec escape s =
  let rec escapelist =
    begin function
    | [] -> []
    | '&'::rest -> (String.explode "&amp;") @ (escapelist rest)
    | '<'::rest -> (String.explode "&lt;") @ (escapelist rest)
    | '>'::rest -> (String.explode "&gt;") @ (escapelist rest)
    | c::rest -> c :: (escapelist rest) end in
String.implode (escapelist (String.explode s))
let namesafe = ref true
let rec replace c =
  if (Char.isAlphaNum c) || (Char.contains ":_-." c)
  then begin String.str c end else begin "_" end
let rec Name cid =
  let n = I.conDecName (I.sgnLookup cid) in
  let name = String.translate replace n in
  let start =
    if
      (Char.isAlpha (String.sub (name, 0))) || ((String.sub (name, 0)) = '_')
    then begin "" end else begin "_" end in
  if !namesafe then begin ((start ^ name) ^ "__c") ^ (Int.toString cid) end
    else begin n end
let rec VarName (x, n) =
  let name = String.translate replace n in
  let start =
    if
      (Char.isAlpha (String.sub (name, 0))) || ((String.sub (name, 0)) = '_')
    then begin "" end else begin "_" end in
if !namesafe then begin ((start ^ name) ^ "__v") ^ (Int.toString x) end
  else begin n end
let rec Str s = s
let rec sexp l = String.concat l
let rec spineLength =
  begin function
  | I.Nil -> 0
  | SClo (s_, _) -> spineLength s_
  | App (_, s_) -> 1 + (spineLength s_) end
let rec fmtCon =
  begin function
  | (g_, BVar x) ->
      let Dec (Some n, _) = I.ctxDec (g_, x) in
      sexp
        [Str
           (((^) "<om:OMV name=\"" VarName ((((I.ctxLength g_) - x) + 1), n))
              ^ "\"/>")]
  | (g_, Const cid) ->
      sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
  | (g_, Def cid) ->
      sexp [Str "<om:OMS cd=\"global\" name=\""; Name cid; Str "\"/>"]
  | (g_, FgnConst (csid, condec)) -> sexp [Str "FgnConst"] end
let rec fmtUni =
  begin function
  | I.Type -> Str "<om:OMS cd=\"twelf\" name=\"type\"/>"
  | I.Kind -> Str "<om:OMS cd=\"twelf\" name=\"kind\"/>" end
let rec fmtExpW =
  begin function
  | (g_, (Uni (l_), s), _) -> sexp [fmtUni l_]
  | (g_, (Pi (((Dec (_, v1_) as d_), p_), v2_), s), imp) ->
      (((begin match p_ with
         | I.Maybe ->
             let Dec (Some name, V1') as d'_ = Names.decLUName (g_, d_) in
             let g'_ = I.Decl (g_, d'_) in
             let _ = ind 1 in
             let fmtBody =
               fmtExp (g'_, (v2_, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
             let _ = ind 1 in
             let fmtType = fmtExp (g_, (V1', s), 0) in
             let _ = unind 2 in
             let pi = if imp > 0 then begin "implicit_Pi" end
               else begin "Pi" end in
             let id = VarName ((I.ctxLength g'_), name) in
             ((fmtBinder (pi, name, id, fmtType, fmtBody))
               (* could sometimes be EName *)(* temporary indentation *))
  | I.No ->
      let g'_ = I.Decl (g_, d_) in
      sexp
        [Str "<om:OMA>";
        nl_ind ();
        Str "<om:OMS cd=\"twelf\" name=\"arrow\"/>";
        nl ();
        fmtExp (g_, (v1_, s), 0);
        nl ();
        fmtExp (g'_, (v2_, (I.dot1 s)), 0);
        nl_unind ();
        Str "</om:OMA>"] end))
  (* if Pi is dependent but anonymous, invent name here *))
| (g_, (Root (h_, s_), s), _) ->
    let l = spineLength s_ in
    let out = ref "" in
    let _ =
      ((if l = 0 then begin (^) ((!) ((:=) out) out) fmtCon (g_, h_) end
      else begin
        (let _ = (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind () in
         let (test, cid) =
           begin match h_ with
           | Const c -> (true, c)
           | Skonst c -> (true, c)
           | Def c -> (true, c)
           | NSDef c -> (true, c)
           | _ -> (false, 0) end in
         let imp = IntSyn.conDecImp (IntSyn.sgnLookup cid) in
         let (test, args) =
           if test
           then
             begin begin match Names.getFixity cid with
                   | Infix (_, _) -> (true, (imp + 2))
                   | _ -> (false, 0) end end
           else begin (false, 0) end in
      let _ =
        if test && (l > args)
        then begin (^) (((!) ((:=) out) out) ^ "<om:OMA>") nl_ind () end
        else begin () end in
    ((((^) ((^) ((!) ((:=) out) out) fmtCon (g_, h_)) fmtSpine
         (g_, (s_, s), args))
        ^ "</om:OMA>")
      (* an application *)(* If there are more than two explicit arguments to an infix operator,
                   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
                   In this case, the output will not be in normal form. *)
      (* print constant and arguments,
           args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *))) end)
(* no arguments *)) in !out
| (g_, (Lam (d_, u_), s), imp) ->
    let Dec (Some name, v_) as d'_ = Names.decLUName (g_, d_) in
    let g'_ = I.Decl (g_, d'_) in
    let _ = ind 1 in
    let fmtBody = fmtExp (g'_, (u_, (I.dot1 s)), (Int.max (0, (imp - 1)))) in
    let _ = ind 1 in
    let fmtType = fmtExp (g_, (v_, s), 0) in
    let _ = unind 2 in
    let lam = if imp > 0 then begin "implicit_lambda" end
      else begin "lambda" end in
    let id = VarName ((I.ctxLength g'_), name) in
    ((fmtBinder (lam, name, id, fmtType, fmtBody))
      (* temporary indentation *))
| (g_, (FgnExp (csid, f_), s), 0) -> sexp [Str "FgnExp"] end
let rec fmtExp (g_, (u_, s), imp) = fmtExpW (g_, (Whnf.whnf (u_, s)), imp)
let rec fmtSpine =
  begin function
  | (g_, (I.Nil, _), _) -> nl_unind ()
  | (g_, (SClo (s_, s'), s), args) ->
      fmtSpine (g_, (s_, (I.comp (s', s))), args)
  | (g_, (App (u_, s_), s), args) ->
      let out = ref ((^) (nl ()) fmtExp (g_, (u_, s), 0)) in
      let _ =
        if (args = 1) && ((spineLength s_) > 0)
        then begin ((^) ((!) ((:=) out) out) nl_unind ()) ^ "</om:OMA>" end
        else begin () end in
    (((^) !out fmtSpine (g_, (s_, s), (args - 1)))
      (* print first argument, 0 is dummy value *)(* close application if args reaches 0 *)
      (* print remaining arguments *)) end
let rec fmtExpTop (g_, (u_, s), imp) =
  sexp
    [Str "<om:OMOBJ>";
    nl_ind ();
    fmtExp (g_, (u_, s), imp);
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
                                                 ((if !namesafe
                                                   then
                                                     begin ((((("<om:OMATP><om:OMS cd=\"omdoc\" name=\"notation\"/><om:OMFOREIGN encoding=\"application/omdoc+xml\">"
                                                                  ^
                                                                  "<presentation for=\"#")
                                                                 ^ varid)
                                                                ^
                                                                "\"><use format=\"twelf\">")
                                                               ^ varname)
                                                              ^
                                                              "</use></presentation>")
                                                             ^
                                                             "</om:OMFOREIGN></om:OMATP>" end
                                                 else begin "" end)
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
  nl_unind ()) ^ "</om:OMBIND>"
let rec fmtSymbol (name, v_, imp) =
  ((^) (((^) ((^) ((^) (((^) (("<symbol name=\"" ^ name) ^ "\">") nl_ind ())
                          ^ "<type system=\"twelf\">")
                     nl_ind ())
                fmtExpTop (I.Null, (v_, I.id), imp))
           nl_unind ())
          ^ "</type>")
     nl_unind ())
    ^ "</symbol>"
let rec fmtDefinition (name, u_, imp) =
  ((^) ((^) ((^) (((("<definition xml:id=\"" ^ name) ^ ".def\" for=\"#") ^
                     name)
                    ^ "\">")
               nl_ind ())
          fmtExpTop (I.Null, (u_, I.id), imp))
     nl_unind ())
    ^ "</definition>"
let rec fmtPresentation cid =
  let imp = I.conDecImp (I.sgnLookup cid) in
  let fixity = Names.getFixity cid in
  let fixString =
    (" fixity=\"" ^
       ((begin match fixity with
         | Names.Fixity.Nonfix -> "prefix"
         | Infix (prec, assoc) ->
             (begin match assoc with
              | Names.Fixity.Left -> "infixl"
              | Names.Fixity.Right -> "infixr"
              | Names.Fixity.None -> "infix" end)
       | Prefix prec -> "prefix" | Postfix prec -> "postfix" end)
    (* case identified by @precedence = Names.Fixity.minPrefInt *)))
    ^ "\"" in
  let precString =
    (" precedence=\"" ^ (Int.toString (Names.Fixity.precToIntAsc fixity))) ^
      "\"" in
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
  if fixity = Names.Fixity.Nonfix then begin "" end
    else begin
      ((^) (((((((^) ((((nl ()) ^ "<private for=\"#") ^ (Name cid)) ^ "\">")
                   nl_ind ())
                  ^ "<data format=\"twelf\"><![CDATA[")
                 ^ (Names.Fixity.toString fixity))
                ^ " ")
               ^ name)
              ^ ".]]></data>")
         nl_unind ())
        ^ "</private>" end
let rec fmtConDec =
  begin function
  | (cid, ConDec (name, parent, imp, _, v_, l_)) ->
      let _ = Names.varReset IntSyn.Null in
      let name = Name cid in fmtSymbol (name, v_, imp)
  | (_, SkoDec (name, parent, imp, v_, l_)) ->
      Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->")
  | (cid, ConDef (name, parent, imp, u_, v_, l_, _)) ->
      let _ = Names.varReset IntSyn.Null in
      let name = Name cid in
      (^) ((^) (fmtSymbol (name, v_, imp)) nl ()) fmtDefinition
        (name, u_, imp)
  | (cid, AbbrevDef (name, parent, imp, u_, v_, l_)) ->
      let _ = Names.varReset IntSyn.Null in
      let name = Name cid in
      (^) ((^) (fmtSymbol (name, v_, imp)) nl ()) fmtDefinition
        (name, u_, imp)
  | (_, BlockDec (name, _, _, _)) ->
      Str (("<!-- Skipping Skolem constant " ^ name) ^ "-->") end
let rec formatExp (g_, u_, imp) = fmtExp (g_, (u_, I.id), imp)
let rec formatConDec condec = fmtConDec condec
let rec conDecToString condec = formatConDec condec
let rec fmtConst cid =
  (^) ((^) ((formatConDec (cid, (IntSyn.sgnLookup cid))) ^ "\n")
         fmtPresentation cid)
    fmtFixity cid
let rec printConst cid = begin namesafe := false; fmtConst cid end
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
    TextIO.output (file, (OMDocPrefix ^ "<theory xml:id=\"global\">\n\n")) in
  let _ =
    IntSyn.sgnApp
      (begin function
       | cid ->
           (begin TextIO.output (file, (fmtConst cid));
            TextIO.output (file, "\n\n") end) end) in
  let _ = TextIO.output (file, "</theory>\n\n</omdoc>") in
  let _ = TextIO.closeOut file in () end
