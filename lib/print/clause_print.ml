
(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type CLAUSEPRINT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    module Formatter : FORMATTER
    val formatClause : (IntSyn.dctx * IntSyn.__Exp) -> Formatter.format
    val formatConDec : IntSyn.__ConDec -> Formatter.format
    val clauseToString : (IntSyn.dctx * IntSyn.__Exp) -> string
    val conDecToString : IntSyn.__ConDec -> string
    val printSgn : unit -> unit
  end;;




(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)
module ClausePrint(ClausePrint:sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 module Whnf : WHNF
                                 module Names : NAMES
                                 module Formatter' : FORMATTER
                                 module Print : PRINT
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 (*! sharing Print.IntSyn = IntSyn' !*)
                                 module Symbol : SYMBOL
                               end) : CLAUSEPRINT =
  struct
    (*! structure IntSyn = IntSyn' !*)
    module Formatter = Formatter'
    (* some shorthands *)
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec parens fmt = F.hbox [sym "("; fmt; sym ")"]
    let rec fmtDQuants =
      function
      | (__g, Pi (((Dec (_, V1) as __d), I.Maybe), V2)) ->
          let __d' = Names.decEName (__g, __d) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__g, __d')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (__g, __d')), V2)
      | (__g, Pi (((Dec (_, V1) as __d), I.Meta), V2)) ->
          let __d' = Names.decEName (__g, __d) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__g, __d')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (__g, __d')), V2)
      | (__g, (Pi _ as __v)) -> [F.hOVbox (fmtDSubGoals (__g, __v, nil))]
      | (__g, __v) -> [Print.formatExp (__g, __v)]
    let rec fmtDSubGoals =
      function
      | (__g, Pi (((Dec (_, V1) as __d), I.No), V2), acc) ->
          fmtDSubGoals
            ((I.Decl (__g, __d)), V2,
              (((::) (((::) F.Break sym "<-") :: F.space) fmtGparens (__g, V1))
                 :: acc))
      | (__g, (Pi _ as __v), acc) ->
          (parens (F.hVbox (fmtDQuants (__g, __v)))) :: acc
      | (__g, __v, acc) -> (Print.formatExp (__g, __v)) :: acc
    let rec fmtDparens =
      function
      | (__g, (Pi _ as __v)) -> parens (F.hVbox (fmtDQuants (__g, __v)))
      | (__g, __v) -> Print.formatExp (__g, __v)
    let rec fmtGparens =
      function
      | (__g, (Pi _ as __v)) -> parens (F.hVbox (fmtGQuants (__g, __v)))
      | (__g, __v) -> Print.formatExp (__g, __v)
    let rec fmtGQuants =
      function
      | (__g, Pi (((Dec (_, V1) as __d), I.Maybe), V2)) ->
          let __d' = Names.decLUName (__g, __d) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__g, __d')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (__g, __d')), V2)
      | (__g, Pi (((Dec (_, V1) as __d), I.Meta), V2)) ->
          let __d' = Names.decLUName (__g, __d) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__g, __d')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (__g, __d')), V2)
      | (__g, __v) -> [F.hOVbox (fmtGHyps (__g, __v))]
    let rec fmtGHyps =
      function
      | (__g, Pi (((Dec (_, V1) as __d), I.No), V2)) ->
          (::) (((::) ((fmtDparens (__g, V1)) :: F.Break) sym "->") :: F.space)
            fmtGHyps ((I.Decl (__g, __d)), V2)
      | (__g, (Pi _ as __v)) -> [F.hVbox (fmtGQuants (__g, __v))]
      | (__g, __v) -> [Print.formatExp (__g, __v)]
    let rec fmtClause (__g, __v) = F.hVbox (fmtDQuants (__g, __v))
    let rec fmtClauseI =
      function
      | (0, __g, __v) -> fmtClause (__g, __v)
      | (i, __g, Pi ((__d, _), __v)) ->
          fmtClauseI ((i - 1), (I.Decl (__g, (Names.decEName (__g, __d)))), __v)
    let rec fmtConDec =
      function
      | ConDec (id, parent, i, _, __v, I.Type) ->
          let _ = Names.varReset IntSyn.Null in
          let Vfmt = fmtClauseI (i, I.Null, __v) in
          F.hVbox
            [Str0 (Symbol.const id);
            F.space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | condec -> Print.formatConDec condec
    (* assumes NF *)
    (* P = I.No *)
    (* __v = Root _ *)
    (* acc <> nil *)
    (* __v = Root _ *)
    (* __v = Root _ *)
    (* __v = Root _ *)
    (* P = I.No or __v = Root _ *)
    (* P = I.Maybe *)
    (* __v = Root _ *)
    (* type family declaration, definition, or Skolem constant *)
    let rec formatClause (__g, __v) = fmtClause (__g, __v)
    let rec formatConDec condec = fmtConDec condec
    let rec clauseToString (__g, __v) = F.makestring_fmt (formatClause (__g, __v))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec printSgn () =
      IntSyn.sgnApp
        (function
         | cid -> (print (conDecToString (IntSyn.sgnLookup cid)); print "\n"))
  end ;;
