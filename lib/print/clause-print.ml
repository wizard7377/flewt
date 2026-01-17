
module type CLAUSEPRINT  =
  sig
    module Formatter :
    ((FORMATTER)(* Clause Printing *)(* Author: Frank Pfenning, Carsten Schuermann *)
    (*! structure IntSyn : INTSYN !*))
    val formatClause : (IntSyn.dctx * IntSyn.__Exp) -> Formatter.format
    val formatConDec : IntSyn.__ConDec -> Formatter.format
    val clauseToString : (IntSyn.dctx * IntSyn.__Exp) -> string
    val conDecToString : IntSyn.__ConDec -> string
    val printSgn : unit -> unit
  end;;




module ClausePrint(ClausePrint:sig
                                 module Whnf : WHNF
                                 module Names : NAMES
                                 module Formatter' : FORMATTER
                                 module Print : PRINT
                                 module Symbol :
                                 ((SYMBOL)(* Clause Printing *)(* Author: Frank Pfenning, Carsten Schuermann *)
                                 (* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 (*! sharing Print.IntSyn = IntSyn' !*))
                               end) : CLAUSEPRINT =
  struct
    module Formatter =
      ((Formatter')(*! structure IntSyn = IntSyn' !*))
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec parens fmt = F.Hbox [sym "("; fmt; sym ")"]
    let rec fmtDQuants =
      function
      | (g, Pi (((Dec (_, V1) as D), I.Maybe), V2)) ->
          let D' = Names.decEName (g, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g, D')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (g, D')), V2)
      | (g, Pi (((Dec (_, V1) as D), I.Meta), V2)) ->
          let D' = Names.decEName (g, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g, D')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (g, D')), V2)
      | (g, (Pi _ as V)) -> [F.HOVbox (fmtDSubGoals (g, V, nil))]
      | (g, V) -> [Print.formatExp (g, V)]
    let rec fmtDSubGoals =
      function
      | (g, Pi (((Dec (_, V1) as D), I.No), V2), acc) ->
          fmtDSubGoals
            ((I.Decl (g, D)), V2,
              (((::) (((::) F.Break sym "<-") :: F.Space) fmtGparens (g, V1))
                 :: acc))
      | (g, (Pi _ as V), acc) ->
          (parens (F.HVbox (fmtDQuants (g, V)))) :: acc
      | (g, V, acc) -> (Print.formatExp (g, V)) :: acc
    let rec fmtDparens =
      function
      | (g, (Pi _ as V)) -> parens (F.HVbox (fmtDQuants (g, V)))
      | (g, V) -> Print.formatExp (g, V)
    let rec fmtGparens =
      function
      | (g, (Pi _ as V)) -> parens (F.HVbox (fmtGQuants (g, V)))
      | (g, V) -> Print.formatExp (g, V)
    let rec fmtGQuants =
      function
      | (g, Pi (((Dec (_, V1) as D), I.Maybe), V2)) ->
          let D' = Names.decLUName (g, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g, D')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (g, D')), V2)
      | (g, Pi (((Dec (_, V1) as D), I.Meta), V2)) ->
          let D' = Names.decLUName (g, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g, D')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (g, D')), V2)
      | (g, V) -> [F.HOVbox (fmtGHyps (g, V))]
    let rec fmtGHyps =
      function
      | (g, Pi (((Dec (_, V1) as D), I.No), V2)) ->
          (::) (((::) ((fmtDparens (g, V1)) :: F.Break) sym "->") :: F.Space)
            fmtGHyps ((I.Decl (g, D)), V2)
      | (g, (Pi _ as V)) -> [F.HVbox (fmtGQuants (g, V))]
      | (g, V) -> [Print.formatExp (g, V)]
    let rec fmtClause (g, V) = F.HVbox (fmtDQuants (g, V))
    let rec fmtClauseI =
      function
      | (0, g, V) -> fmtClause (g, V)
      | (i, g, Pi ((D, _), V)) ->
          fmtClauseI ((i - 1), (I.Decl (g, (Names.decEName (g, D)))), V)
    let rec fmtConDec =
      function
      | ConDec (id, parent, i, _, V, I.Type) ->
          let _ = Names.varReset IntSyn.Null in
          let Vfmt = fmtClauseI (i, I.Null, V) in
          F.HVbox
            [Str0 (Symbol.const id);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | condec -> Print.formatConDec condec
    let rec formatClause
      (((g)(* some shorthands *)(* assumes NF *)
       (* P = I.No *)(* V = Root _ *)
       (* acc <> nil *)(* V = Root _ *)
       (* V = Root _ *)(* V = Root _ *)
       (* P = I.No or V = Root _ *)(* P = I.Maybe *)
       (* V = Root _ *)(* type family declaration, definition, or Skolem constant *)),
       V)
      = fmtClause (g, V)
    let rec formatConDec condec = fmtConDec condec
    let rec clauseToString (g, V) = F.makestring_fmt (formatClause (g, V))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec printSgn () =
      IntSyn.sgnApp
        (function
         | cid -> (print (conDecToString (IntSyn.sgnLookup cid)); print "\n"))
  end ;;
