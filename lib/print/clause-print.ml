
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
    let rec parens fmt = F.Hbox [sym "("; fmt; sym ")"]
    let rec fmtDQuants =
      function
      | (G, Pi (((Dec (_, V1) as D), I.Maybe), V2)) ->
          let D' = Names.decEName (G, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (G, D')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (G, D')), V2)
      | (G, Pi (((Dec (_, V1) as D), I.Meta), V2)) ->
          let D' = Names.decEName (G, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (G, D')) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (G, D')), V2)
      | (G, (Pi _ as V)) -> [F.HOVbox (fmtDSubGoals (G, V, nil))]
      | (G, V) -> [Print.formatExp (G, V)]
    let rec fmtDSubGoals =
      function
      | (G, Pi (((Dec (_, V1) as D), I.No), V2), acc) ->
          fmtDSubGoals
            ((I.Decl (G, D)), V2,
              (((::) (((::) F.Break sym "<-") :: F.Space) fmtGparens (G, V1))
                 :: acc))
      | (G, (Pi _ as V), acc) ->
          (parens (F.HVbox (fmtDQuants (G, V)))) :: acc
      | (G, V, acc) -> (Print.formatExp (G, V)) :: acc
    let rec fmtDparens =
      function
      | (G, (Pi _ as V)) -> parens (F.HVbox (fmtDQuants (G, V)))
      | (G, V) -> Print.formatExp (G, V)
    let rec fmtGparens =
      function
      | (G, (Pi _ as V)) -> parens (F.HVbox (fmtGQuants (G, V)))
      | (G, V) -> Print.formatExp (G, V)
    let rec fmtGQuants =
      function
      | (G, Pi (((Dec (_, V1) as D), I.Maybe), V2)) ->
          let D' = Names.decLUName (G, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (G, D')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (G, D')), V2)
      | (G, Pi (((Dec (_, V1) as D), I.Meta), V2)) ->
          let D' = Names.decLUName (G, D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (G, D')) sym "}") ::
                  F.Break)
            fmtGQuants ((I.Decl (G, D')), V2)
      | (G, V) -> [F.HOVbox (fmtGHyps (G, V))]
    let rec fmtGHyps =
      function
      | (G, Pi (((Dec (_, V1) as D), I.No), V2)) ->
          (::) (((::) ((fmtDparens (G, V1)) :: F.Break) sym "->") :: F.Space)
            fmtGHyps ((I.Decl (G, D)), V2)
      | (G, (Pi _ as V)) -> [F.HVbox (fmtGQuants (G, V))]
      | (G, V) -> [Print.formatExp (G, V)]
    let rec fmtClause (G, V) = F.HVbox (fmtDQuants (G, V))
    let rec fmtClauseI =
      function
      | (0, G, V) -> fmtClause (G, V)
      | (i, G, Pi ((D, _), V)) ->
          fmtClauseI ((i - 1), (I.Decl (G, (Names.decEName (G, D)))), V)
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
    (* assumes NF *)
    (* P = I.No *)
    (* V = Root _ *)
    (* acc <> nil *)
    (* V = Root _ *)
    (* V = Root _ *)
    (* V = Root _ *)
    (* P = I.No or V = Root _ *)
    (* P = I.Maybe *)
    (* V = Root _ *)
    (* type family declaration, definition, or Skolem constant *)
    let rec formatClause (G, V) = fmtClause (G, V)
    let rec formatConDec condec = fmtConDec condec
    let rec clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec printSgn () =
      IntSyn.sgnApp
        (function
         | cid -> (print (conDecToString (IntSyn.sgnLookup cid)); print "\n"))
  end ;;
