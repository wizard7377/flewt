
module type CLAUSEPRINT  =
  sig
    module Formatter : FORMATTER
    val formatClause : IntSyn.dctx -> IntSyn.__Exp -> Formatter.format
    val formatConDec : IntSyn.__ConDec -> Formatter.format
    val clauseToString : IntSyn.dctx -> IntSyn.__Exp -> string
    val conDecToString : IntSyn.__ConDec -> string
    val printSgn : unit -> unit
  end;;




module ClausePrint(ClausePrint:sig
                                 module Whnf : WHNF
                                 module Names : NAMES
                                 module Formatter' : FORMATTER
                                 module Print : PRINT
                                 module Symbol : SYMBOL
                               end) : CLAUSEPRINT =
  struct
    module Formatter = Formatter'
    module I = IntSyn
    module F = Formatter
    let Str = F.String
    let rec Str0 s n = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec parens fmt = F.Hbox [sym "("; fmt; sym ")"]
    let rec fmtDQuants __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Pi (((Dec (_, __V1) as D), I.Maybe), __V2)) ->
          let __D' = Names.decEName (__G, __D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__G, __D')) sym "}")
                  :: F.Break)
            fmtDQuants ((I.Decl (__G, __D')), __V2)
      | (__G, Pi (((Dec (_, __V1) as D), I.Meta), __V2)) ->
          let __D' = Names.decEName (__G, __D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__G, __D')) sym "}")
                  :: F.Break)
            fmtDQuants ((I.Decl (__G, __D')), __V2)
      | (__G, (Pi _ as V)) -> [F.HOVbox (fmtDSubGoals (__G, __V, nil))]
      | (__G, __V) -> [Print.formatExp (__G, __V)](* V = Root _ *)
      (* P = I.No *)
    let rec fmtDSubGoals __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, Pi (((Dec (_, __V1) as D), I.No), __V2), acc) ->
          fmtDSubGoals
            ((I.Decl (__G, __D)), __V2,
              (((::) (((::) F.Break sym "<-") :: F.Space) fmtGparens
                  (__G, __V1))
                 :: acc))
      | (__G, (Pi _ as V), acc) ->
          (parens (F.HVbox (fmtDQuants (__G, __V)))) :: acc
      | (__G, __V, acc) -> (Print.formatExp (__G, __V)) :: acc(* V = Root _ *)
      (* acc <> nil *)
    let rec fmtDparens __5__ __6__ =
      match (__5__, __6__) with
      | (__G, (Pi _ as V)) -> parens (F.HVbox (fmtDQuants (__G, __V)))
      | (__G, __V) -> Print.formatExp (__G, __V)(* V = Root _ *)
    let rec fmtGparens __7__ __8__ =
      match (__7__, __8__) with
      | (__G, (Pi _ as V)) -> parens (F.HVbox (fmtGQuants (__G, __V)))
      | (__G, __V) -> Print.formatExp (__G, __V)(* V = Root _ *)
    let rec fmtGQuants __9__ __10__ =
      match (__9__, __10__) with
      | (__G, Pi (((Dec (_, __V1) as D), I.Maybe), __V2)) ->
          let __D' = Names.decLUName (__G, __D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__G, __D')) sym "}")
                  :: F.Break)
            fmtGQuants ((I.Decl (__G, __D')), __V2)
      | (__G, Pi (((Dec (_, __V1) as D), I.Meta), __V2)) ->
          let __D' = Names.decLUName (__G, __D) in
          (::) (((::) ((::) (sym "{") Print.formatDec (__G, __D')) sym "}")
                  :: F.Break)
            fmtGQuants ((I.Decl (__G, __D')), __V2)
      | (__G, __V) -> [F.HOVbox (fmtGHyps (__G, __V))](* P = I.No or V = Root _ *)
    let rec fmtGHyps __11__ __12__ =
      match (__11__, __12__) with
      | (__G, Pi (((Dec (_, __V1) as D), I.No), __V2)) ->
          (::) (((::) ((fmtDparens (__G, __V1)) :: F.Break) sym "->") ::
                  F.Space)
            fmtGHyps ((I.Decl (__G, __D)), __V2)
      | (__G, (Pi _ as V)) -> [F.HVbox (fmtGQuants (__G, __V))]
      | (__G, __V) -> [Print.formatExp (__G, __V)](* V = Root _ *)
      (* P = I.Maybe *)
    let rec fmtClause (__G) (__V) = F.HVbox (fmtDQuants (__G, __V))
    let rec fmtClauseI __13__ __14__ __15__ =
      match (__13__, __14__, __15__) with
      | (0, __G, __V) -> fmtClause (__G, __V)
      | (i, __G, Pi ((__D, _), __V)) ->
          fmtClauseI
            ((i - 1), (I.Decl (__G, (Names.decEName (__G, __D)))), __V)
    let rec fmtConDec =
      function
      | ConDec (id, parent, i, _, __V, I.Type) ->
          let _ = Names.varReset IntSyn.Null in
          let Vfmt = fmtClauseI (i, I.Null, __V) in
          F.HVbox
            [Str0 (Symbol.const id);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | condec -> Print.formatConDec condec(* type family declaration, definition, or Skolem constant *)
    let rec formatClause (__G) (__V) = fmtClause (__G, __V)
    let rec formatConDec condec = fmtConDec condec
    let rec clauseToString (__G) (__V) =
      F.makestring_fmt (formatClause (__G, __V))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec printSgn () =
      IntSyn.sgnApp
        (fun cid -> print (conDecToString (IntSyn.sgnLookup cid)); print "\n")
  end ;;
