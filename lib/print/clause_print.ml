module type CLAUSEPRINT  =
  sig
    module Formatter : FORMATTER
    val formatClause : (IntSyn.dctx * IntSyn.exp_) -> Formatter.format
    val formatConDec : IntSyn.conDec_ -> Formatter.format
    val clauseToString : (IntSyn.dctx * IntSyn.exp_) -> string
    val conDecToString : IntSyn.conDec_ -> string
    val printSgn : unit -> unit
  end


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
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec parens fmt = F.Hbox [sym "("; fmt; sym ")"]
    let rec fmtDQuants =
      begin function
      | (g_, Pi (((Dec (_, v1_) as d_), I.Maybe), v2_)) ->
          let d'_ = Names.decEName (g_, d_) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g_, d'_)) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (g_, d'_)), v2_)
      | (g_, Pi (((Dec (_, v1_) as d_), I.Meta), v2_)) ->
          let d'_ = Names.decEName (g_, d_) in
          (::) (((::) ((::) (sym "{") Print.formatDec (g_, d'_)) sym "}") ::
                  F.Break)
            fmtDQuants ((I.Decl (g_, d'_)), v2_)
      | (g_, (Pi _ as v_)) -> [F.HOVbox (fmtDSubGoals (g_, v_, []))]
      | (g_, v_) -> [Print.formatExp (g_, v_)] end(* V = Root _ *)
    (* P = I.No *)
    let rec fmtDSubGoals =
      begin function
      | (g_, Pi (((Dec (_, v1_) as d_), I.No), v2_), acc) ->
          fmtDSubGoals
            ((I.Decl (g_, d_)), v2_,
              (((::) (((::) F.Break sym "<-") :: F.Space) fmtGparens
                  (g_, v1_))
                 :: acc))
      | (g_, (Pi _ as v_), acc) ->
          (parens (F.HVbox (fmtDQuants (g_, v_)))) :: acc
      | (g_, v_, acc) -> (Print.formatExp (g_, v_)) :: acc end(* V = Root _ *)
    (* acc <> nil *)
  let rec fmtDparens =
    begin function
    | (g_, (Pi _ as v_)) -> parens (F.HVbox (fmtDQuants (g_, v_)))
    | (g_, v_) -> Print.formatExp (g_, v_) end(* V = Root _ *)
let rec fmtGparens =
  begin function
  | (g_, (Pi _ as v_)) -> parens (F.HVbox (fmtGQuants (g_, v_)))
  | (g_, v_) -> Print.formatExp (g_, v_) end(* V = Root _ *)
let rec fmtGQuants =
  begin function
  | (g_, Pi (((Dec (_, v1_) as d_), I.Maybe), v2_)) ->
      let d'_ = Names.decLUName (g_, d_) in
      (::) (((::) ((::) (sym "{") Print.formatDec (g_, d'_)) sym "}") ::
              F.Break)
        fmtGQuants ((I.Decl (g_, d'_)), v2_)
  | (g_, Pi (((Dec (_, v1_) as d_), I.Meta), v2_)) ->
      let d'_ = Names.decLUName (g_, d_) in
      (::) (((::) ((::) (sym "{") Print.formatDec (g_, d'_)) sym "}") ::
              F.Break)
        fmtGQuants ((I.Decl (g_, d'_)), v2_)
  | (g_, v_) -> [F.HOVbox (fmtGHyps (g_, v_))] end(* P = I.No or V = Root _ *)
let rec fmtGHyps =
  begin function
  | (g_, Pi (((Dec (_, v1_) as d_), I.No), v2_)) ->
      (::) (((::) ((fmtDparens (g_, v1_)) :: F.Break) sym "->") :: F.Space)
        fmtGHyps ((I.Decl (g_, d_)), v2_)
  | (g_, (Pi _ as v_)) -> [F.HVbox (fmtGQuants (g_, v_))]
  | (g_, v_) -> [Print.formatExp (g_, v_)] end(* V = Root _ *)(* P = I.Maybe *)
let rec fmtClause (g_, v_) = F.HVbox (fmtDQuants (g_, v_))
let rec fmtClauseI =
  begin function
  | (0, g_, v_) -> fmtClause (g_, v_)
  | (i, g_, Pi ((d_, _), v_)) ->
      fmtClauseI ((i - 1), (I.Decl (g_, (Names.decEName (g_, d_)))), v_) end
let rec fmtConDec =
  begin function
  | ConDec (id, parent, i, _, v_, I.Type) ->
      let _ = Names.varReset IntSyn.Null in
      let Vfmt = fmtClauseI (i, I.Null, v_) in
      F.HVbox
        [Str0 (Symbol.const id); F.Space; sym ":"; F.Break; Vfmt; sym "."]
  | condec -> Print.formatConDec condec end(* type family declaration, definition, or Skolem constant *)
let rec formatClause (g_, v_) = fmtClause (g_, v_)
let rec formatConDec condec = fmtConDec condec
let rec clauseToString (g_, v_) = F.makestring_fmt (formatClause (g_, v_))
let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
let rec printSgn () =
  IntSyn.sgnApp
    (begin function
     | cid ->
         (begin print (conDecToString (IntSyn.sgnLookup cid)); print "\n" end) end)
end
