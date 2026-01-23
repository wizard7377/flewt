module type MTPRINT  =
  sig
    module Formatter : FORMATTER
    module StateSyn : STATESYN
    exception Error of string 
    val nameState : StateSyn.state_ -> StateSyn.state_
    val formatState : StateSyn.state_ -> Formatter.format
    val stateToString : StateSyn.state_ -> string
  end


module MTPrint(MTPrint:sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module StateSyn' : STATESYN
                         module Formatter' : FORMATTER
                         module Print : PRINT
                         module FunPrint : FUNPRINT
                       end) : MTPRINT =
  struct
    module Formatter = Formatter'
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module N = Names
    module S = StateSyn
    module Fmt = Formatter
    let rec nameState (State (n, (g_, b_), (IH, OH), d, o_, h_, f_)) =
      let _ = Names.varReset I.Null in
      let g'_ = Names.ctxName g_ in
      S.State (n, (g'_, b_), (IH, OH), d, o_, h_, f_)
    let rec formatOrder =
      begin function
      | (g_, Arg (us_, vs_)) ->
          [Print.formatExp (g_, (I.EClo us_));
          Fmt.String ":";
          Print.formatExp (g_, (I.EClo vs_))]
      | (g_, Lex (os_)) ->
          [Fmt.String "{";
          Fmt.HVbox0 1 0 1 (formatOrders (g_, os_));
          Fmt.String "}"]
      | (g_, Simul (os_)) ->
          [Fmt.String "[";
          Fmt.HVbox0 1 0 1 (formatOrders (g_, os_));
          Fmt.String "]"] end
    let rec formatOrders =
      begin function
      | (g_, []) -> []
      | (g_, (o_)::[]) -> formatOrder (g_, o_)
      | (g_, (o_)::os_) ->
          (@) ((formatOrder (g_, o_)) @ [Fmt.String ","; Fmt.Break])
            formatOrders (g_, os_) end
  let rec formatTag =
    begin function
    | (g_, Parameter l) -> [Fmt.String "<p>"]
    | (g_, Lemma (Splits k)) ->
        [Fmt.String "<i"; Fmt.String (Int.toString k); Fmt.String ">"]
    | (g_, Lemma (S.RL)) -> [Fmt.String "<i >"]
    | (g_, Lemma (S.RLdone)) -> [Fmt.String "<i*>"] end
let rec formatCtx =
  begin function
  | (I.Null, b_) -> []
  | (Decl (I.Null, d_), Decl (I.Null, t_)) ->
      if !Global.chatter >= 4
      then
        begin [Fmt.HVbox
                 ((formatTag (I.Null, t_)) @
                    [Fmt.Break; Print.formatDec (I.Null, d_)])] end
      else begin [Print.formatDec (I.Null, d_)] end
  | (Decl (g_, d_), Decl (b_, t_)) ->
      if !Global.chatter >= 4
      then
        begin ((formatCtx (g_, b_)) @ [Fmt.String ","; Fmt.Break; Fmt.Break])
                @
                [Fmt.HVbox
                   ((formatTag (g_, t_)) @
                      [Fmt.Break; Print.formatDec (g_, d_)])] end
      else begin
        ((formatCtx (g_, b_)) @ [Fmt.String ","; Fmt.Break]) @
          [Fmt.Break; Print.formatDec (g_, d_)] end end
let rec formatState (State (n, (g_, b_), (IH, OH), d, o_, h_, f_)) =
  Fmt.Vbox0 0 1
    [Fmt.HVbox0 1 0 1 (formatOrder (g_, o_));
    Fmt.Break;
    Fmt.String "========================";
    Fmt.Break;
    Fmt.HVbox0 1 0 1 (formatCtx (g_, b_));
    Fmt.Break;
    Fmt.String "------------------------";
    Fmt.Break;
    FunPrint.formatForBare (g_, f_)]
let rec stateToString (s_) = Fmt.makestring_fmt (formatState s_)
let nameState = nameState
let formatState = formatState
let stateToString = stateToString end
