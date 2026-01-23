module type STATEPRINT  =
  sig
    module Formatter : FORMATTER
    module State : STATE
    exception Error of string 
    val nameState : State.state_ -> State.state_
    val formatState : State.state_ -> Formatter.format
    val stateToString : State.state_ -> string
  end


module StatePrint(StatePrint:sig
                               module Global : GLOBAL
                               module State' : STATE
                               module Names : NAMES
                               module Formatter' : FORMATTER
                               module Print : PRINT
                               module TomegaPrint : TOMEGAPRINT
                             end) : STATEPRINT =
  struct
    module Formatter = Formatter'
    module State = State'
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module S = State'
    module N = Names
    module Fmt = Formatter
    let rec nameCtx (Psi) = Psi
    let rec nameState (s_) = s_
    let rec formatCtx =
      begin function
      | I.Null -> []
      | Decl (I.Null, UDec (d_)) ->
          if !Global.chatter >= 4
          then begin [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, d_)]] end
          else begin [Print.formatDec (I.Null, d_)] end
      | Decl (I.Null, PDec (Some s, f_, _)) ->
          if !Global.chatter >= 4
          then
            begin [Fmt.HVbox
                     [Fmt.Break;
                     Fmt.String s;
                     Fmt.Space;
                     Fmt.String "::";
                     Fmt.Space;
                     TomegaPrint.formatFor (I.Null, f_)]] end
          else begin
            [Fmt.String s;
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            TomegaPrint.formatFor (I.Null, f_)] end
    | Decl (Psi, UDec (d_)) ->
        let g_ = T.coerceCtx Psi in
        if !Global.chatter >= 4
        then
          begin ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
                  [Fmt.HVbox [Fmt.Break; Print.formatDec (g_, d_)]] end
          else begin
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (g_, d_)] end
| Decl (Psi, PDec (Some s, f_, _)) ->
    if !Global.chatter >= 4
    then
      begin ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String "::";
                 Fmt.Space;
                 TomegaPrint.formatFor (Psi, f_)]] end
    else begin
      ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
        [Fmt.Break;
        Fmt.String s;
        Fmt.Space;
        Fmt.String "::";
        Fmt.Space;
        TomegaPrint.formatFor (Psi, f_)] end end
let rec formatState (State (w_, Psi, p_, f_, _)) =
  Fmt.Vbox0 0 1
    [Fmt.String "------------------------";
    Fmt.Break;
    Fmt.String "------------------------";
    Fmt.Break;
    TomegaPrint.formatPrg (Psi, p_)]
let rec stateToString (s_) = Fmt.makestring_fmt (formatState s_)
let nameState = nameState
let formatState = formatState
let stateToString = stateToString end
