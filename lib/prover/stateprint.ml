
module type STATEPRINT  =
  sig
    module Formatter : FORMATTER
    module State : STATE
    exception Error of string 
    val nameState : State.__State -> State.__State
    val formatState : State.__State -> Formatter.format
    val stateToString : State.__State -> string
  end;;




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
    let rec nameState (__S) = __S
    let rec formatCtx =
      function
      | I.Null -> []
      | Decl (I.Null, UDec (__D)) ->
          if (!Global.chatter) >= 4
          then [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, __D)]]
          else [Print.formatDec (I.Null, __D)]
      | Decl (I.Null, PDec (Some s, __F, _)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.Space;
               Fmt.String "::";
               Fmt.Space;
               TomegaPrint.formatFor (I.Null, __F)]]
          else
            [Fmt.String s;
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            TomegaPrint.formatFor (I.Null, __F)]
      | Decl (Psi, UDec (__D)) ->
          let __G = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox [Fmt.Break; Print.formatDec (__G, __D)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__G, __D)]
      | Decl (Psi, PDec (Some s, __F, _)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String "::";
                 Fmt.Space;
                 TomegaPrint.formatFor (Psi, __F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.Space;
              Fmt.String "::";
              Fmt.Space;
              TomegaPrint.formatFor (Psi, __F)]
    let rec formatState (State (__W, Psi, __P, __F, _)) =
      Fmt.Vbox0 0 1
        [Fmt.String "------------------------";
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        TomegaPrint.formatPrg (Psi, __P)]
    let rec stateToString (__S) = Fmt.makestring_fmt (formatState __S)
    let nameState = nameState
    let formatState = formatState
    let stateToString = stateToString
  end ;;
