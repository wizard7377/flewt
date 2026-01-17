
module type STATEPRINT  =
  sig
    module Formatter :
    ((FORMATTER)(* Meta Printer Version 1.3 *)(* Author: Carsten Schuermann *))
    module State :
    ((STATE)(*! structure IntSyn : INTSYN !*)(*! structure Tomega : TOMEGA !*))
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
                               module TomegaPrint :
                               ((TOMEGAPRINT)(* Meta Printer Version 1.3 *)
                               (* Author: Carsten Schuermann *)(*! structure IntSyn' : INTSYN !*)
                               (*! structure Tomega' : TOMEGA !*)
                               (*! sharing Tomega'.IntSyn = IntSyn' !*)
                               (*! sharing State'.IntSyn = IntSyn' !*)
                               (*! sharing State'.Tomega = Tomega' !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               (*! sharing Print.IntSyn = IntSyn' !*))
                             end) : STATEPRINT =
  struct
    module Formatter =
      ((Formatter')(*! sharing TomegaPrint.IntSyn = IntSyn' !*)(*! sharing TomegaPrint.Tomega = Tomega' !*))
    module State =
      ((State')(*! structure IntSyn = IntSyn' !*)(*! structure Tomega = Tomega' !*))
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module S = State'
    module N = Names
    module Fmt = Formatter
    let rec nameCtx (Psi) = Psi
    let rec nameState (S) = S
    let rec formatCtx =
      function
      | I.Null -> []
      | Decl (I.Null, UDec (D)) ->
          if (!Global.chatter) >= 4
          then [Fmt.HVbox [Fmt.Break; Print.formatDec (I.Null, D)]]
          else [Print.formatDec (I.Null, D)]
      | Decl (I.Null, PDec (SOME s, F, _)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.Space;
               Fmt.String "::";
               Fmt.Space;
               TomegaPrint.formatFor (I.Null, F)]]
          else
            [Fmt.String s;
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            TomegaPrint.formatFor (I.Null, F)]
      | Decl (Psi, UDec (D)) ->
          let g = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox [Fmt.Break; Print.formatDec (g, D)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (g, D)]
      | Decl (Psi, PDec (SOME s, F, _)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.Space;
                 Fmt.String "::";
                 Fmt.Space;
                 TomegaPrint.formatFor (Psi, F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.Space;
              Fmt.String "::";
              Fmt.Space;
              TomegaPrint.formatFor (Psi, F)]
    let rec formatState (State (W, Psi, P, F, _)) =
      Fmt.Vbox0 0 1
        [Fmt.String "------------------------";
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        TomegaPrint.formatPrg (Psi, P)]
    let rec stateToString (S) = Fmt.makestring_fmt (formatState S)
    let ((nameState)(*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME "s", F, TC))    to be fixed! --cs *)
      (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
      (*
    fun formatOrder (g, S.Arg (Us, Vs)) =
          [Print.formatExp (g, I.EClo Us), Fmt.String ":",
           Print.formatExp (g, I.EClo Vs)]
      | formatOrder (g, S.Lex Os) =
          [Fmt.String "{", Fmt.HVbox0 1 0 1 (formatOrders (g, Os)), Fmt.String "}"]
      | formatOrder (g, S.Simul Os) =
          [Fmt.String "[", Fmt.HVbox0 1 0 1 (formatOrders (g, Os)), Fmt.String "]"]

    and formatOrders (g, nil) = nil
      | formatOrders (g, O :: nil) = formatOrder (g, O)
      | formatOrders (g, O :: Os) = formatOrder (g, O) @
          [Fmt.String ",", Fmt.Break]  @ formatOrders (g, Os)

     format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
      (*      | formatTag (g, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)
      (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
      (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
      (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *))
      = nameState
    let formatState = formatState
    let stateToString = stateToString
  end ;;
