
(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module type STATEPRINT  =
  sig
    module Formatter : FORMATTER
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    val nameState : State.__State -> State.__State
    val formatState : State.__State -> Formatter.format
    val stateToString : State.__State -> string
  end;;




(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module StatePrint(StatePrint:sig
                               module Global : GLOBAL
                               module State' : STATE
                               module Names : NAMES
                               module Formatter' : FORMATTER
                               module Print : PRINT
                               (*! structure IntSyn' : INTSYN !*)
                               (*! structure Tomega' : TOMEGA !*)
                               (*! sharing Tomega'.IntSyn = IntSyn' !*)
                               (*! sharing State'.IntSyn = IntSyn' !*)
                               (*! sharing State'.Tomega = Tomega' !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               (*! sharing Print.IntSyn = IntSyn' !*)
                               module TomegaPrint : TOMEGAPRINT
                             end) : STATEPRINT =
  struct
    module Formatter = Formatter'
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
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
      | Decl (I.Null, UDec (__d)) ->
          if (!Global.chatter) >= 4
          then [Fmt.hVbox [Fmt.Break; Print.formatDec (I.Null, __d)]]
          else [Print.formatDec (I.Null, __d)]
      | Decl (I.Null, PDec (Some s, F, _)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.hVbox
               [Fmt.Break;
               Fmt.String s;
               Fmt.space;
               Fmt.String "::";
               Fmt.space;
               TomegaPrint.formatFor (I.Null, F)]]
          else
            [Fmt.String s;
            Fmt.space;
            Fmt.String "::";
            Fmt.space;
            TomegaPrint.formatFor (I.Null, F)]
      | Decl (Psi, UDec (__d)) ->
          let __g = T.coerceCtx Psi in
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.hVbox [Fmt.Break; Print.formatDec (__g, __d)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__g, __d)]
      | Decl (Psi, PDec (Some s, F, _)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.hVbox
                 [Fmt.Break;
                 Fmt.String s;
                 Fmt.space;
                 Fmt.String "::";
                 Fmt.space;
                 TomegaPrint.formatFor (Psi, F)]]
          else
            ((formatCtx Psi) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break;
              Fmt.String s;
              Fmt.space;
              Fmt.String "::";
              Fmt.space;
              TomegaPrint.formatFor (Psi, F)]
    let rec formatState (State (W, Psi, P, F, _)) =
      Fmt.Vbox0 0 1
        [Fmt.String "------------------------";
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        TomegaPrint.formatPrg (Psi, P)]
    let rec stateToString (S) = Fmt.makestring_fmt (formatState S)
    (*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec __d)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, __d)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (Some "s", F, TC))    to be fixed! --cs *)
    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
    (*
    fun formatOrder (__g, S.Arg (__Us, __Vs)) =
          [Print.formatExp (__g, I.EClo __Us), Fmt.String ":",
           Print.formatExp (__g, I.EClo __Vs)]
      | formatOrder (__g, S.Lex __Os) =
          [Fmt.String "{", Fmt.hVbox0 1 0 1 (formatOrders (__g, __Os)), Fmt.String "}"]
      | formatOrder (__g, S.Simul __Os) =
          [Fmt.String "[", Fmt.hVbox0 1 0 1 (formatOrders (__g, __Os)), Fmt.String "]"]

    and formatOrders (__g, nil) = nil
      | formatOrders (__g, O :: nil) = formatOrder (__g, O)
      | formatOrders (__g, O :: __Os) = formatOrder (__g, O) @
          [Fmt.String ",", Fmt.Break]  @ formatOrders (__g, __Os)

     format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
    (*      | formatTag (__g, S.Assumption k) = [Fmt.String "<a",
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
    *)
    let nameState = nameState
    let formatState = formatState
    let stateToString = stateToString
  end ;;
