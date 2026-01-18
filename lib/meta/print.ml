
(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPRINT  =
  sig
    module Formatter : FORMATTER
    module StateSyn : STATESYN
    exception Error of string 
    val nameState : StateSyn.__State -> StateSyn.__State
    val formatState : StateSyn.__State -> Formatter.format
    val stateToString : StateSyn.__State -> string
  end;;




(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module MTPrint(MTPrint:sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module StateSyn' : STATESYN
                         module Formatter' : FORMATTER
                         module Print : PRINT
                         (*! structure IntSyn : INTSYN !*)
                         (*! structure FunSyn : FUNSYN !*)
                         (*! sharing FunSyn.IntSyn = IntSyn !*)
                         (*! sharing Names.IntSyn = IntSyn !*)
                         (*! sharing StateSyn'.FunSyn = FunSyn !*)
                         (*! sharing StateSyn'.IntSyn = IntSyn !*)
                         (*! sharing Print.IntSyn = IntSyn !*)
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
    let rec nameState (State (n, (__g, B), (IH, OH), d, O, H, F)) =
      let _ = Names.varReset I.Null in
      let __g' = Names.ctxName __g in S.State (n, (__g', B), (IH, OH), d, O, H, F)
    let rec formatOrder =
      function
      | (__g, Arg (__Us, __Vs)) ->
          [Print.formatExp (__g, (I.EClo __Us));
          Fmt.String ":";
          Print.formatExp (__g, (I.EClo __Vs))]
      | (__g, Lex (__Os)) ->
          [Fmt.String "{";
          Fmt.hVbox0 1 0 1 (formatOrders (__g, __Os));
          Fmt.String "}"]
      | (__g, Simul (__Os)) ->
          [Fmt.String "[";
          Fmt.hVbox0 1 0 1 (formatOrders (__g, __Os));
          Fmt.String "]"]
    let rec formatOrders =
      function
      | (__g, nil) -> nil
      | (__g, (O)::nil) -> formatOrder (__g, O)
      | (__g, (O)::__Os) ->
          (@) ((formatOrder (__g, O)) @ [Fmt.String ","; Fmt.Break])
            formatOrders (__g, __Os)
    let rec formatTag =
      function
      | (__g, Parameter l) -> [Fmt.String "<p>"]
      | (__g, Lemma (Splits k)) ->
          [Fmt.String "<i"; Fmt.String (Int.toString k); Fmt.String ">"]
      | (__g, Lemma (S.RL)) -> [Fmt.String "<i >"]
      | (__g, Lemma (S.RLdone)) -> [Fmt.String "<i*>"]
    let rec formatCtx =
      function
      | (I.Null, B) -> []
      | (Decl (I.Null, __d), Decl (I.Null, T)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.hVbox
               ((formatTag (I.Null, T)) @
                  [Fmt.Break; Print.formatDec (I.Null, __d)])]
          else [Print.formatDec (I.Null, __d)]
      | (Decl (__g, __d), Decl (B, T)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx (__g, B)) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.hVbox
                 ((formatTag (__g, T)) @ [Fmt.Break; Print.formatDec (__g, __d)])]
          else
            ((formatCtx (__g, B)) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__g, __d)]
    let rec formatState (State (n, (__g, B), (IH, OH), d, O, H, F)) =
      Fmt.Vbox0 0 1
        [Fmt.hVbox0 1 0 1 (formatOrder (__g, O));
        Fmt.Break;
        Fmt.String "========================";
        Fmt.Break;
        Fmt.hVbox0 1 0 1 (formatCtx (__g, B));
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        FunPrint.formatForBare (__g, F)]
    let rec stateToString (S) = Fmt.makestring_fmt (formatState S)
    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
    (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
    (*      | formatTag (__g, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)
    (* formatCtx (__g, B) = fmt'

       Invariant:
       If   |- __g ctx       and __g is already named
       and  |- B : __g tags
       then fmt' is a format describing the context (__g, B)
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
