
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
    let rec nameState (State (n, (G, B), (IH, OH), d, O, H, F)) =
      let _ = Names.varReset I.Null in
      let G' = Names.ctxName G in S.State (n, (G', B), (IH, OH), d, O, H, F)
    let rec formatOrder =
      function
      | (G, Arg (Us, Vs)) ->
          [Print.formatExp (G, (I.EClo Us));
          Fmt.String ":";
          Print.formatExp (G, (I.EClo Vs))]
      | (G, Lex (Os)) ->
          [Fmt.String "{";
          Fmt.HVbox0 1 0 1 (formatOrders (G, Os));
          Fmt.String "}"]
      | (G, Simul (Os)) ->
          [Fmt.String "[";
          Fmt.HVbox0 1 0 1 (formatOrders (G, Os));
          Fmt.String "]"]
    let rec formatOrders =
      function
      | (G, nil) -> nil
      | (G, (O)::nil) -> formatOrder (G, O)
      | (G, (O)::Os) ->
          (@) ((formatOrder (G, O)) @ [Fmt.String ","; Fmt.Break])
            formatOrders (G, Os)
    let rec formatTag =
      function
      | (G, Parameter l) -> [Fmt.String "<p>"]
      | (G, Lemma (Splits k)) ->
          [Fmt.String "<i"; Fmt.String (Int.toString k); Fmt.String ">"]
      | (G, Lemma (S.RL)) -> [Fmt.String "<i >"]
      | (G, Lemma (S.RLdone)) -> [Fmt.String "<i*>"]
    let rec formatCtx =
      function
      | (I.Null, B) -> []
      | (Decl (I.Null, D), Decl (I.Null, T)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               ((formatTag (I.Null, T)) @
                  [Fmt.Break; Print.formatDec (I.Null, D)])]
          else [Print.formatDec (I.Null, D)]
      | (Decl (G, D), Decl (B, T)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx (G, B)) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 ((formatTag (G, T)) @ [Fmt.Break; Print.formatDec (G, D)])]
          else
            ((formatCtx (G, B)) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (G, D)]
    let rec formatState (State (n, (G, B), (IH, OH), d, O, H, F)) =
      Fmt.Vbox0 0 1
        [Fmt.HVbox0 1 0 1 (formatOrder (G, O));
        Fmt.Break;
        Fmt.String "========================";
        Fmt.Break;
        Fmt.HVbox0 1 0 1 (formatCtx (G, B));
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        FunPrint.formatForBare (G, F)]
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
    (*      | formatTag (G, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)
    (* formatCtx (G, B) = fmt'

       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
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
