
module type MTPRINT  =
  sig
    module Formatter :
    ((FORMATTER)(* Meta Printer Version 1.3 *)(* Author: Carsten Schuermann *))
    module StateSyn : STATESYN
    exception Error of string 
    val nameState : StateSyn.__State -> StateSyn.__State
    val formatState : StateSyn.__State -> Formatter.format
    val stateToString : StateSyn.__State -> string
  end;;




module MTPrint(MTPrint:sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module StateSyn' : STATESYN
                         module Formatter' : FORMATTER
                         module Print : PRINT
                         module FunPrint :
                         ((FUNPRINT)(* Meta Printer Version 1.3 *)
                         (* Author: Carsten Schuermann *)
                         (*! structure IntSyn : INTSYN !*)
                         (*! structure FunSyn : FUNSYN !*)
                         (*! sharing FunSyn.IntSyn = IntSyn !*)(*! sharing Names.IntSyn = IntSyn !*)
                         (*! sharing StateSyn'.FunSyn = FunSyn !*)
                         (*! sharing StateSyn'.IntSyn = IntSyn !*)
                         (*! sharing Print.IntSyn = IntSyn !*))
                       end) : MTPRINT =
  struct
    module Formatter =
      ((Formatter')(*! sharing FunPrint.FunSyn = FunSyn !*))
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module N = Names
    module S = StateSyn
    module Fmt = Formatter
    let rec nameState (State (n, (g, B), (IH, OH), d, O, H, F)) =
      let _ = Names.varReset I.Null in
      let g' = Names.ctxName g in S.State (n, (g', B), (IH, OH), d, O, H, F)
    let rec formatOrder =
      function
      | (g, Arg (Us, Vs)) ->
          [Print.formatExp (g, (I.EClo Us));
          Fmt.String ":";
          Print.formatExp (g, (I.EClo Vs))]
      | (g, Lex (Os)) ->
          [Fmt.String "{";
          Fmt.HVbox0 1 0 1 (formatOrders (g, Os));
          Fmt.String "}"]
      | (g, Simul (Os)) ->
          [Fmt.String "[";
          Fmt.HVbox0 1 0 1 (formatOrders (g, Os));
          Fmt.String "]"]
    let rec formatOrders =
      function
      | (g, nil) -> nil
      | (g, (O)::nil) -> formatOrder (g, O)
      | (g, (O)::Os) ->
          (@) ((formatOrder (g, O)) @ [Fmt.String ","; Fmt.Break])
            formatOrders (g, Os)
    let rec formatTag =
      function
      | (g, Parameter l) -> [Fmt.String "<p>"]
      | (g, Lemma (Splits k)) ->
          [Fmt.String "<i"; Fmt.String (Int.toString k); Fmt.String ">"]
      | (g, Lemma (S.RL)) -> [Fmt.String "<i >"]
      | (g, Lemma (S.RLdone)) -> [Fmt.String "<i*>"]
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
      | (Decl (g, D), Decl (B, T)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx (g, B)) @ [Fmt.String ","; Fmt.Break; Fmt.Break]) @
              [Fmt.HVbox
                 ((formatTag (g, T)) @ [Fmt.Break; Print.formatDec (g, D)])]
          else
            ((formatCtx (g, B)) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (g, D)]
    let rec formatState (State (n, (g, B), (IH, OH), d, O, H, F)) =
      Fmt.Vbox0 0 1
        [Fmt.HVbox0 1 0 1 (formatOrder (g, O));
        Fmt.Break;
        Fmt.String "========================";
        Fmt.Break;
        Fmt.HVbox0 1 0 1 (formatCtx (g, B));
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        FunPrint.formatForBare (g, F)]
    let rec stateToString (S) = Fmt.makestring_fmt (formatState S)
    let ((nameState)(* nameState S = S'

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
      (*      | formatTag (g, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)
      (* formatCtx (g, B) = fmt'

       Invariant:
       If   |- g ctx       and g is already named
       and  |- B : g tags
       then fmt' is a format describing the context (g, B)
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
