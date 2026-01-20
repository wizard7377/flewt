
module type MTPRINT  =
  sig
    module Formatter : FORMATTER
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
    let rec nameState (State (n, (__G, __B), (IH, OH), d, __O, __H, __F)) =
      let _ = Names.varReset I.Null in
      let __G' = Names.ctxName __G in
      S.State (n, (__G', __B), (IH, OH), d, __O, __H, __F)
    let rec formatOrder __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Arg (__Us, __Vs)) ->
          [Print.formatExp (__G, (I.EClo __Us));
          Fmt.String ":";
          Print.formatExp (__G, (I.EClo __Vs))]
      | (__G, Lex (__Os)) ->
          [Fmt.String "{";
          Fmt.HVbox0 1 0 1 (formatOrders (__G, __Os));
          Fmt.String "}"]
      | (__G, Simul (__Os)) ->
          [Fmt.String "[";
          Fmt.HVbox0 1 0 1 (formatOrders (__G, __Os));
          Fmt.String "]"]
    let rec formatOrders __2__ __3__ =
      match (__2__, __3__) with
      | (__G, nil) -> nil
      | (__G, (__O)::nil) -> formatOrder (__G, __O)
      | (__G, (__O)::__Os) ->
          (@) ((formatOrder (__G, __O)) @ [Fmt.String ","; Fmt.Break])
            formatOrders (__G, __Os)
    let rec formatTag __4__ __5__ =
      match (__4__, __5__) with
      | (__G, Parameter l) -> [Fmt.String "<p>"]
      | (__G, Lemma (Splits k)) ->
          [Fmt.String "<i"; Fmt.String (Int.toString k); Fmt.String ">"]
      | (__G, Lemma (S.RL)) -> [Fmt.String "<i >"]
      | (__G, Lemma (S.RLdone)) -> [Fmt.String "<i*>"]
    let rec formatCtx __6__ __7__ =
      match (__6__, __7__) with
      | (I.Null, __B) -> []
      | (Decl (I.Null, __D), Decl (I.Null, __T)) ->
          if (!Global.chatter) >= 4
          then
            [Fmt.HVbox
               ((formatTag (I.Null, __T)) @
                  [Fmt.Break; Print.formatDec (I.Null, __D)])]
          else [Print.formatDec (I.Null, __D)]
      | (Decl (__G, __D), Decl (__B, __T)) ->
          if (!Global.chatter) >= 4
          then
            ((formatCtx (__G, __B)) @ [Fmt.String ","; Fmt.Break; Fmt.Break])
              @
              [Fmt.HVbox
                 ((formatTag (__G, __T)) @
                    [Fmt.Break; Print.formatDec (__G, __D)])]
          else
            ((formatCtx (__G, __B)) @ [Fmt.String ","; Fmt.Break]) @
              [Fmt.Break; Print.formatDec (__G, __D)]
    let rec formatState (State (n, (__G, __B), (IH, OH), d, __O, __H, __F)) =
      Fmt.Vbox0 0 1
        [Fmt.HVbox0 1 0 1 (formatOrder (__G, __O));
        Fmt.Break;
        Fmt.String "========================";
        Fmt.Break;
        Fmt.HVbox0 1 0 1 (formatCtx (__G, __B));
        Fmt.Break;
        Fmt.String "------------------------";
        Fmt.Break;
        FunPrint.formatForBare (__G, __F)]
    let rec stateToString (__S) = Fmt.makestring_fmt (formatState __S)
    let nameState = nameState
    let formatState = formatState
    let stateToString = stateToString
  end ;;
