
module type METAPRINT  =
  sig
    module MetaSyn : METASYN
    val stateToString : MetaSyn.__State -> string
    val sgnToString : MetaSyn.__Sgn -> string
    val modeToString : MetaSyn.__Mode -> string
    val conDecToString : IntSyn.__ConDec -> string
  end;;




module MetaPrint(MetaPrint:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module Formatter : FORMATTER
                             module Print : PRINT
                             module ClausePrint : CLAUSEPRINT
                           end) : METAPRINT =
  struct
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    module I = IntSyn
    module F = Formatter
    let rec modeToString = function | M.Top -> "+" | M.Bot -> "-"
    let rec depthToString b = if b <= 0 then "" else Int.toString b
    let rec fmtPrefix (GM) =
      let rec fmtPrefix' __0__ __1__ =
        match (__0__, __1__) with
        | (Prefix (I.Null, I.Null, I.Null), Fmt) -> Fmt
        | (Prefix
           (Decl (I.Null, __D), Decl (I.Null, mode), Decl (I.Null, b)), Fmt)
            ->
            [F.String (depthToString b);
            F.String (modeToString mode);
            Print.formatDec (I.Null, __D)] @ Fmt
        | (Prefix (Decl (__G, __D), Decl (__M, mode), Decl (__B, b)), Fmt) ->
            fmtPrefix'
              ((M.Prefix (__G, __M, __B)),
                ([F.String ",";
                 F.Space;
                 F.Break;
                 F.String (depthToString b);
                 F.String (modeToString mode);
                 Print.formatDec (__G, __D)] @ Fmt)) in
      F.HVbox (fmtPrefix' (GM, []))
    let rec prefixToString (GM) = F.makestring_fmt (fmtPrefix GM)
    let rec stateToString (State (name, (Prefix (__G, __M, __B) as GM), __V))
      =
      ((^) (((^) (name ^ ":\n") prefixToString GM) ^ "\n--------------\n")
         ClausePrint.clauseToString (__G, __V))
        ^ "\n\n"
    let rec sgnToString =
      function
      | M.SgnEmpty -> ""
      | ConDec (e, __S) ->
          (^) ((if (!Global.chatter) >= 4
                then (Print.conDecToString e) ^ "\n"
                else
                  ((if (!Global.chatter) >= 3
                    then (ClausePrint.conDecToString e) ^ "\n"
                    else "")
                  (* use form without quantifiers, which is reparsable *)))
            (* use explicitly quantified form *))
            sgnToString __S
    let modeToString = modeToString
    let sgnToString = sgnToString
    let stateToString = stateToString
    let conDecToString = ClausePrint.conDecToString
  end ;;
