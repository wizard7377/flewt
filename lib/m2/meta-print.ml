
module type METAPRINT  =
  sig
    module MetaSyn :
    ((METASYN)(* Meta printer for proof states *)(* Author: Carsten Schuermann *))
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
                             module ClausePrint :
                             ((CLAUSEPRINT)(* Meta printer for proof states *)
                             (* Author: Carsten Schuermann *)(*! sharing Print.IntSyn = MetaSyn'.IntSyn !*))
                           end) : METAPRINT =
  struct
    module MetaSyn =
      ((MetaSyn')(*! sharing ClausePrint.IntSyn = MetaSyn'.IntSyn !*))
    module M = MetaSyn
    module I = IntSyn
    module F = Formatter
    let rec modeToString = function | M.Top -> "+" | M.Bot -> "-"
    let rec depthToString b = if b <= 0 then "" else Int.toString b
    let rec fmtPrefix (GM) =
      let fmtPrefix' =
        function
        | (Prefix (I.Null, I.Null, I.Null), Fmt) -> Fmt
        | (Prefix (Decl (I.Null, D), Decl (I.Null, mode), Decl (I.Null, b)),
           Fmt) ->
            [F.String (depthToString b);
            F.String (modeToString mode);
            Print.formatDec (I.Null, D)] @ Fmt
        | (Prefix (Decl (G, D), Decl (M, mode), Decl (B, b)), Fmt) ->
            fmtPrefix'
              ((M.Prefix (G, M, B)),
                ([F.String ",";
                 F.Space;
                 F.Break;
                 F.String (depthToString b);
                 F.String (modeToString mode);
                 Print.formatDec (G, D)] @ Fmt)) in
      F.HVbox (fmtPrefix' (GM, []))
    let rec prefixToString (GM) = F.makestring_fmt (fmtPrefix GM)
    let rec stateToString (State (name, (Prefix (G, M, B) as GM), V)) =
      ((^) (((^) (name ^ ":\n") prefixToString GM) ^ "\n--------------\n")
         ClausePrint.clauseToString (G, V))
        ^ "\n\n"
    let rec sgnToString =
      function
      | M.SgnEmpty -> ""
      | ConDec (e, S) ->
          (^) (if (!Global.chatter) >= 4
               then (Print.conDecToString e) ^ "\n"
               else
                 if (!Global.chatter) >= 3
                 then (ClausePrint.conDecToString e) ^ "\n"
                 else "")
            sgnToString S
    let ((modeToString)(* depthToString is used to format splitting depth *)
      (* use explicitly quantified form *)(* use form without quantifiers, which is reparsable *))
      = modeToString
    let sgnToString = sgnToString
    let stateToString = stateToString
    let conDecToString = ClausePrint.conDecToString
  end ;;
