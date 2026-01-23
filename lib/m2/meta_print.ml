module type METAPRINT  =
  sig
    module MetaSyn : METASYN
    val stateToString : MetaSyn.state_ -> string
    val sgnToString : MetaSyn.sgn_ -> string
    val modeToString : MetaSyn.mode_ -> string
    val conDecToString : IntSyn.conDec_ -> string
  end


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
    let rec modeToString = begin function | M.Top -> "+" | M.Bot -> "-" end
    let rec depthToString b = if b <= 0 then begin "" end
      else begin Int.toString b end
let rec fmtPrefix (GM) =
  let rec fmtPrefix' =
    begin function
    | (Prefix (I.Null, I.Null, I.Null), Fmt) -> Fmt
    | (Prefix (Decl (I.Null, d_), Decl (I.Null, mode), Decl (I.Null, b)),
       Fmt) ->
        [F.String (depthToString b);
        F.String (modeToString mode);
        Print.formatDec (I.Null, d_)] @ Fmt
    | (Prefix (Decl (g_, d_), Decl (m_, mode), Decl (b_, b)), Fmt) ->
        fmtPrefix'
          ((M.Prefix (g_, m_, b_)),
            ([F.String ",";
             F.Space;
             F.Break;
             F.String (depthToString b);
             F.String (modeToString mode);
             Print.formatDec (g_, d_)] @ Fmt)) end in
F.HVbox (fmtPrefix' (GM, []))
let rec prefixToString (GM) = F.makestring_fmt (fmtPrefix GM)
let rec stateToString (State (name, (Prefix (g_, m_, b_) as GM), v_)) =
  ((^) (((^) (name ^ ":\n") prefixToString GM) ^ "\n--------------\n")
     ClausePrint.clauseToString (g_, v_))
    ^ "\n\n"
let rec sgnToString =
  begin function
  | M.SgnEmpty -> ""
  | ConDec (e, s_) ->
      (^) ((if !Global.chatter >= 4
            then begin (Print.conDecToString e) ^ "\n" end
        else begin
          ((if !Global.chatter >= 3
            then begin (ClausePrint.conDecToString e) ^ "\n" end
          else begin "" end)
      (* use form without quantifiers, which is reparsable *)) end)
  (* use explicitly quantified form *)) sgnToString s_ end
let modeToString = modeToString
let sgnToString = sgnToString
let stateToString = stateToString
let conDecToString = ClausePrint.conDecToString end
