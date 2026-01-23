module type THMPRINT  =
  sig
    module ThmSyn : THMSYN
    val tDeclToString : ThmSyn.tDecl_ -> string
    val callpatsToString : ThmSyn.callpats_ -> string
    val rDeclToString : ThmSyn.rDecl_ -> string
    val ROrderToString : ThmSyn.redOrder_ -> string
    val tabledDeclToString : ThmSyn.tabledDecl_ -> string
    val keepTableDeclToString : ThmSyn.keepTableDecl_ -> string
  end


module ThmPrint(ThmPrint:sig
                           module ThmSyn' : THMSYN
                           module Formatter : FORMATTER
                         end) : THMPRINT =
  struct
    module ThmSyn = ThmSyn'
    module L = ThmSyn
    module I = IntSyn
    module F = Formatter
    let rec fmtIds =
      begin function
      | [] -> []
      | n::[] -> [F.String n]
      | n::l_ -> [F.String n; F.String " "] @ (fmtIds l_) end
    let rec fmtParams =
      begin function
      | [] -> []
      | (Some n)::[] -> [F.String n]
      | (None)::[] -> [F.String "_"]
      | (Some n)::l_ -> [F.String n; F.String " "] @ (fmtParams l_)
      | (None)::l_ -> [F.String "_"; F.String " "] @ (fmtParams l_) end
  let rec fmtType (c, l_) =
    F.HVbox
      ([F.String (I.conDecName (I.sgnLookup c)); F.String " "] @
         (fmtParams l_))
  let rec fmtCallpats =
    begin function
    | [] -> []
    | (t_)::[] -> [F.String "("; fmtType t_; F.String ")"]
    | (t_)::l_ ->
        [F.String "("; fmtType t_; F.String ") "] @ (fmtCallpats l_) end
let rec fmtOptions =
  begin function
  | _::[] as l_ -> [F.HVbox (fmtIds l_)]
  | l_ -> [F.String "("; F.HVbox (fmtIds l_); F.String ") "] end
let rec fmtOrder =
  begin function
  | Varg (l_) ->
      (begin match l_ with
       | (h_)::[] -> fmtIds l_
       | _ -> [F.String "("; F.HVbox (fmtIds l_); F.String ")"] end)
  | Lex (l_) -> [F.String "{"; F.HVbox (fmtOrders l_); F.String "}"]
  | Simul (l_) -> [F.String "["; F.HVbox (fmtOrders l_); F.String "]"] end
let rec fmtOrders =
  begin function
  | [] -> []
  | (o_)::[] -> fmtOrder o_
  | (o_)::l_ -> (fmtOrder o_) @ ((::) (F.String " ") fmtOrders l_) end
let rec tDeclToString (TDecl (o_, Callpats (l_))) =
  F.makestring_fmt
    (F.HVbox ((fmtOrder o_) @ ((::) (F.String " ") fmtCallpats l_)))
let rec callpatsToString (Callpats (l_)) =
  F.makestring_fmt (F.HVbox (fmtCallpats l_))
let rec fmtROrder (RedOrder (p_, o_, o'_)) =
  begin match p_ with
  | L.Less -> (fmtOrder o_) @ ((::) (F.String " < ") fmtOrder o'_)
  | L.Leq -> (fmtOrder o_) @ ((::) (F.String " <= ") fmtOrder o'_)
  | L.Eq -> (fmtOrder o_) @ ((::) (F.String " = ") fmtOrder o'_) end
let rec ROrderToString (r_) = F.makestring_fmt (F.HVbox (fmtROrder r_))
let rec rDeclToString (RDecl (r_, Callpats (l_))) =
  F.makestring_fmt
    (F.HVbox ((fmtROrder r_) @ ((::) (F.String " ") fmtCallpats l_)))
let rec tabledDeclToString (TabledDecl cid) =
  F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
let rec keepTableDeclToString (KeepTableDecl cid) =
  F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
let tDeclToString = tDeclToString
let callpatsToString = callpatsToString
let ROrderToString = ROrderToString
let rDeclToString = rDeclToString
let tabledDeclToString = tabledDeclToString
let keepTableDeclToString = keepTableDeclToString end
