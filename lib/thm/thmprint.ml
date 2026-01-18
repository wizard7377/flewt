
(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
module type THMPRINT  =
  sig
    module ThmSyn : THMSYN
    val tDeclToString : ThmSyn.__TDecl -> string
    val callpatsToString : ThmSyn.__Callpats -> string
    val rDeclToString : ThmSyn.__RDecl -> string
    (* -bp *)
    val ROrderToString : ThmSyn.__RedOrder -> string
    (* -bp *)
    val tabledDeclToString : ThmSyn.__TabledDecl -> string
    (* -bp *)
    val keepTableDeclToString : ThmSyn.__KeepTableDecl -> string
  end;;




(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
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
      function
      | nil -> []
      | n::nil -> [F.String n]
      | n::L -> [F.String n; F.String " "] @ (fmtIds L)
    let rec fmtParams =
      function
      | nil -> []
      | (SOME n)::nil -> [F.String n]
      | (NONE)::nil -> [F.String "_"]
      | (SOME n)::L -> [F.String n; F.String " "] @ (fmtParams L)
      | (NONE)::L -> [F.String "_"; F.String " "] @ (fmtParams L)
    let rec fmtType (c, L) =
      F.HVbox
        ([F.String (I.conDecName (I.sgnLookup c)); F.String " "] @
           (fmtParams L))
    let rec fmtCallpats =
      function
      | nil -> []
      | (T)::nil -> [F.String "("; fmtType T; F.String ")"]
      | (T)::L -> [F.String "("; fmtType T; F.String ") "] @ (fmtCallpats L)
    let rec fmtOptions =
      function
      | _::nil as L -> [F.HVbox (fmtIds L)]
      | L -> [F.String "("; F.HVbox (fmtIds L); F.String ") "]
    let rec fmtOrder =
      function
      | Varg (L) ->
          (match L with
           | (H)::nil -> fmtIds L
           | _ -> [F.String "("; F.HVbox (fmtIds L); F.String ")"])
      | Lex (L) -> [F.String "{"; F.HVbox (fmtOrders L); F.String "}"]
      | Simul (L) -> [F.String "["; F.HVbox (fmtOrders L); F.String "]"]
    let rec fmtOrders =
      function
      | nil -> nil
      | (O)::nil -> fmtOrder O
      | (O)::L -> (fmtOrder O) @ ((::) (F.String " ") fmtOrders L)
    let rec tDeclToString (TDecl (O, Callpats (L))) =
      F.makestring_fmt
        (F.HVbox ((fmtOrder O) @ ((::) (F.String " ") fmtCallpats L)))
    let rec callpatsToString (Callpats (L)) =
      F.makestring_fmt (F.HVbox (fmtCallpats L))
    let rec fmtROrder (RedOrder (P, O, O')) =
      match P with
      | L.Less -> (fmtOrder O) @ ((::) (F.String " < ") fmtOrder O')
      | L.Leq -> (fmtOrder O) @ ((::) (F.String " <= ") fmtOrder O')
      | L.Eq -> (fmtOrder O) @ ((::) (F.String " = ") fmtOrder O')
    let rec ROrderToString (R) = F.makestring_fmt (F.HVbox (fmtROrder R))
    let rec rDeclToString (RDecl (R, Callpats (L))) =
      F.makestring_fmt
        (F.HVbox ((fmtROrder R) @ ((::) (F.String " ") fmtCallpats L)))
    let rec tabledDeclToString (TabledDecl cid) =
      F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
    let rec keepTableDeclToString (KeepTableDecl cid) =
      F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
    (* -bp *)
    let tDeclToString = tDeclToString
    let callpatsToString = callpatsToString
    let ROrderToString = ROrderToString
    (* -bp *)
    let rDeclToString = rDeclToString
    (* -bp *)
    let tabledDeclToString = tabledDeclToString
    let keepTableDeclToString = keepTableDeclToString
  end ;;
