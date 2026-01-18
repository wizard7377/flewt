
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
    module __l = ThmSyn
    module I = IntSyn
    module F = Formatter
    let rec fmtIds =
      function
      | nil -> []
      | n::nil -> [F.String n]
      | n::__l -> [F.String n; F.String " "] @ (fmtIds __l)
    let rec fmtParams =
      function
      | nil -> []
      | (Some n)::nil -> [F.String n]
      | (None)::nil -> [F.String "_"]
      | (Some n)::__l -> [F.String n; F.String " "] @ (fmtParams __l)
      | (None)::__l -> [F.String "_"; F.String " "] @ (fmtParams __l)
    let rec fmtType (c, __l) =
      F.hVbox
        ([F.String (I.conDecName (I.sgnLookup c)); F.String " "] @
           (fmtParams __l))
    let rec fmtCallpats =
      function
      | nil -> []
      | (T)::nil -> [F.String "("; fmtType T; F.String ")"]
      | (T)::__l -> [F.String "("; fmtType T; F.String ") "] @ (fmtCallpats __l)
    let rec fmtOptions =
      function
      | _::nil as __l -> [F.hVbox (fmtIds __l)]
      | __l -> [F.String "("; F.hVbox (fmtIds __l); F.String ") "]
    let rec fmtOrder =
      function
      | Varg (__l) ->
          (match __l with
           | (H)::nil -> fmtIds __l
           | _ -> [F.String "("; F.hVbox (fmtIds __l); F.String ")"])
      | Lex (__l) -> [F.String "{"; F.hVbox (fmtOrders __l); F.String "}"]
      | Simul (__l) -> [F.String "["; F.hVbox (fmtOrders __l); F.String "]"]
    let rec fmtOrders =
      function
      | nil -> nil
      | (O)::nil -> fmtOrder O
      | (O)::__l -> (fmtOrder O) @ ((::) (F.String " ") fmtOrders __l)
    let rec tDeclToString (TDecl (O, Callpats (__l))) =
      F.makestring_fmt
        (F.hVbox ((fmtOrder O) @ ((::) (F.String " ") fmtCallpats __l)))
    let rec callpatsToString (Callpats (__l)) =
      F.makestring_fmt (F.hVbox (fmtCallpats __l))
    let rec fmtROrder (RedOrder (P, O, O')) =
      match P with
      | L.Less -> (fmtOrder O) @ ((::) (F.String " < ") fmtOrder O')
      | L.Leq -> (fmtOrder O) @ ((::) (F.String " <= ") fmtOrder O')
      | L.Eq -> (fmtOrder O) @ ((::) (F.String " = ") fmtOrder O')
    let rec ROrderToString (R) = F.makestring_fmt (F.hVbox (fmtROrder R))
    let rec rDeclToString (RDecl (R, Callpats (__l))) =
      F.makestring_fmt
        (F.hVbox ((fmtROrder R) @ ((::) (F.String " ") fmtCallpats __l)))
    let rec tabledDeclToString (TabledDecl cid) =
      F.makestring_fmt (F.hVbox [F.String (I.conDecName (I.sgnLookup cid))])
    let rec keepTableDeclToString (KeepTableDecl cid) =
      F.makestring_fmt (F.hVbox [F.String (I.conDecName (I.sgnLookup cid))])
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
