
module type THMPRINT  =
  sig
    module ThmSyn : THMSYN
    val tDeclToString : ThmSyn.__TDecl -> string
    val callpatsToString : ThmSyn.__Callpats -> string
    val rDeclToString : ThmSyn.__RDecl -> string
    val ROrderToString : ThmSyn.__RedOrder -> string
    val tabledDeclToString : ThmSyn.__TabledDecl -> string
    val keepTableDeclToString : ThmSyn.__KeepTableDecl -> string
  end;;




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
      | n::__L -> [F.String n; F.String " "] @ (fmtIds __L)
    let rec fmtParams =
      function
      | nil -> []
      | (Some n)::nil -> [F.String n]
      | (None)::nil -> [F.String "_"]
      | (Some n)::__L -> [F.String n; F.String " "] @ (fmtParams __L)
      | (None)::__L -> [F.String "_"; F.String " "] @ (fmtParams __L)
    let rec fmtType c (__L) =
      F.HVbox
        ([F.String (I.conDecName (I.sgnLookup c)); F.String " "] @
           (fmtParams __L))
    let rec fmtCallpats =
      function
      | nil -> []
      | (__T)::nil -> [F.String "("; fmtType __T; F.String ")"]
      | (__T)::__L ->
          [F.String "("; fmtType __T; F.String ") "] @ (fmtCallpats __L)
    let rec fmtOptions =
      function
      | _::nil as L -> [F.HVbox (fmtIds __L)]
      | __L -> [F.String "("; F.HVbox (fmtIds __L); F.String ") "]
    let rec fmtOrder =
      function
      | Varg (__L) ->
          (match __L with
           | (__H)::nil -> fmtIds __L
           | _ -> [F.String "("; F.HVbox (fmtIds __L); F.String ")"])
      | Lex (__L) -> [F.String "{"; F.HVbox (fmtOrders __L); F.String "}"]
      | Simul (__L) -> [F.String "["; F.HVbox (fmtOrders __L); F.String "]"]
    let rec fmtOrders =
      function
      | nil -> nil
      | (__O)::nil -> fmtOrder __O
      | (__O)::__L -> (fmtOrder __O) @ ((::) (F.String " ") fmtOrders __L)
    let rec tDeclToString (TDecl (__O, Callpats (__L))) =
      F.makestring_fmt
        (F.HVbox ((fmtOrder __O) @ ((::) (F.String " ") fmtCallpats __L)))
    let rec callpatsToString (Callpats (__L)) =
      F.makestring_fmt (F.HVbox (fmtCallpats __L))
    let rec fmtROrder (RedOrder (__P, __O, __O')) =
      match __P with
      | L.Less -> (fmtOrder __O) @ ((::) (F.String " < ") fmtOrder __O')
      | L.Leq -> (fmtOrder __O) @ ((::) (F.String " <= ") fmtOrder __O')
      | L.Eq -> (fmtOrder __O) @ ((::) (F.String " = ") fmtOrder __O')
    let rec ROrderToString (__R) = F.makestring_fmt (F.HVbox (fmtROrder __R))
    let rec rDeclToString (RDecl (__R, Callpats (__L))) =
      F.makestring_fmt
        (F.HVbox ((fmtROrder __R) @ ((::) (F.String " ") fmtCallpats __L)))
    let rec tabledDeclToString (TabledDecl cid) =
      F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
    let rec keepTableDeclToString (KeepTableDecl cid) =
      F.makestring_fmt (F.HVbox [F.String (I.conDecName (I.sgnLookup cid))])
    let tDeclToString = tDeclToString
    let callpatsToString = callpatsToString
    let ROrderToString = ROrderToString
    let rDeclToString = rDeclToString
    let tabledDeclToString = tabledDeclToString
    let keepTableDeclToString = keepTableDeclToString
  end ;;
