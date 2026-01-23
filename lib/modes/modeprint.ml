module type MODEPRINT  =
  sig
    val modeToString : (IntSyn.cid * ModeSyn.modeSpine_) -> string
    val modesToString : (IntSyn.cid * ModeSyn.modeSpine_) list -> string
  end


module ModePrint(ModePrint:sig
                             module Names : NAMES
                             module Formatter : FORMATTER
                             module Print : PRINT
                           end) : MODEPRINT =
  struct
    module I = IntSyn
    module M = ModeSyn
    module F = Formatter
    module P = Print
    let rec modeToString =
      begin function
      | M.Plus -> "+"
      | M.Star -> "*"
      | M.Minus -> "-"
      | M.Minus1 -> "-1" end
    let rec argToString (Marg (m, _)) = modeToString m
    let rec nameDec =
      begin function
      | (Dec (_, v_), Marg (_, (Some _ as name))) -> I.Dec (name, v_)
      | (d_, Marg (_, None)) -> d_ end
  let rec makeSpine (g_) =
    let rec makeSpine' =
      begin function
      | (I.Null, _, s_) -> s_
      | (Decl (g_, _), k, s_) ->
          makeSpine'
            (g_, (k + 1), (I.App ((I.Root ((I.BVar k), I.Nil)), s_))) end in
  makeSpine' (g_, 1, I.Nil)
let rec fmtModeDec (cid, mS) =
  let v_ = I.constType cid in
  let rec fmtModeDec' =
    begin function
    | (g_, _, M.Mnil) ->
        [F.String "(";
        P.formatExp (g_, (I.Root ((I.Const cid), (makeSpine g_))));
        F.String ")"]
    | (g_, Pi ((d_, _), v'_), Mapp (marg, s_)) ->
        let d'_ = nameDec (d_, marg) in
        let D'' = Names.decEName (g_, d'_) in
        [F.String (argToString marg);
        F.String "{";
        P.formatDec (g_, D'');
        F.String "}";
        F.Break] @ (fmtModeDec' ((I.Decl (g_, D'')), v'_, s_)) end in
  F.HVbox (fmtModeDec' (I.Null, v_, mS))
let rec fmtModeDecs =
  begin function
  | (cid, mS)::[] -> (fmtModeDec (cid, mS)) :: []
  | (cid, mS)::mdecs ->
      (::) ((fmtModeDec (cid, mS)) :: F.Break) fmtModeDecs mdecs end
let rec modeToString cM = F.makestring_fmt (fmtModeDec cM)
let rec modesToString mdecs =
  F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
let modeToString = modeToString
let modesToString = modesToString end
