
(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)
module type MODEPRINT  =
  sig
    (*! structure ModeSyn : MODESYN !*)
    val modeToString : (IntSyn.cid * ModeSyn.__ModeSpine) -> string
    val modesToString : (IntSyn.cid * ModeSyn.__ModeSpine) list -> string
  end;;




(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)
module ModePrint(ModePrint:sig
                             (*! structure ModeSyn' : MODESYN !*)
                             module Names : NAMES
                             module Formatter : FORMATTER
                             (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                             module Print : PRINT
                           end) : MODEPRINT =
  struct
    (* structure ModeSyn = ModeSyn' *)
    module I = IntSyn
    module M = ModeSyn
    module F = Formatter
    module P = Print
    let rec modeToString =
      function
      | M.Plus -> "+"
      | M.Star -> "*"
      | M.Minus -> "-"
      | M.Minus1 -> "-1"
    let rec argToString (Marg (m, _)) = modeToString m
    let rec nameDec =
      function
      | (Dec (_, V), Marg (_, (SOME _ as name))) -> I.Dec (name, V)
      | (D, Marg (_, NONE)) -> D
    let rec makeSpine (G) =
      let rec makeSpine' =
        function
        | (I.Null, _, S) -> S
        | (Decl (G, _), k, S) ->
            makeSpine'
              (G, (k + 1), (I.App ((I.Root ((I.BVar k), I.Nil)), S))) in
      makeSpine' (G, 1, I.Nil)
    let rec fmtModeDec (cid, mS) =
      let V = I.constType cid in
      let rec fmtModeDec' =
        function
        | (G, _, M.Mnil) ->
            [F.String "(";
            P.formatExp (G, (I.Root ((I.Const cid), (makeSpine G))));
            F.String ")"]
        | (G, Pi ((D, _), V'), Mapp (marg, S)) ->
            let D' = nameDec (D, marg) in
            let D'' = Names.decEName (G, D') in
            [F.String (argToString marg);
            F.String "{";
            P.formatDec (G, D'');
            F.String "}";
            F.Break] @ (fmtModeDec' ((I.Decl (G, D'')), V', S)) in
      F.HVbox (fmtModeDec' (I.Null, V, mS))
    let rec fmtModeDecs =
      function
      | (cid, mS)::nil -> (fmtModeDec (cid, mS)) :: nil
      | (cid, mS)::mdecs ->
          (::) ((fmtModeDec (cid, mS)) :: F.Break) fmtModeDecs mdecs
    let rec modeToString cM = F.makestring_fmt (fmtModeDec cM)
    let rec modesToString mdecs =
      F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
    let modeToString = modeToString
    let modesToString = modesToString
  end ;;
