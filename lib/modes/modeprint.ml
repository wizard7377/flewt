
module type MODEPRINT  =
  sig
    val modeToString :
      (IntSyn.cid * ModeSyn.__ModeSpine) ->
        ((string)(*! structure ModeSyn : MODESYN !*)
        (* Author: Carsten Schuermann *)(* Printing Mode Declarations *))
    val modesToString : (IntSyn.cid * ModeSyn.__ModeSpine) list -> string
  end;;




module ModePrint(ModePrint:sig
                             module Names : NAMES
                             module Formatter : FORMATTER
                             module Print :
                             ((PRINT)(* Printing Mode Declarations *)
                             (* Author: Carsten Schuermann *)(*! structure ModeSyn' : MODESYN !*)
                             (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*))
                           end) : MODEPRINT =
  struct
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
    let rec makeSpine (g) =
      let makeSpine' =
        function
        | (I.Null, _, S) -> S
        | (Decl (g, _), k, S) ->
            makeSpine'
              (g, (k + 1), (I.App ((I.Root ((I.BVar k), I.Nil)), S))) in
      makeSpine' (g, 1, I.Nil)
    let rec fmtModeDec (cid, mS) =
      let V = I.constType cid in
      let fmtModeDec' =
        function
        | (g, _, M.Mnil) ->
            [F.String "(";
            P.formatExp (g, (I.Root ((I.Const cid), (makeSpine g))));
            F.String ")"]
        | (g, Pi ((D, _), V'), Mapp (marg, S)) ->
            let D' = nameDec (D, marg) in
            let D'' = Names.decEName (g, D') in
            [F.String (argToString marg);
            F.String "{";
            P.formatDec (g, D'');
            F.String "}";
            F.Break] @ (fmtModeDec' ((I.Decl (g, D'')), V', S)) in
      F.HVbox (fmtModeDec' (I.Null, V, mS))
    let rec fmtModeDecs =
      function
      | (cid, mS)::nil -> (fmtModeDec (cid, mS)) :: nil
      | (cid, mS)::mdecs ->
          (::) ((fmtModeDec (cid, mS)) :: F.Break) fmtModeDecs mdecs
    let rec modeToString cM = F.makestring_fmt (fmtModeDec cM)
    let rec modesToString mdecs =
      F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
    let ((modeToString)(*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
      (* structure ModeSyn = ModeSyn' *)) = modeToString
    let modesToString = modesToString
  end ;;
