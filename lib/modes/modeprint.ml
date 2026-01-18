
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
      | (Dec (_, __v), Marg (_, (Some _ as name))) -> I.Dec (name, __v)
      | (__d, Marg (_, None)) -> __d
    let rec makeSpine (__g) =
      let rec makeSpine' =
        function
        | (I.Null, _, S) -> S
        | (Decl (__g, _), k, S) ->
            makeSpine'
              (__g, (k + 1), (I.App ((I.Root ((I.BVar k), I.Nil)), S))) in
      makeSpine' (__g, 1, I.Nil)
    let rec fmtModeDec (cid, mS) =
      let __v = I.constType cid in
      let rec fmtModeDec' =
        function
        | (__g, _, M.Mnil) ->
            [F.String "(";
            P.formatExp (__g, (I.Root ((I.Const cid), (makeSpine __g))));
            F.String ")"]
        | (__g, Pi ((__d, _), __v'), Mapp (marg, S)) ->
            let __d' = nameDec (__d, marg) in
            let __d'' = Names.decEName (__g, __d') in
            [F.String (argToString marg);
            F.String "{";
            P.formatDec (__g, __d'');
            F.String "}";
            F.Break] @ (fmtModeDec' ((I.Decl (__g, __d'')), __v', S)) in
      F.hVbox (fmtModeDec' (I.Null, __v, mS))
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
