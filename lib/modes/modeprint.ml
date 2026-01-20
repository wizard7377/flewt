
module type MODEPRINT  =
  sig
    val modeToString : IntSyn.cid -> ModeSyn.__ModeSpine -> string
    val modesToString : (IntSyn.cid * ModeSyn.__ModeSpine) list -> string
  end;;




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
      function
      | M.Plus -> "+"
      | M.Star -> "*"
      | M.Minus -> "-"
      | M.Minus1 -> "-1"
    let rec argToString (Marg (m, _)) = modeToString m
    let rec nameDec __0__ __1__ =
      match (__0__, __1__) with
      | (Dec (_, __V), Marg (_, (Some _ as name))) -> I.Dec (name, __V)
      | (__D, Marg (_, NONE)) -> __D
    let rec makeSpine (__G) =
      let rec makeSpine' __2__ __3__ __4__ =
        match (__2__, __3__, __4__) with
        | (I.Null, _, __S) -> __S
        | (Decl (__G, _), k, __S) ->
            makeSpine'
              (__G, (k + 1), (I.App ((I.Root ((I.BVar k), I.Nil)), __S))) in
      makeSpine' (__G, 1, I.Nil)
    let rec fmtModeDec cid mS =
      let __V = I.constType cid in
      let rec fmtModeDec' __5__ __6__ __7__ =
        match (__5__, __6__, __7__) with
        | (__G, _, M.Mnil) ->
            [F.String "(";
            P.formatExp (__G, (I.Root ((I.Const cid), (makeSpine __G))));
            F.String ")"]
        | (__G, Pi ((__D, _), __V'), Mapp (marg, __S)) ->
            let __D' = nameDec (__D, marg) in
            let D'' = Names.decEName (__G, __D') in
            [F.String (argToString marg);
            F.String "{";
            P.formatDec (__G, D'');
            F.String "}";
            F.Break] @ (fmtModeDec' ((I.Decl (__G, D'')), __V', __S)) in
      F.HVbox (fmtModeDec' (I.Null, __V, mS))
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
