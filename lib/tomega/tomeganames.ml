
module type TOMEGANAMES  =
  sig val decName : Tomega.__Dec IntSyn.__Ctx -> Tomega.__Dec -> Tomega.__Dec
  end;;




module TomegaNames : TOMEGANAMES =
  struct
    module T = Tomega
    module I = IntSyn
    let rec decName __0__ __1__ =
      match (__0__, __1__) with
      | (Psi, UDec (__D)) -> T.UDec (Names.decName ((T.coerceCtx Psi), __D))
      | (Psi, PDec (x, __F, TC1, TC2)) ->
          let NDec x' = Names.decName ((T.coerceCtx Psi), (I.NDec x)) in
          T.PDec (x', __F, TC1, TC2)
  end ;;
