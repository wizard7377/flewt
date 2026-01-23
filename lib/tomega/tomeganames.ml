module type TOMEGANAMES  =
  sig val decName : (Tomega.dec_ IntSyn.ctx_ * Tomega.dec_) -> Tomega.dec_
  end


module TomegaNames : TOMEGANAMES =
  struct
    module T = Tomega
    module I = IntSyn
    let rec decName =
      begin function
      | (Psi, UDec (d_)) -> T.UDec (Names.decName ((T.coerceCtx Psi), d_))
      | (Psi, PDec (x, f_, TC1, TC2)) ->
          let NDec x' = Names.decName ((T.coerceCtx Psi), (I.NDec x)) in
          T.PDec (x', f_, TC1, TC2) end end 