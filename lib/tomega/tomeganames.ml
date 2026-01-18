
(* Naming *)
(* Author: Carsten Schuermann *)
module type TOMEGANAMES  =
  sig
    val decName : (Tomega.__Dec IntSyn.__Ctx * Tomega.__Dec) -> Tomega.__Dec
  end;;




(* Naming *)
(* Author: Carsten Schuermann *)
module TomegaNames : TOMEGANAMES =
  struct
    module T = Tomega
    module I = IntSyn
    let rec decName =
      function
      | (Psi, UDec (D)) -> T.UDec (Names.decName ((T.coerceCtx Psi), D))
      | (Psi, PDec (x, F, TC1, TC2)) ->
          let NDec x' = Names.decName ((T.coerceCtx Psi), (I.NDec x)) in
          T.PDec (x', F, TC1, TC2)
  end ;;
