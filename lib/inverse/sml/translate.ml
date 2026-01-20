
module type TRANSLATE  =
  sig
    val translate_condec : IntSyn.cid -> IntSyn.__ConDec -> Syntax.dec
    val translate_signat : unit -> (Syntax.const * Syntax.dec) list
  end;;




module Translate : TRANSLATE =
  struct
    module L = Lib
    module I = IntSyn
    module S = Syntax
    module Sig = S.Signat
    module C = ClausePrint
    module D = Debug
    exception Translate of string 
    exception Trans1 of (S.const * I.__ConDec) 
    exception Fail_exp of (string * I.__Exp) 
    let rec translate_uni = function | I.Kind -> S.Kind | I.Type -> S.Type
    let rec translate_head =
      function
      | BVar i -> S.BVar i
      | Const c -> S.Const c
      | Def c -> S.Const c
      | _ -> raise (Translate "translate_head: bad case")
    let rec translate_depend =
      function
      | I.No -> S.No
      | I.Maybe -> S.Maybe
      | _ -> raise (Fail "translate_depend: bad case")
    let rec translate_exp =
      function
      | Uni uni -> S.Uni (translate_uni uni)
      | Pi ((Dec (name, __U1), depend), __U2) ->
          S.Pi
            {
              var = name;
              arg = (translate_exp __U1);
              depend = (translate_depend depend);
              body = (translate_exp __U2)
            }
      | Root (__H, __S) ->
          S.Root ((translate_head __H), (translate_spine __S))
      | Lam (Dec (name, _), __U) ->
          S.Lam { var = name; body = (translate_exp __U) }
      | __E -> raise (Fail_exp ("translate_exp: bad case", __E))
    let rec translate_spine =
      function
      | I.Nil -> S.Nil
      | App (__U, __S) -> S.App ((translate_exp __U), (translate_spine __S))
      | _ -> raise (Translate "translate_spine: bad case")
    let rec translate_condec __0__ __1__ =
      match (__0__, __1__) with
      | (cid, ConDec (name, _, _, _, __E, __U)) ->
          S.Decl
            {
              id = cid;
              name;
              exp = (translate_exp __E);
              uni = (translate_uni __U)
            }
      | (cid, ConDef (name, _, _, __U, __V, I.Type, Anc (ex1, h, exa))) ->
          S.Def
            {
              id = cid;
              name;
              exp = (translate_exp __V);
              def = (translate_exp __U);
              height = h;
              root = (L.the exa);
              uni = S.Type
            }
      | (cid, AbbrevDef (name, mid, n, __U, __V, lev)) ->
          S.Abbrev
            {
              id = cid;
              name;
              exp = (translate_exp __V);
              def = (translate_exp __U);
              uni = (translate_uni lev)
            }
      | cdec -> raise (Trans1 cdec)
    let rec can_translate =
      function
      | ConDec _ -> true
      | ConDef _ -> true
      | AbbrevDef _ -> true
      | _ -> false
    let rec translate_signat' () =
      let n = L.fst (IntSyn.sgnSize ()) in
      let ns = L.upto (0, (n - 1)) in
      let cds = map IntSyn.sgnLookup ns in
      let cds' =
        L.filter (fun id -> fun dec -> can_translate dec) (L.zip ns cds) in
      map (fun ((c, e) as dec) -> (c, (translate_condec dec))) cds'
    let rec translate_signat () =
      Timers.time Timers.translation translate_signat' ()
  end ;;
