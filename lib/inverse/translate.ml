
module type TRANSLATE  =
  sig
    (** Translate a Twelf declaration to a Flewt declaration. *)
    val translate_condec : (IntSyn.cid * IntSyn.__ConDec) -> Syntax.dec
    (** Translate the currently loaded Twelf signature to Flewt *)
    val translate_signat : unit -> (Syntax.const * Syntax.dec) list
  end;;




module Translate : TRANSLATE =
  struct
    module __l = Lib
    module I = IntSyn
    module S = Syntax
    module Sig = S.Signat
    module C = ClausePrint
    module __d = Debug
    (* -------------------------------------------------------------------------- *)
    (*  Exceptions                                                                *)
    (* -------------------------------------------------------------------------- *)
    exception Translate of string 
    exception Trans1 of (S.const * I.__ConDec) 
    exception Fail_exp of (string * I.__Exp) 
    (* -------------------------------------------------------------------------- *)
    (*  Basic Translation                                                         *)
    (* -------------------------------------------------------------------------- *)
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
      | Root (H, S) -> S.Root ((translate_head H), (translate_spine S))
      | Lam (Dec (name, _), __u) ->
          S.Lam { var = name; body = (translate_exp __u) }
      | E -> raise (Fail_exp ("translate_exp: bad case", E))
    let rec translate_spine =
      function
      | I.Nil -> S.Nil
      | App (__u, S) -> S.App ((translate_exp __u), (translate_spine S))
      | _ -> raise (Translate "translate_spine: bad case")
    let rec translate_condec =
      function
      | (cid, ConDec (name, _, _, _, E, __u)) ->
          S.Decl
            {
              id = cid;
              name;
              exp = (translate_exp E);
              uni = (translate_uni __u)
            }
      | (cid, ConDef (name, _, _, __u, __v, I.Type, Anc (ex1, h, exa))) ->
          S.Def
            {
              id = cid;
              name;
              exp = (translate_exp __v);
              def = (translate_exp __u);
              height = h;
              root = (L.the exa);
              uni = S.Type
            }
      | (cid, AbbrevDef (name, mid, n, __u, __v, lev)) ->
          S.Abbrev
            {
              id = cid;
              name;
              exp = (translate_exp __v);
              def = (translate_exp __u);
              uni = (translate_uni lev)
            }
      | cdec -> raise (Trans1 cdec)
    (*     | translate_condec _ = raise Translate "translate_condec: bad case" *)
    let rec can_translate =
      function
      | ConDec _ -> true__
      | ConDef _ -> true__
      | AbbrevDef _ -> true__
      | _ -> false__
    let rec translate_signat' () =
      let n = L.fst (IntSyn.sgnSize ()) in
      let ns = L.upto (0, (n - 1)) in
      let cds = map IntSyn.sgnLookup ns in
      let cds' =
        L.filter (function | (id, dec) -> can_translate dec) (L.zip ns cds) in
      map (function | (c, e) as dec -> (c, (translate_condec dec))) cds'
    let rec translate_signat () =
      Timers.time Timers.translation translate_signat' ()
  end ;;
