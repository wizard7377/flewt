module type TRANSLATE  =
  sig
    val translate_condec : (IntSyn.cid * IntSyn.conDec_) -> Syntax.dec
    val translate_signat : unit -> (Syntax.const * Syntax.dec) list
  end


module Translate : TRANSLATE =
  struct
    module L = Lib
    module I = IntSyn
    module S = Syntax
    module Sig = S.Signat
    module C = ClausePrint
    module D = Debug
    exception Translate of string 
    exception Trans1 of (S.const * I.conDec_) 
    exception Fail_exp of (string * I.exp_) 
    let rec translate_uni =
      begin function | I.Kind -> S.Kind | I.Type -> S.Type end
    let rec translate_head =
      begin function
      | BVar i -> S.BVar i
      | Const c -> S.Const c
      | Def c -> S.Const c
      | _ -> raise (Translate "translate_head: bad case") end
  let rec translate_depend =
    begin function
    | I.No -> S.No
    | I.Maybe -> S.Maybe
    | _ -> raise (Fail "translate_depend: bad case") end
let rec translate_exp =
  begin function
  | Uni uni -> S.Uni (translate_uni uni)
  | Pi ((Dec (name, u1_), depend), u2_) ->
      S.Pi
        {
          var = name;
          arg = (translate_exp u1_);
          depend = (translate_depend depend);
          body = (translate_exp u2_)
        }
  | Root (h_, s_) -> S.Root ((translate_head h_), (translate_spine s_))
  | Lam (Dec (name, _), u_) ->
      S.Lam { var = name; body = (translate_exp u_) }
  | e_ -> raise (Fail_exp ("translate_exp: bad case", e_)) end
let rec translate_spine =
  begin function
  | I.Nil -> S.Nil
  | App (u_, s_) -> S.App ((translate_exp u_), (translate_spine s_))
  | _ -> raise (Translate "translate_spine: bad case") end
let rec translate_condec =
  begin function
  | (cid, ConDec (name, _, _, _, e_, u_)) ->
      S.Decl
        { id = cid; name; exp = (translate_exp e_); uni = (translate_uni u_)
        }
  | (cid, ConDef (name, _, _, u_, v_, I.Type, Anc (ex1, h, exa))) ->
      S.Def
        {
          id = cid;
          name;
          exp = (translate_exp v_);
          def = (translate_exp u_);
          height = h;
          root = (L.the exa);
          uni = S.Type
        }
  | (cid, AbbrevDef (name, mid, n, u_, v_, lev)) ->
      S.Abbrev
        {
          id = cid;
          name;
          exp = (translate_exp v_);
          def = (translate_exp u_);
          uni = (translate_uni lev)
        }
  | cdec -> raise (Trans1 cdec) end
let rec can_translate =
  begin function
  | ConDec _ -> true
  | ConDef _ -> true
  | AbbrevDef _ -> true
  | _ -> false end
let rec translate_signat' () =
  let n = L.fst (IntSyn.sgnSize ()) in
  let ns = L.upto (0, (n - 1)) in
  let cds = map IntSyn.sgnLookup ns in
  let cds' = L.filter (begin function | (id, dec) -> can_translate dec end)
    (L.zip ns cds) in
  map (begin function | (c, e) as dec -> (c, (translate_condec dec)) end)
    cds'
let rec translate_signat () =
  Timers.time Timers.translation translate_signat' () end
