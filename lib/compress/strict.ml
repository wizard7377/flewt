module Strict =
  struct
    open Syntax
    exception EtaContract 
    let rec eta_contract_var =
      begin function
      | Elt t -> eta_contract_var' 0 t
      | _ -> raise EtaContract end
    let rec eta_contract_var' arg__2 arg__3 =
      begin match (arg__2, arg__3) with
      | (n, ATerm (ARoot (Var n', s))) ->
          let s' = map eta_contract_var s in
          let rec decreasing_list arg__0 arg__1 =
            begin match (arg__0, arg__1) with
            | (0, []) -> true
            | (n, h::tl) -> ((n - 1) = h) && (decreasing_list (n - 1) tl)
            | (_, _) -> false end in
          if decreasing_list n s' then begin n' - n end
            else begin raise EtaContract end
    | (n, NTerm (Lam t)) -> eta_contract_var' (n + 1) t
    | (_, _) -> raise EtaContract end
let rec pattern_spine' =
  begin function
  | (d_, []) -> true
  | (d_, n::s) ->
      let rec isn x = x = n in
      let rec hasn s = List.exists isn s in
      (hasn d_) && ((not (hasn s)) && (pattern_spine' (d_, s))) end
let rec pattern_spine (d_, s) =
  begin try pattern_spine' (d_, (map eta_contract_var s))
  with | EtaContract -> false end
let rec spine_occ arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (n, (d_, [])) -> false
  | (n, (d_, (Elt t)::s)) -> (term_occ n (d_, t)) || (spine_occ n (d_, s))
  | (n, (d_, (AElt t)::s)) -> (aterm_occ n (d_, t)) || (spine_occ n (d_, s))
  | (n, (d_, (Ascribe (t, a))::s)) ->
      (nterm_occ n (d_, t)) ||
        ((type_occ n (d_, a)) || (spine_occ n (d_, s)))
  | (n, (d_, (Omit)::s)) -> false end
let rec term_occ arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (n, (d_, NTerm t)) -> nterm_occ n (d_, t)
  | (n, (d_, ATerm t)) -> aterm_occ n (d_, t) end
let rec nterm_occ arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (n, (d_, Lam t)) ->
      term_occ (n + 1) ((0 :: (map (begin function | x -> x + 1 end) d_)), t)
  | (n, (d_, NRoot (h, s))) -> root_occ n (d_, h, s) end
let rec aterm_occ arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (n, (d_, ARoot (h, s))) -> root_occ n (d_, h, s)
  | (n, (d_, ERoot _)) -> false end
let rec root_occ arg__12 arg__13 =
  begin match (arg__12, arg__13) with
  | (n, (d_, Var n', s)) -> ((if n = n' then begin pattern_spine (d_, s) end
      else begin (List.exists (begin function | x -> x = n' end) d_) &&
        (spine_occ n (d_, s)) end)
  (* n = n' precludes n in D, right? *))
| (n, (d_, Const n', s)) -> spine_occ n (d_, s) end
let rec type_occ arg__14 arg__15 =
  begin match (arg__14, arg__15) with
  | (n, (d_, TRoot (_, s))) -> spine_occ n (d_, s)
  | (n, (d_, TPi (_, a, b))) ->
      (((type_occ n (d_, a)) ||
          (type_occ (n + 1)
             ((0 :: (map (begin function | x -> x + 1 end) d_)), b)))
  (* PERF: suspend these context shifts, do them at the end *)) end
let rec check_strict_type' arg__16 arg__17 arg__18 =
  begin match (arg__16, arg__17, arg__18) with
  | (n, p, TRoot (n', s)) -> if p then begin false end
      else begin spine_occ n ([], s) end
  | (n, p, TPi (PLUS, a, b)) ->
      (type_occ n ([], a)) || (check_strict_type' (n + 1) p b)
  | (n, p, TPi (_, a, b)) -> check_strict_type' (n + 1) p b end
let rec check_strict_kind' arg__19 arg__20 =
  begin match (arg__19, arg__20) with
  | (n, Type) -> false
  | (n, KPi (PLUS, a, k)) ->
      (type_occ n ([], a)) || (check_strict_kind' (n + 1) k)
  | (n, KPi (_, a, k)) -> check_strict_kind' (n + 1) k end
let rec check_strict_type p b = check_strict_type' 0 p b
let rec check_strict_kind k = check_strict_kind' 0 k
end