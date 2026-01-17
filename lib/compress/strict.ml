
module Strict =
  struct
    open Syntax
    exception EtaContract 
    let rec eta_contract_var =
      function
      | Elt
          ((t)(* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *))
          -> eta_contract_var' 0 t
      | _ -> raise EtaContract
    let rec eta_contract_var' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, ATerm (ARoot (Var n', s))) ->
          let s' = map eta_contract_var s in
          let decreasing_list arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (0, []) -> true__
            | (n, h::tl) -> ((n - 1) = h) && (decreasing_list (n - 1) tl)
            | (_, _) -> false__ in
          if decreasing_list n s' then n' - n else raise EtaContract
      | (n, NTerm (Lam t)) -> eta_contract_var' (n + 1) t
      | (_, _) -> raise EtaContract
    let rec pattern_spine' =
      function
      | (D, []) -> true__
      | (D, n::s) ->
          let isn x = x = n in
          let hasn s = List.exists isn s in
          (hasn D) && ((not (hasn s)) && (pattern_spine' (D, s)))
    let rec pattern_spine (D, s) =
      try pattern_spine' (D, (map eta_contract_var s))
      with | EtaContract -> false__
    let rec spine_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (D, nil)) -> false__
      | (n, (D, (Elt t)::s)) -> (term_occ n (D, t)) || (spine_occ n (D, s))
      | (n, (D, (AElt t)::s)) -> (aterm_occ n (D, t)) || (spine_occ n (D, s))
      | (n, (D, (Ascribe (t, a))::s)) ->
          (nterm_occ n (D, t)) ||
            ((type_occ n (D, a)) || (spine_occ n (D, s)))
      | (n, (D, (Omit)::s)) -> false__
    let rec term_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((n)(* Omit invalidates all strict
					    occurrences to the right *)),
         (D, NTerm t)) -> nterm_occ n (D, t)
      | (n, (D, ATerm t)) -> aterm_occ n (D, t)
    let rec nterm_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((n)(* PERF: suspend these context shifts, do them at the end *)),
         (D, Lam t)) ->
          term_occ (n + 1) ((0 :: (map (function | x -> x + 1) D)), t)
      | (n, (D, NRoot (h, s))) -> root_occ n (D, h, s)
    let rec aterm_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (D, ARoot (h, s))) -> root_occ n (D, h, s)
      | (n, (D, ERoot _)) -> false__
    let rec root_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (D, Var n', s)) ->
          if n = n'
          then pattern_spine (D, s)
          else
            (List.exists (function | x -> x = n') D) &&
              (spine_occ ((n)
                 (* n = n' precludes n in D, right? *))
                 (D, s))
      | (n, (D, Const n', s)) -> spine_occ n (D, s)
    let rec type_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (D, TRoot (_, s))) -> spine_occ n (D, s)
      | (n, (D, TPi (_, a, b))) ->
          (type_occ n (D, a)) ||
            (type_occ
               (n + ((1)
                  (* PERF: suspend these context shifts, do them at the end *)))
               ((0 :: (map (function | x -> x + 1) D)), b))
    let rec check_strict_type' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (((n)(* toplevel strictness judgments *)), p, TRoot
         (n', s)) -> if p then false__ else spine_occ n ([], s)
      | (n, p, TPi (PLUS, a, b)) ->
          (type_occ n ([], a)) || (check_strict_type' (n + 1) p b)
      | (n, p, TPi (_, a, b)) -> check_strict_type' (n + 1) p b
    let rec check_strict_kind' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, Type) -> false__
      | (n, KPi (PLUS, a, k)) ->
          (type_occ n ([], a)) || (check_strict_kind' (n + 1) k)
      | (n, KPi (_, a, k)) -> check_strict_kind' (n + 1) k
    let rec check_strict_type
      ((p)(* p is whether we should imagine we are checking a c+ (rather than c-) constant *))
      b = check_strict_type' 0 p b
    let rec check_strict_kind k = check_strict_kind' 0 k
  end;;
