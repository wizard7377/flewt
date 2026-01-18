
module Strict =
  struct
    open Syntax
    exception EtaContract 
    (* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *)
    let rec eta_contract_var =
      function | Elt t -> eta_contract_var' 0 t | _ -> raise EtaContract
    let rec eta_contract_var' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, ATerm (ARoot (Var n', s))) ->
          let s' = map eta_contract_var s in
          let rec decreasing_list arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (0, []) -> true__
            | (n, h::tl) -> ((n - 1) = h) && (decreasing_list (n - 1) tl)
            | (_, _) -> false__ in
          if decreasing_list n s' then n' - n else raise EtaContract
      | (n, NTerm (Lam t)) -> eta_contract_var' (n + 1) t
      | (_, _) -> raise EtaContract
    let rec pattern_spine' =
      function
      | (__d, []) -> true__
      | (__d, n::s) ->
          let rec isn x = x = n in
          let rec hasn s = List.exists isn s in
          (hasn __d) && ((not (hasn s)) && (pattern_spine' (__d, s)))
    let rec pattern_spine (__d, s) =
      try pattern_spine' (__d, (map eta_contract_var s))
      with | EtaContract -> false__
    let rec spine_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, nil)) -> false__
      | (n, (__d, (Elt t)::s)) -> (term_occ n (__d, t)) || (spine_occ n (__d, s))
      | (n, (__d, (AElt t)::s)) -> (aterm_occ n (__d, t)) || (spine_occ n (__d, s))
      | (n, (__d, (Ascribe (t, a))::s)) ->
          (nterm_occ n (__d, t)) ||
            ((type_occ n (__d, a)) || (spine_occ n (__d, s)))
      | (n, (__d, (Omit)::s)) -> false__
    let rec term_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, NTerm t)) -> nterm_occ n (__d, t)
      | (n, (__d, ATerm t)) -> aterm_occ n (__d, t)
    let rec nterm_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, Lam t)) ->
          term_occ (n + 1) ((0 :: (map (function | x -> x + 1) __d)), t)
      | (n, (__d, NRoot (h, s))) -> root_occ n (__d, h, s)
    let rec aterm_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, ARoot (h, s))) -> root_occ n (__d, h, s)
      | (n, (__d, ERoot _)) -> false__
    let rec root_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, Var n', s)) ->
          ((if n = n'
            then pattern_spine (__d, s)
            else
              (List.exists (function | x -> x = n') __d) &&
                (spine_occ n (__d, s)))
          (* n = n' precludes n in __d, right? *))
      | (n, (__d, Const n', s)) -> spine_occ n (__d, s)
    let rec type_occ arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, (__d, TRoot (_, s))) -> spine_occ n (__d, s)
      | (n, (__d, TPi (_, a, b))) ->
          (((type_occ n (__d, a)) ||
              (type_occ (n + 1) ((0 :: (map (function | x -> x + 1) __d)), b)))
          (* PERF: suspend these context shifts, do them at the end *))
    (* toplevel strictness judgments *)
    let rec check_strict_type' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (n, p, TRoot (n', s)) -> if p then false__ else spine_occ n ([], s)
      | (n, p, TPi (PLUS, a, b)) ->
          (type_occ n ([], a)) || (check_strict_type' (n + 1) p b)
      | (n, p, TPi (_, a, b)) -> check_strict_type' (n + 1) p b
    let rec check_strict_kind' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, Type) -> false__
      | (n, KPi (PLUS, a, k)) ->
          (type_occ n ([], a)) || (check_strict_kind' (n + 1) k)
      | (n, KPi (_, a, k)) -> check_strict_kind' (n + 1) k
    (* p is whether we should imagine we are checking a c+ (rather than c-) constant *)
    let rec check_strict_type p b = check_strict_type' 0 p b
    let rec check_strict_kind k = check_strict_kind' 0 k
  end;;
