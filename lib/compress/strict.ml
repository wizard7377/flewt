
module Strict =
  struct
    open Syntax
    exception EtaContract 
    let rec eta_contract_var =
      function | Elt t -> eta_contract_var' 0 t | _ -> raise EtaContract
    let rec eta_contract_var' __2__ __3__ =
      match (__2__, __3__) with
      | (n, ATerm (ARoot (Var n', s))) ->
          let s' = map eta_contract_var s in
          let rec decreasing_list __0__ __1__ =
            match (__0__, __1__) with
            | (0, []) -> true__
            | (n, h::tl) -> ((n - 1) = h) && (decreasing_list (n - 1) tl)
            | (_, _) -> false__ in
          if decreasing_list n s' then n' - n else raise EtaContract
      | (n, NTerm (Lam t)) -> eta_contract_var' (n + 1) t
      | (_, _) -> raise EtaContract
    let rec pattern_spine' __4__ __5__ =
      match (__4__, __5__) with
      | (__D, []) -> true__
      | (__D, n::s) ->
          let rec isn x = x = n in
          let rec hasn s = List.exists isn s in
          (hasn __D) && ((not (hasn s)) && (pattern_spine' (__D, s)))
    let rec pattern_spine (__D) s =
      try pattern_spine' (__D, (map eta_contract_var s))
      with | EtaContract -> false__
    let rec spine_occ __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (n, __D, nil) -> false__
      | (n, __D, (Elt t)::s) ->
          (term_occ n (__D, t)) || (spine_occ n (__D, s))
      | (n, __D, (AElt t)::s) ->
          (aterm_occ n (__D, t)) || (spine_occ n (__D, s))
      | (n, __D, (Ascribe (t, a))::s) ->
          (nterm_occ n (__D, t)) ||
            ((type_occ n (__D, a)) || (spine_occ n (__D, s)))
      | (n, __D, (Omit)::s) -> false__
    let rec term_occ __9__ __10__ __11__ =
      match (__9__, __10__, __11__) with
      | (n, __D, NTerm t) -> nterm_occ n (__D, t)
      | (n, __D, ATerm t) -> aterm_occ n (__D, t)
    let rec nterm_occ __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (n, __D, Lam t) ->
          term_occ (n + 1) ((0 :: (map (fun x -> x + 1) __D)), t)
      | (n, __D, NRoot (h, s)) -> root_occ n (__D, h, s)
    let rec aterm_occ __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (n, __D, ARoot (h, s)) -> root_occ n (__D, h, s)
      | (n, __D, ERoot _) -> false__
    let rec root_occ __18__ __19__ __20__ __21__ =
      match (__18__, __19__, __20__, __21__) with
      | (n, __D, Var n', s) ->
          ((if n = n'
            then pattern_spine (__D, s)
            else
              (List.exists (fun x -> x = n') __D) && (spine_occ n (__D, s)))
          (* n = n' precludes n in D, right? *))
      | (n, __D, Const n', s) -> spine_occ n (__D, s)
    let rec type_occ __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | (n, __D, TRoot (_, s)) -> spine_occ n (__D, s)
      | (n, __D, TPi (_, a, b)) ->
          (((type_occ n (__D, a)) ||
              (type_occ (n + 1) ((0 :: (map (fun x -> x + 1) __D)), b)))
          (* PERF: suspend these context shifts, do them at the end *))
    let rec check_strict_type' __25__ __26__ __27__ =
      match (__25__, __26__, __27__) with
      | (n, p, TRoot (n', s)) -> if p then false__ else spine_occ n ([], s)
      | (n, p, TPi (PLUS, a, b)) ->
          (type_occ n ([], a)) || (check_strict_type' (n + 1) p b)
      | (n, p, TPi (_, a, b)) -> check_strict_type' (n + 1) p b
    let rec check_strict_kind' __28__ __29__ =
      match (__28__, __29__) with
      | (n, Type) -> false__
      | (n, KPi (PLUS, a, k)) ->
          (type_occ n ([], a)) || (check_strict_kind' (n + 1) k)
      | (n, KPi (_, a, k)) -> check_strict_kind' (n + 1) k
    let rec check_strict_type p b = check_strict_type' 0 p b
    let rec check_strict_kind k = check_strict_kind' 0 k
  end;;
