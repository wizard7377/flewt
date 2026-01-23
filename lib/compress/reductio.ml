module Reductio =
  struct
    exception Unimp 
    exception Error of string 
    exception Matching of string 
    exception NonPattern 
    exception NotFound of string 
    open Syntax
    type kinding_constraint =
      | CON_LF 
      | CON_PLUS 
      | CON_MINUS 
    type eq_c =
      | EltC of (spinelt * spinelt) 
      | SpineC of (spine * spine) 
      | TypeC of (tp * tp) 
    type nonrec tp_c = (term * tp)
    let rec tp_eq =
      begin function
      | (TRoot (n, sp), TRoot (n', sp')) ->
          type_const_head_eq (n, n', sp, sp')
      | (TPi (m, a, b), TPi (m', a', b')) ->
          (m = m') && ((tp_eq (a, a')) && (tp_eq (b, b')))
      | _ -> false end
    let rec sp_eq =
      begin function
      | ([], []) -> true
      | (e::sp, e'::sp') -> (elt_eq (e, e')) && (sp_eq (sp, sp'))
      | _ -> false end
  let rec elt_eq (t, t') = elt_eq' ((elt_eroot_elim t), (elt_eroot_elim t'))
  let rec elt_eq' =
    begin function
    | (Elt t, Elt t') -> tm_eq (t, t')
    | (AElt t, AElt t') -> atm_eq (t, t')
    | (Ascribe (t, a), Ascribe (t', a')) ->
        (ntm_eq (t, t')) && (tp_eq (a, a'))
    | (Omit, Omit) -> true
    | _ -> false end
let rec tm_eq =
  begin function
  | (NTerm t, NTerm t') -> ntm_eq (t, t')
  | (ATerm t, ATerm t') -> atm_eq (t, t')
  | _ -> false end
let rec atm_eq =
  begin function
  | ((ARoot (Const n, sp) as tm), (ARoot (Const n', sp') as tm')) ->
      const_head_eq (n, n', sp, sp', (ATerm tm), (ATerm tm'))
  | (ARoot (Var n, sp), ARoot (Var n', sp')) -> (n = n') && (sp_eq (sp, sp'))
  | _ -> false end
let rec ntm_eq (t, t') = ntm_eq' ((ntm_eroot_elim t), (ntm_eroot_elim t'))
let rec ntm_eq' =
  begin function
  | ((NRoot (Const n, sp) as tm), (NRoot (Const n', sp') as tm')) ->
      const_head_eq (n, n', sp, sp', (NTerm tm), (NTerm tm'))
  | (Lam t, Lam t') -> tm_eq (t, t')
  | _ -> false end
let rec const_head_eq (n, n', sp, sp', tm, tm') =
  let def = Sgn.def n in
  let def' = Sgn.def n' in
  let eq_and_strict =
    (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
  let rec redux t n sp =
    reduce ((srTerm (t, (typeOf (Sgn.classifier n)))), sp) in
  begin match (eq_and_strict, def, def') with
  | (true, _, _) -> sp_eq (sp, sp')
  | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) -> false
  | (_, DEF_TERM t, DEF_TERM t') -> tm_eq ((redux t n sp), (redux t' n' sp'))
  | (_, DEF_TERM t, Sgn.DEF_NONE) -> tm_eq ((redux t n sp), tm')
  | (_, Sgn.DEF_NONE, DEF_TERM t') -> tm_eq (tm, (redux t' n' sp'))
  | _ -> raise (Syntax "invariant violation") end
let rec type_const_head_eq (n, n', sp, sp') =
  let def = Sgn.def n in
  let def' = Sgn.def n' in
  let eq_and_strict =
    (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
  let rec redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
  begin match (eq_and_strict, def, def') with
  | (true, _, _) -> sp_eq (sp, sp')
  | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) -> false
  | (_, DEF_TYPE a, DEF_TYPE a') -> tp_eq ((redux a n sp), (redux a' n' sp'))
  | (_, DEF_TYPE a, Sgn.DEF_NONE) ->
      tp_eq ((redux a n sp), (TRoot (n', sp')))
  | (_, Sgn.DEF_NONE, DEF_TYPE a') ->
      tp_eq ((TRoot (n, sp)), (redux a' n' sp'))
  | _ -> raise (Syntax "invariant violation") end
let rec eq_c_true =
  begin function
  | EltC (e, e') -> elt_eq (e, e')
  | SpineC (s, s') -> sp_eq (s, s')
  | TypeC (a, a') -> tp_eq (a, a') end
type nonrec ppsubst = (int list * int)
let rec pp_shift (vs, shift) m =
  let len = length vs in
  if m < len then begin ((List.drop (vs, m)), shift) end
    else begin ([], ((m - len) + shift)) end
let rec pp_nth (vs, shift) n =
  let len = length vs in if n < len then begin List.nth (vs, n) end
    else begin (n - len) + shift end
let rec pp_o (pps, (vs, shift)) =
  let (vs', shift') = pp_shift pps shift in
  (((map (pp_nth pps) vs) @ vs'), shift')
let rec pp_comp ppsl = foldr pp_o ([], 0) ppsl
let rec pp_normalize s = pp_normalize' s
let rec pp_normalize' =
  begin function
  | Id -> ([], 0)
  | TermDot (t, a, s) ->
      let v =
        begin try Strict.eta_contract_var (Elt t)
        with | Strict.EtaContract -> raise Domain end in
    let (vs, shift) = pp_normalize' s in ((((v :: vs), shift))
      (* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *))
  | ZeroDotShift s ->
      let (vs, shift) = pp_normalize' s in
      ((0 :: (map (begin function | x -> x + 1 end) vs)), (shift + 1))
  | Shift (n, m) -> ((List.tabulate (n, (begin function | x -> x end))),
      (n + m)) | EVarDot _ -> raise Domain
| VarOptDot (no, s) ->
    let (vs, shift) = pp_normalize' s in
    (begin match no with
     | Some n -> ((n :: vs), shift)
     | None -> raise (Error "??? I'm not sure this is really wrong") end)
| Compose sl -> prepattern (substs_comp sl) end(* XXX: Correct??? *)
(* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)
let rec prepattern (s : subst) = pp_normalize s
let rec pp_ispat =
  begin function
  | ([], shift) -> true
  | (n::s, shift) ->
      let rec isn x = x = n in
      let rec hasn s = List.exists isn s in
      (n < shift) && ((not (hasn s)) && (pp_ispat (s, shift))) end
let rec makesubst =
  begin function
  | ([], 0) -> Id
  | ([], shift) -> Shift (0, shift)
  | (v::vs, shift) -> VarOptDot (v, (makesubst (vs, shift))) end
let rec pp_invert (vs, shift) =
  let inds = List.tabulate (shift, (begin function | x -> x end)) in
let rec search arg__0 arg__1 arg__2 =
  begin match (arg__0, arg__1, arg__2) with
  | (n, [], (x : int)) -> None
  | (n, h::tl, x) -> if x = h then begin Some n end
      else begin search (n + 1) tl x end end in
makesubst ((map (search 0 vs) inds), (length vs))
let rec flex_left =
  begin function
  | ((({ contents = None } as r), a), (s : subst), rhs) ->
      let pps = begin try prepattern s with | Domain -> raise NonPattern end in
    let _ = if pp_ispat pps then begin () end else begin raise NonPattern end in
let ppsi = pp_invert pps in
let rhs' = subst_term ppsi (termof rhs) in let _ = (:=) r Some rhs' in ()
| _ -> raise (Error "evar invariant violated") end
let rec just_one c = [c]
let rec just_one' c = [c]
let rec match_one' =
  begin function
  | EltC (Elt (NTerm (Lam t)), Elt (NTerm (Lam t'))) ->
      just_one (EltC ((Elt t), (Elt t')))
  | EltC
      ((Elt (NTerm (NRoot (Const n, s))) as elt),
       (Elt (NTerm (NRoot (Const n', s'))) as elt'))
      -> match_const_head (n, n', s, s', elt, elt', "c- head mismatch")
  | EltC
      ((Elt (ATerm (ARoot (Const n, s))) as elt),
       (Elt (ATerm (ARoot (Const n', s'))) as elt'))
      -> match_const_head (n, n', s, s', elt, elt', "c+ head mismatch")
  | EltC (Elt (ATerm (ARoot (Var n, s))), Elt (ATerm (ARoot (Var n', s'))))
      -> if n = n' then begin just_one' (SpineC (s, s')) end
      else begin raise (Matching "var head mismatch") end
  | EltC (AElt t, AElt t') ->
      just_one' (EltC ((Elt (ATerm t)), (Elt (ATerm t'))))
  | EltC (Ascribe (m, a), Ascribe (m', a')) ->
      match_two (EltC ((Elt (NTerm m)), (Elt (NTerm m')))) (TypeC (a, a'))
  | EltC (Omit, Omit) -> []
  | TypeC (TPi (m, a, b), TPi (m', a', b')) ->
      if (m = MINUS) && (m' = MINUS)
      then begin match_two (TypeC (a, a')) (TypeC (b, b')) end
      else begin raise (Matching "mode mismatch") end
| TypeC (TRoot (n, s), TRoot (n', s')) ->
    match_type_const_head (n, n', s, s', "type family mismatch")
| SpineC ([], []) -> []
| SpineC (h::s, h'::s') -> match_two (EltC (h, h')) (SpineC (s, s'))
| EltC (Elt (ATerm (ERoot (ev, (s : subst)))), elt) ->
    (begin flex_left (ev, s, elt); [] end)
| x -> raise (Matching "doesn't match") end
let rec match_one =
  begin function
  | EltC (elt, elt') ->
      match_one' (EltC ((elt_eroot_elim elt), (elt_eroot_elim elt')))
  | e -> match_one' e end
let rec match_two e1 e2 = [e1; e2]
let rec match_const_head (n, n', s, s', elt, elt', err) =
  let def = Sgn.def n in
  let def' = Sgn.def n' in
  let eq_and_strict =
    (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
  let rec redux t n sp =
    reduce ((srTerm (t, (typeOf (Sgn.classifier n)))), sp) in
  let eq =
    begin match (eq_and_strict, def, def') with
    | (true, _, _) -> SpineC (s, s')
    | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) -> raise (Matching err)
    | (_, DEF_TERM t, DEF_TERM t') ->
        EltC ((Elt (redux t n s)), (Elt (redux t' n' s')))
    | (_, DEF_TERM t, Sgn.DEF_NONE) -> EltC ((Elt (redux t n s)), elt')
    | (_, Sgn.DEF_NONE, DEF_TERM t') -> EltC (elt, (Elt (redux t' n' s')))
    | _ -> raise (Matching "invariant violation") end in
  just_one' eq
let rec match_type_const_head (n, n', s, s', err) =
  let def = Sgn.def n in
  let def' = Sgn.def n' in
  let eq_and_strict =
    (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
  let rec redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
  let eq =
    begin match (eq_and_strict, def, def') with
    | (true, _, _) -> SpineC (s, s')
    | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) -> raise (Matching err)
    | (_, DEF_TYPE a, DEF_TYPE a') -> TypeC ((redux a n s), (redux a' n' s'))
    | (_, DEF_TYPE a, Sgn.DEF_NONE) ->
        TypeC ((redux a n s), (TRoot (n', s')))
    | (_, Sgn.DEF_NONE, DEF_TYPE a') ->
        TypeC ((TRoot (n, s)), (redux a' n' s'))
    | _ -> raise (Matching "invariant violation") end in
  just_one' eq
let rec matching p =
  let rec matching' =
    begin function
    | (c::p, p') ->
        (begin try let eqs = match_one c in matching' ((eqs @ p), p')
         with | NonPattern -> matching' (p, (c :: p')) end)
    | ([], p') -> p' end in
matching' (p, [])
let rec ctxcons (a, g_) = a :: g_
type cg_mode =
  | CG_SYNTH 
  | CG_CHECK of tp 
let rec constraint_gen (g_) (s, z, c) = constraint_gen' g_ (s, z, c)
let rec constraint_gen' arg__3 arg__4 =
  begin match (arg__3, arg__4) with
  | (g_, ([], (TRoot _ as a), CG_CHECK (TRoot _ as a'))) ->
      ([TypeC (a, a')], [], None)
  | (g_, ([], TRoot (n, s), CG_SYNTH)) -> ([], [], (Some (TRoot (n, s))))
  | (g_, ((Omit)::s, TPi (OMIT, a, z), c)) ->
      let (ev : evar) = ((ref None), a) in
      let z' = subst_tp (EVarDotId ev) z in
      let (p, q, aa) = constraint_gen' g_ (s, z', c) in (p, q, aa)
  | (g_, ((Elt m)::s, TPi (MINUS, a, z), c)) ->
      let z' = subst_tp (TermDot (m, a, Id)) z in
      let (p, q, aa) = constraint_gen' g_ (s, z', c) in
      (p, ((m, a) :: q), aa)
  | (g_, ((AElt m)::s, TPi (PLUS, a, z), c)) ->
      let a' = synth (g_, m) in
      let z' = subst_tp (TermDot ((ATerm m), a, Id)) z in
      let (p, q, aa) = constraint_gen' g_ (s, z', c) in
      (((((TypeC (a, a')) :: p), q, aa))
        (* Same PERF comment here as above *))
  | (g_, ((Ascribe (m, a'))::s, TPi (PLUS, a, z), c)) ->
      let z' = subst_tp (TermDot ((NTerm m), a, Id)) z in
      let (p, q, aa) = constraint_gen' g_ (s, z', c) in
      (((((TypeC (a, a')) :: p), q, aa))
        (* As well as here *))
  | (_, _) -> raise (Error "spine doesn't match type") end(* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)
let rec tp_constraint_gen arg__5 arg__6 =
  begin match (arg__5, arg__6) with
  | (g_, ([], Type)) -> ([], [])
  | (g_, ((Omit)::s, KPi (OMIT, a, z))) ->
      let (ev : evar) = ((ref None), a) in
      let z' = subst_knd (EVarDotId ev) z in
      let (p, q) = tp_constraint_gen g_ (s, z') in (p, q)
  | (g_, ((Elt m)::s, KPi (MINUS, a, z))) ->
      let z' = subst_knd (TermDot (m, a, Id)) z in
      let (p, q) = tp_constraint_gen g_ (s, z') in (p, ((m, a) :: q))
  | (g_, ((AElt m)::s, KPi (PLUS, a, z))) ->
      let a' = synth (g_, m) in
      let z' = subst_knd (TermDot ((ATerm m), a, Id)) z in
      let (p, q) = tp_constraint_gen g_ (s, z') in
      (((TypeC (a, a')) :: p), q)
  | (g_, ((Ascribe (m, a'))::s, KPi (PLUS, a, z))) ->
      let z' = subst_knd (TermDot ((NTerm m), a, Id)) z in
      let (p, q) = tp_constraint_gen g_ (s, z') in
      (((TypeC (a, a')) :: p), q)
  | (_, _) -> raise (Error "spine doesn't match type") end
let rec check_equality_constraints p = List.all eq_c_true p
let rec check_typing_constraints (g_) q =
  List.all (begin function | (m, a) -> check (g_, m, a) end) q
let rec matching_succeeds (g_) (p, q) =
  let p' = matching p in
  let _ = if check_equality_constraints p' then begin () end
    else begin raise (Matching "residual equality constraints failed") end in
let _ = if check_typing_constraints g_ q then begin () end
  else begin raise (Matching "residual typing constraints failed") end in
((true)
  (* evar side-effects affect q, raises Matching if matching fails *))
let rec check_spinelt =
  begin function
  | (g_, Elt t, a) -> check (g_, t, a)
  | (g_, AElt t, a) -> check (g_, (ATerm t), a)
  | (g_, Ascribe (t, a), a') -> (tp_eq (a, a')) && (check (g_, (NTerm t), a))
  | (g_, Omit, _) -> raise (Error "cannot check omitted arguments") end
let rec check =
  begin function
  | (g_, NTerm (Lam t), TPi (_, a, b)) -> check ((ctxcons (a, g_)), t, b)
  | (g_, ATerm t, a) ->
      (begin try tp_eq ((synth (g_, t)), a) with | Error s -> false end)
  | (g_, NTerm (NRoot (Const n, s)), a) ->
      let b =
        begin match Sgn.classifier n with
        | tclass b -> b
        | _ -> raise (Error "signature invariant violated!") end in
    let (p, q, _) = constraint_gen g_ (s, b, (CG_CHECK a)) in
    ((matching_succeeds g_ (p, q))
      (* creates ref cells for evars *))
  | _ -> false end
let rec check_kind =
  begin function
  | (g_, Type) -> true
  | (g_, KPi (OMIT, a, k)) ->
      (check_type CON_LF (g_, a)) &&
        ((check_kind ((ctxcons (a, g_)), k)) && (Strict.check_strict_kind k))
  | (g_, KPi (_, a, k)) ->
      (check_type CON_LF (g_, a)) && (check_kind ((ctxcons (a, g_)), k)) end
let rec check_type arg__7 arg__8 =
  begin match (arg__7, arg__8) with
  | (_, (g_, TRoot (n, s))) ->
      let k =
        begin match Sgn.classifier n with
        | kclass k -> k
        | _ -> raise (Error "signature invariant violated!") end in
    let (p, q) = tp_constraint_gen g_ (s, k) in
    ((matching_succeeds g_ (p, q))
      (* creates ref cells for evars *))
  | (con, (g_, TPi (OMIT, a, b))) ->
      let plusconst =
        begin match con with
        | CON_LF ->
            raise (Error "TPi(OMIT) where a pure LF function type expected")
        | CON_PLUS -> true
        | CON_MINUS -> false end in
    (check_type CON_LF (g_, a)) &&
      ((check_type con ((ctxcons (a, g_)), b)) &&
         (Strict.check_strict_type plusconst b))
  | (con, (g_, TPi (m, a, b))) ->
      (begin match (con, m) with
       | (CON_LF, PLUS) ->
           raise (Error "TPi(PLUS) where a pure LF function type expected")
       | _ ->
           (check_type CON_LF (g_, a)) &&
             (check_type con ((ctxcons (a, g_)), b)) end) end
let rec check_type' =
  begin function
  | (g_, Type, []) -> true
  | (g_, KPi (_, a, k), m::s) ->
      let _ = if check_spinelt (g_, m, a) then begin () end
        else begin raise (Error "argument type mismatch") end in
let k' = subst_knd (TermDot ((termof m), a, Id)) k in check_type' (g_, k', s)
  | _ -> false end
let rec synth =
  begin function
  | (g_, ARoot (Var n, s)) -> synth' (g_, (ctxLookup (g_, n)), s)
  | (g_, ARoot (Const n, s)) ->
      let b =
        begin match Sgn.classifier n with
        | tclass b -> b
        | _ -> raise (Error "signature invariant violated!") end in
    let (p, q, aopt) = constraint_gen g_ (s, b, CG_SYNTH) in
    let _ = matching_succeeds g_ (p, q) in ((Option.valOf aopt)
      (* creates ref cells for evars *)(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *)
      (* raises Matching if not *)(* by invariant, aopt must be SOME *))
  | (g_, (ERoot _ as t)) -> elt_synth (g_, (eroot_elim_plus t)) end
let rec synth' =
  begin function
  | (g_, (TRoot (_, _) as a), []) -> a
  | (g_, TPi (_, a, b), m::s) ->
      let _ = if check_spinelt (g_, m, a) then begin () end
        else begin raise (Error "argument type mismatch") end in
let b' = subst_tp (TermDot ((termof m), a, Id)) b in synth' (g_, b', s)
  | _ -> raise (Error "applying nonfunction to argument") end
let rec elt_synth =
  begin function
  | (g_, AElt t) -> synth (g_, t)
  | (g_, Ascribe (t, a)) -> if check (g_, (NTerm t), a) then begin a end
      else begin raise (Error "ascription doesn't check") end
  | (g_, Elt _) ->
      raise (Error "trying to synthesize a merely checkable element")
  | (g_, Omit) -> raise (Error "trying to synthesize an omitted argument") end
let rec check_plusconst_type t = check_type CON_PLUS ([], t)
let rec check_minusconst_type t = check_type CON_MINUS ([], t)
let rec check_strictness_type arg__9 arg__10 =
  begin match (arg__9, arg__10) with
  | (_, TRoot (n, s)) -> true
  | (plusconst, TPi (OMIT, _, b)) ->
      (check_strictness_type plusconst b) &&
        (Strict.check_strict_type plusconst b)
  | (plusconst, TPi (_, _, b)) -> check_strictness_type plusconst b end
let check_plusconst_strictness = check_strictness_type true
let check_minusconst_strictness = check_strictness_type false
end