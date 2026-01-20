
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
    let rec tp_eq __0__ __1__ =
      match (__0__, __1__) with
      | (TRoot (n, sp), TRoot (n', sp')) ->
          type_const_head_eq (n, n', sp, sp')
      | (TPi (m, a, b), TPi (m', a', b')) ->
          (m = m') && ((tp_eq (a, a')) && (tp_eq (b, b')))
      | _ -> false__
    let rec sp_eq __2__ __3__ =
      match (__2__, __3__) with
      | ([], []) -> true__
      | (e::sp, e'::sp') -> (elt_eq (e, e')) && (sp_eq (sp, sp'))
      | _ -> false__
    let rec elt_eq t t' = elt_eq' ((elt_eroot_elim t), (elt_eroot_elim t'))
    let rec elt_eq' __4__ __5__ =
      match (__4__, __5__) with
      | (Elt t, Elt t') -> tm_eq (t, t')
      | (AElt t, AElt t') -> atm_eq (t, t')
      | (Ascribe (t, a), Ascribe (t', a')) ->
          (ntm_eq (t, t')) && (tp_eq (a, a'))
      | (Omit, Omit) -> true__
      | _ -> false__
    let rec tm_eq __6__ __7__ =
      match (__6__, __7__) with
      | (NTerm t, NTerm t') -> ntm_eq (t, t')
      | (ATerm t, ATerm t') -> atm_eq (t, t')
      | _ -> false__
    let rec atm_eq __8__ __9__ =
      match (__8__, __9__) with
      | ((ARoot (Const n, sp) as tm), (ARoot (Const n', sp') as tm')) ->
          const_head_eq (n, n', sp, sp', (ATerm tm), (ATerm tm'))
      | (ARoot (Var n, sp), ARoot (Var n', sp')) ->
          (n = n') && (sp_eq (sp, sp'))
      | _ -> false__
    let rec ntm_eq t t' = ntm_eq' ((ntm_eroot_elim t), (ntm_eroot_elim t'))
    let rec ntm_eq' __10__ __11__ =
      match (__10__, __11__) with
      | ((NRoot (Const n, sp) as tm), (NRoot (Const n', sp') as tm')) ->
          const_head_eq (n, n', sp, sp', (NTerm tm), (NTerm tm'))
      | (Lam t, Lam t') -> tm_eq (t, t')
      | _ -> false__
    let rec const_head_eq n n' sp sp' tm tm' =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let rec redux t n sp =
        reduce ((srTerm (t, (typeOf (Sgn.classifier n)))), sp) in
      match (eq_and_strict, def, def') with
      | (true__, _, _) -> sp_eq (sp, sp')
      | (false__, Sgn.DEF_NONE, Sgn.DEF_NONE) -> false__
      | (_, DEF_TERM t, DEF_TERM t') ->
          tm_eq ((redux t n sp), (redux t' n' sp'))
      | (_, DEF_TERM t, Sgn.DEF_NONE) -> tm_eq ((redux t n sp), tm')
      | (_, Sgn.DEF_NONE, DEF_TERM t') -> tm_eq (tm, (redux t' n' sp'))
      | _ -> raise (Syntax "invariant violation")
    let rec type_const_head_eq n n' sp sp' =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let rec redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
      match (eq_and_strict, def, def') with
      | (true__, _, _) -> sp_eq (sp, sp')
      | (false__, Sgn.DEF_NONE, Sgn.DEF_NONE) -> false__
      | (_, DEF_TYPE a, DEF_TYPE a') ->
          tp_eq ((redux a n sp), (redux a' n' sp'))
      | (_, DEF_TYPE a, Sgn.DEF_NONE) ->
          tp_eq ((redux a n sp), (TRoot (n', sp')))
      | (_, Sgn.DEF_NONE, DEF_TYPE a') ->
          tp_eq ((TRoot (n, sp)), (redux a' n' sp'))
      | _ -> raise (Syntax "invariant violation")
    let rec eq_c_true =
      function
      | EltC (e, e') -> elt_eq (e, e')
      | SpineC (s, s') -> sp_eq (s, s')
      | TypeC (a, a') -> tp_eq (a, a')
    type nonrec ppsubst = (int list * int)
    let rec pp_shift vs shift m =
      let len = length vs in
      if m < len
      then ((List.drop (vs, m)), shift)
      else ([], ((m - len) + shift))
    let rec pp_nth vs shift n =
      let len = length vs in
      if n < len then List.nth (vs, n) else (n - len) + shift
    let rec pp_o pps (vs, shift) =
      let (vs', shift') = pp_shift pps shift in
      (((map (pp_nth pps) vs) @ vs'), shift')
    let rec pp_comp ppsl = foldr pp_o ([], 0) ppsl
    let rec pp_normalize s = pp_normalize' s
    let rec pp_normalize' =
      function
      | Id -> ([], 0)
      | TermDot (t, a, s) ->
          let v =
            try Strict.eta_contract_var (Elt t)
            with | Strict.EtaContract -> raise Domain in
          let (vs, shift) = pp_normalize' s in ((((v :: vs), shift))
            (* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *))
      | ZeroDotShift s ->
          let (vs, shift) = pp_normalize' s in
          ((0 :: (map (fun x -> x + 1) vs)), (shift + 1))
      | Shift (n, m) -> ((List.tabulate (n, (fun x -> x))), (n + m))
      | EVarDot _ -> raise Domain
      | VarOptDot (no, s) ->
          let (vs, shift) = pp_normalize' s in
          (match no with
           | Some n -> ((n :: vs), shift)
           | NONE -> raise (Error "??? I'm not sure this is really wrong"))
      | Compose sl -> prepattern (substs_comp sl)(* XXX: Correct??? *)
      (* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)
    let rec prepattern s = pp_normalize s
    let rec pp_ispat __12__ __13__ =
      match (__12__, __13__) with
      | ([], shift) -> true__
      | (n::s, shift) ->
          let rec isn x = x = n in
          let rec hasn s = List.exists isn s in
          (n < shift) && ((not (hasn s)) && (pp_ispat (s, shift)))
    let rec makesubst __14__ __15__ =
      match (__14__, __15__) with
      | ([], 0) -> Id
      | ([], shift) -> Shift (0, shift)
      | (v::vs, shift) -> VarOptDot (v, (makesubst (vs, shift)))
    let rec pp_invert vs shift =
      let inds = List.tabulate (shift, (fun x -> x)) in
      let rec search __16__ __17__ __18__ =
        match (__16__, __17__, __18__) with
        | (n, [], x) -> NONE
        | (n, h::tl, x) -> if x = h then Some n else search (n + 1) tl x in
      makesubst ((map (search 0 vs) inds), (length vs))
    let rec flex_left __19__ __20__ __21__ =
      match (__19__, __20__, __21__) with
      | ((({ contents = NONE } as r), a), (s : subst), rhs) ->
          let pps = try prepattern s with | Domain -> raise NonPattern in
          let _ = if pp_ispat pps then () else raise NonPattern in
          let ppsi = pp_invert pps in
          let rhs' = subst_term ppsi (termof rhs) in
          let _ = (:=) r Some rhs' in ()
      | _ -> raise (Error "evar invariant violated")
    let rec just_one c = [c]
    let rec just_one' c = [c]
    let rec match_one' =
      function
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
      | EltC
          (Elt (ATerm (ARoot (Var n, s))), Elt (ATerm (ARoot (Var n', s'))))
          ->
          if n = n'
          then just_one' (SpineC (s, s'))
          else raise (Matching "var head mismatch")
      | EltC (AElt t, AElt t') ->
          just_one' (EltC ((Elt (ATerm t)), (Elt (ATerm t'))))
      | EltC (Ascribe (m, a), Ascribe (m', a')) ->
          match_two (EltC ((Elt (NTerm m)), (Elt (NTerm m'))))
            (TypeC (a, a'))
      | EltC (Omit, Omit) -> []
      | TypeC (TPi (m, a, b), TPi (m', a', b')) ->
          if (m = MINUS) && (m' = MINUS)
          then match_two (TypeC (a, a')) (TypeC (b, b'))
          else raise (Matching "mode mismatch")
      | TypeC (TRoot (n, s), TRoot (n', s')) ->
          match_type_const_head (n, n', s, s', "type family mismatch")
      | SpineC ([], []) -> []
      | SpineC (h::s, h'::s') -> match_two (EltC (h, h')) (SpineC (s, s'))
      | EltC (Elt (ATerm (ERoot (ev, (s : subst)))), elt) ->
          (flex_left (ev, s, elt); [])
      | x -> raise (Matching "doesn't match")
    let rec match_one =
      function
      | EltC (elt, elt') ->
          match_one' (EltC ((elt_eroot_elim elt), (elt_eroot_elim elt')))
      | e -> match_one' e
    let rec match_two e1 e2 = [e1; e2]
    let rec match_const_head n n' s s' elt elt' err =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let rec redux t n sp =
        reduce ((srTerm (t, (typeOf (Sgn.classifier n)))), sp) in
      let eq =
        match (eq_and_strict, def, def') with
        | (true__, _, _) -> SpineC (s, s')
        | (false__, Sgn.DEF_NONE, Sgn.DEF_NONE) -> raise (Matching err)
        | (_, DEF_TERM t, DEF_TERM t') ->
            EltC ((Elt (redux t n s)), (Elt (redux t' n' s')))
        | (_, DEF_TERM t, Sgn.DEF_NONE) -> EltC ((Elt (redux t n s)), elt')
        | (_, Sgn.DEF_NONE, DEF_TERM t') ->
            EltC (elt, (Elt (redux t' n' s')))
        | _ -> raise (Matching "invariant violation") in
      just_one' eq
    let rec match_type_const_head n n' s s' err =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let rec redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
      let eq =
        match (eq_and_strict, def, def') with
        | (true__, _, _) -> SpineC (s, s')
        | (false__, Sgn.DEF_NONE, Sgn.DEF_NONE) -> raise (Matching err)
        | (_, DEF_TYPE a, DEF_TYPE a') ->
            TypeC ((redux a n s), (redux a' n' s'))
        | (_, DEF_TYPE a, Sgn.DEF_NONE) ->
            TypeC ((redux a n s), (TRoot (n', s')))
        | (_, Sgn.DEF_NONE, DEF_TYPE a') ->
            TypeC ((TRoot (n, s)), (redux a' n' s'))
        | _ -> raise (Matching "invariant violation") in
      just_one' eq
    let rec matching p =
      let rec matching' __22__ __23__ =
        match (__22__, __23__) with
        | (c::p, p') ->
            (try let eqs = match_one c in matching' ((eqs @ p), p')
             with | NonPattern -> matching' (p, (c :: p')))
        | ([], p') -> p' in
      matching' (p, [])
    let rec ctxcons a (__G) = a :: __G
    type cg_mode =
      | CG_SYNTH 
      | CG_CHECK of tp 
    let rec constraint_gen (__G) s z c = constraint_gen' __G (s, z, c)
    let rec constraint_gen' __24__ __25__ __26__ __27__ =
      match (__24__, __25__, __26__, __27__) with
      | (__G, [], (TRoot _ as a), CG_CHECK (TRoot _ as a')) ->
          ([TypeC (a, a')], [], NONE)
      | (__G, [], TRoot (n, s), CG_SYNTH) -> ([], [], (Some (TRoot (n, s))))
      | (__G, (Omit)::s, TPi (OMIT, a, z), c) ->
          let (ev : evar) = ((ref NONE), a) in
          let z' = subst_tp (EVarDotId ev) z in
          let (p, q, aa) = constraint_gen' __G (s, z', c) in (p, q, aa)
      | (__G, (Elt m)::s, TPi (MINUS, a, z), c) ->
          let z' = subst_tp (TermDot (m, a, Id)) z in
          let (p, q, aa) = constraint_gen' __G (s, z', c) in
          (p, ((m, a) :: q), aa)
      | (__G, (AElt m)::s, TPi (PLUS, a, z), c) ->
          let a' = synth (__G, m) in
          let z' = subst_tp (TermDot ((ATerm m), a, Id)) z in
          let (p, q, aa) = constraint_gen' __G (s, z', c) in
          (((((TypeC (a, a')) :: p), q, aa))
            (* Same PERF comment here as above *))
      | (__G, (Ascribe (m, a'))::s, TPi (PLUS, a, z), c) ->
          let z' = subst_tp (TermDot ((NTerm m), a, Id)) z in
          let (p, q, aa) = constraint_gen' __G (s, z', c) in
          (((((TypeC (a, a')) :: p), q, aa))
            (* As well as here *))
      | (_, _) -> raise (Error "spine doesn't match type")(* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)
    let rec tp_constraint_gen __28__ __29__ __30__ =
      match (__28__, __29__, __30__) with
      | (__G, [], Type) -> ([], [])
      | (__G, (Omit)::s, KPi (OMIT, a, z)) ->
          let (ev : evar) = ((ref NONE), a) in
          let z' = subst_knd (EVarDotId ev) z in
          let (p, q) = tp_constraint_gen __G (s, z') in (p, q)
      | (__G, (Elt m)::s, KPi (MINUS, a, z)) ->
          let z' = subst_knd (TermDot (m, a, Id)) z in
          let (p, q) = tp_constraint_gen __G (s, z') in (p, ((m, a) :: q))
      | (__G, (AElt m)::s, KPi (PLUS, a, z)) ->
          let a' = synth (__G, m) in
          let z' = subst_knd (TermDot ((ATerm m), a, Id)) z in
          let (p, q) = tp_constraint_gen __G (s, z') in
          (((TypeC (a, a')) :: p), q)
      | (__G, (Ascribe (m, a'))::s, KPi (PLUS, a, z)) ->
          let z' = subst_knd (TermDot ((NTerm m), a, Id)) z in
          let (p, q) = tp_constraint_gen __G (s, z') in
          (((TypeC (a, a')) :: p), q)
      | (_, _) -> raise (Error "spine doesn't match type")
    let rec check_equality_constraints p = List.all eq_c_true p
    let rec check_typing_constraints (__G) q =
      List.all (fun m -> fun a -> check (__G, m, a)) q
    let rec matching_succeeds (__G) p q =
      let p' = matching p in
      let _ =
        if check_equality_constraints p'
        then ()
        else raise (Matching "residual equality constraints failed") in
      let _ =
        if check_typing_constraints __G q
        then ()
        else raise (Matching "residual typing constraints failed") in
      ((true__)
        (* evar side-effects affect q, raises Matching if matching fails *))
    let rec check_spinelt __31__ __32__ __33__ =
      match (__31__, __32__, __33__) with
      | (__G, Elt t, a) -> check (__G, t, a)
      | (__G, AElt t, a) -> check (__G, (ATerm t), a)
      | (__G, Ascribe (t, a), a') ->
          (tp_eq (a, a')) && (check (__G, (NTerm t), a))
      | (__G, Omit, _) -> raise (Error "cannot check omitted arguments")
    let rec check __34__ __35__ __36__ =
      match (__34__, __35__, __36__) with
      | (__G, NTerm (Lam t), TPi (_, a, b)) ->
          check ((ctxcons (a, __G)), t, b)
      | (__G, ATerm t, a) ->
          (try tp_eq ((synth (__G, t)), a) with | Error s -> false__)
      | (__G, NTerm (NRoot (Const n, s)), a) ->
          let b =
            match Sgn.classifier n with
            | tclass b -> b
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q, _) = constraint_gen __G (s, b, (CG_CHECK a)) in
          ((matching_succeeds __G (p, q))
            (* creates ref cells for evars *))
      | _ -> false__
    let rec check_kind __37__ __38__ =
      match (__37__, __38__) with
      | (__G, Type) -> true__
      | (__G, KPi (OMIT, a, k)) ->
          (check_type CON_LF (__G, a)) &&
            ((check_kind ((ctxcons (a, __G)), k)) &&
               (Strict.check_strict_kind k))
      | (__G, KPi (_, a, k)) ->
          (check_type CON_LF (__G, a)) &&
            (check_kind ((ctxcons (a, __G)), k))
    let rec check_type __39__ __40__ __41__ =
      match (__39__, __40__, __41__) with
      | (_, __G, TRoot (n, s)) ->
          let k =
            match Sgn.classifier n with
            | kclass k -> k
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q) = tp_constraint_gen __G (s, k) in
          ((matching_succeeds __G (p, q))
            (* creates ref cells for evars *))
      | (con, __G, TPi (OMIT, a, b)) ->
          let plusconst =
            match con with
            | CON_LF ->
                raise
                  (Error "TPi(OMIT) where a pure LF function type expected")
            | CON_PLUS -> true__
            | CON_MINUS -> false__ in
          (check_type CON_LF (__G, a)) &&
            ((check_type con ((ctxcons (a, __G)), b)) &&
               (Strict.check_strict_type plusconst b))
      | (con, __G, TPi (m, a, b)) ->
          (match (con, m) with
           | (CON_LF, PLUS) ->
               raise
                 (Error "TPi(PLUS) where a pure LF function type expected")
           | _ ->
               (check_type CON_LF (__G, a)) &&
                 (check_type con ((ctxcons (a, __G)), b)))
    let rec check_type' __42__ __43__ __44__ =
      match (__42__, __43__, __44__) with
      | (__G, Type, []) -> true__
      | (__G, KPi (_, a, k), m::s) ->
          let _ =
            if check_spinelt (__G, m, a)
            then ()
            else raise (Error "argument type mismatch") in
          let k' = subst_knd (TermDot ((termof m), a, Id)) k in
          check_type' (__G, k', s)
      | _ -> false__
    let rec synth __45__ __46__ =
      match (__45__, __46__) with
      | (__G, ARoot (Var n, s)) -> synth' (__G, (ctxLookup (__G, n)), s)
      | (__G, ARoot (Const n, s)) ->
          let b =
            match Sgn.classifier n with
            | tclass b -> b
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q, aopt) = constraint_gen __G (s, b, CG_SYNTH) in
          let _ = matching_succeeds __G (p, q) in ((Option.valOf aopt)
            (* creates ref cells for evars *)(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *)
            (* raises Matching if not *)(* by invariant, aopt must be Some *))
      | (__G, (ERoot _ as t)) -> elt_synth (__G, (eroot_elim_plus t))
    let rec synth' __47__ __48__ __49__ =
      match (__47__, __48__, __49__) with
      | (__G, (TRoot (_, _) as a), []) -> a
      | (__G, TPi (_, a, b), m::s) ->
          let _ =
            if check_spinelt (__G, m, a)
            then ()
            else raise (Error "argument type mismatch") in
          let b' = subst_tp (TermDot ((termof m), a, Id)) b in
          synth' (__G, b', s)
      | _ -> raise (Error "applying nonfunction to argument")
    let rec elt_synth __50__ __51__ =
      match (__50__, __51__) with
      | (__G, AElt t) -> synth (__G, t)
      | (__G, Ascribe (t, a)) ->
          if check (__G, (NTerm t), a)
          then a
          else raise (Error "ascription doesn't check")
      | (__G, Elt _) ->
          raise (Error "trying to synthesize a merely checkable element")
      | (__G, Omit) ->
          raise (Error "trying to synthesize an omitted argument")
    let rec check_plusconst_type t = check_type CON_PLUS ([], t)
    let rec check_minusconst_type t = check_type CON_MINUS ([], t)
    let rec check_strictness_type __52__ __53__ =
      match (__52__, __53__) with
      | (_, TRoot (n, s)) -> true__
      | (plusconst, TPi (OMIT, _, b)) ->
          (check_strictness_type plusconst b) &&
            (Strict.check_strict_type plusconst b)
      | (plusconst, TPi (_, _, b)) -> check_strictness_type plusconst b
    let check_plusconst_strictness = check_strictness_type true__
    let check_minusconst_strictness = check_strictness_type false__
  end;;
