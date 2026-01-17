
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
      | EltC of
      (((spinelt)(* left side is open, (with respect to outer pi bindings)
           and right side is closed *)
      (* All Pis, and [Pi] can use strict occs in later args
                              and in return type. *)
      (* Pi-, Pi+, [Pi] matched by strict occ in later args
                             not necessarily in return type *)
      (* Pi- only *)) * spinelt) 
      | SpineC of (spine * spine) 
      | TypeC of (tp * tp) 
    type nonrec tp_c = (term * tp)
    let rec tp_eq =
      function
      | (TRoot (((n)(* equality checking *)), sp), TRoot
         (n', sp')) -> type_const_head_eq (n, n', sp, sp')
      | (TPi (m, a, b), TPi (m', a', b')) ->
          (m = m') && ((tp_eq (a, a')) && (tp_eq (b, b')))
      | _ -> false__
    let rec sp_eq =
      function
      | ([], []) -> true__
      | (e::sp, e'::sp') -> (elt_eq (e, e')) && (sp_eq (sp, sp'))
      | _ -> false__
    let rec elt_eq (t, t') =
      elt_eq' ((elt_eroot_elim t), (elt_eroot_elim t'))
    let rec elt_eq' =
      function
      | (Elt t, Elt t') -> tm_eq (t, t')
      | (AElt t, AElt t') -> atm_eq (t, t')
      | (Ascribe (t, a), Ascribe (t', a')) ->
          (ntm_eq (t, t')) && (tp_eq (a, a'))
      | (Omit, Omit) -> true__
      | _ -> false__
    let rec tm_eq =
      function
      | (NTerm t, NTerm t') -> ntm_eq (t, t')
      | (ATerm t, ATerm t') -> atm_eq (t, t')
      | _ -> false__
    let rec atm_eq =
      function
      | ((ARoot (Const n, sp) as tm), (ARoot (Const n', sp') as tm')) ->
          const_head_eq (n, n', sp, sp', (ATerm tm), (ATerm tm'))
      | (ARoot (Var n, sp), ARoot (Var n', sp')) ->
          (n = n') && (sp_eq (sp, sp'))
      | _ -> false__
    let rec ntm_eq
      (((t)(* ERoots are taken care of at the spine element level *)),
       t')
      = ntm_eq' ((ntm_eroot_elim t), (ntm_eroot_elim t'))
    let rec ntm_eq' =
      function
      | ((NRoot (Const n, sp) as tm), (NRoot (Const n', sp') as tm')) ->
          const_head_eq (n, n', sp, sp', (NTerm tm), (NTerm tm'))
      | (Lam t, Lam t') -> tm_eq (t, t')
      | _ -> false__
    let rec const_head_eq
      (((n)(* determine whether two roots are equal. n and n' are the cids of the heads, whether the
           roots happen to be nroots or aroots. sp and sp' are the spines, and tm and tm' are the
           entire roots. *)),
       n', sp, sp', tm, tm')
      =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let redux t n sp =
        reduce ((srTerm (t, (typeOf (Sgn.classifier n)))), sp) in
      match (eq_and_strict, def, def') with
      | (true__, _, _) -> sp_eq (sp, sp')
      | (false__, Sgn.DEF_NONE, Sgn.DEF_NONE) -> false__
      | (_, DEF_TERM t, DEF_TERM t') ->
          tm_eq ((redux t n sp), (redux t' n' sp'))
      | (_, DEF_TERM t, Sgn.DEF_NONE) -> tm_eq ((redux t n sp), tm')
      | (_, Sgn.DEF_NONE, DEF_TERM t') -> tm_eq (tm, (redux t' n' sp'))
      | _ -> raise (Syntax "invariant violation")
    let rec type_const_head_eq
      (((n)(* similar thing for atomic types. Here we need not include redundant arguments for the entire
            TRoot since there is only one kind of TRoot (not both ARoot and NRoot in the case of terms)
            so we just build it back up from scratch *)),
       n', sp, sp')
      =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
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
      | EltC
          (((e)(* is an equality constraint satisfied? *)),
           e')
          -> elt_eq (e, e')
      | SpineC (s, s') -> sp_eq (s, s')
      | TypeC (a, a') -> tp_eq (a, a')
    type nonrec ppsubst =
      (((int)(* ([i1, i2, ... , in], m) represents i1.i2. ... in . shift^m *)
        (* The type ppsubst is a compact way of representing a
           class of substitutions that contains all of the pattern
           substitutions. These are the "prepattern" substitutions,
           the ones that are of the form 
           i1.i2. ... in . shift^m
           where all the i1...in are variables. *))
        list * int)
    let rec pp_shift
      (((vs)(* pp_shift pps m: compute pps o shift^m *)),
       shift)
      m =
      let len = length vs in
      if m < len
      then ((List.drop (vs, m)), shift)
      else ([], ((m - len) + shift))
    let rec pp_nth
      (((vs)(* pp_nth: extract the result of applying a ppsubst to the nth variable *)),
       shift)
      n =
      let len = length vs in
      if n < len then List.nth (vs, n) else (n - len) + shift
    let rec pp_o
      (((pps)(* pp_o: compose two ppsubsts *)), (vs, shift))
      =
      let (vs', shift') = pp_shift pps shift in
      (((map (pp_nth pps) vs) @ vs'), shift')
    let rec pp_comp
      ((ppsl)(* pp_comp: compose a list of ppsubsts *)) =
      foldr pp_o ([], 0) ppsl
    let rec pp_normalize
      ((s)(* pp_normalize s
           if a substitution s is equal to a 'prepattern'
           i1.i2. ... in . shift^m (no restriction on the i's being distinct)
           returns ([i1, i2, ... , in], m).
           Otherwise raises Domain. *))
      = pp_normalize' s
    let rec pp_normalize' =
      function
      | Id -> ([], 0)
      | TermDot (t, a, s) ->
          let ((v)(* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *))
            =
            try Strict.eta_contract_var (Elt t)
            with | Strict.EtaContract -> raise Domain in
          let (vs, shift) = pp_normalize' s in ((v :: vs), shift)
      | ZeroDotShift s ->
          let (vs, shift) = pp_normalize' s in
          ((0 :: (map (function | x -> x + 1) vs)), (shift + 1))
      | Shift (n, m) ->
          ((List.tabulate
              (((n)
                (* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)),
                (function | x -> x))), (n + m))
      | EVarDot _ -> raise Domain
      | VarOptDot (((no)(* XXX: Correct??? *)), s) ->
          let (vs, shift) = pp_normalize' s in
          (match no with
           | SOME n -> ((n :: vs), shift)
           | NONE -> raise (Error "??? I'm not sure this is really wrong"))
      | Compose sl -> prepattern (substs_comp sl)
    let rec prepattern
      (s :
        ((subst)(* raises Domain if it is not a prepattern *)(* prepattern: convert a subst into a ppsubst *)))
      = pp_normalize s
    let rec pp_ispat =
      function
      | ((([])(* pp_ispat: is this ppsubst a pattern substitution? *)),
         shift) -> true__
      | (n::s, shift) ->
          let isn x = x = n in
          let hasn s = List.exists isn s in
          (n < shift) && ((not (hasn s)) && (pp_ispat (s, shift)))
    let rec makesubst =
      function
      | ((([])(* take a list of int options and a shift value and
        produce an actual substitution. This is morally a one-sided
        inverse to pp_normalize *)),
         0) -> Id
      | ([], shift) -> Shift (0, shift)
      | (v::vs, shift) -> VarOptDot (v, (makesubst (vs, shift)))
    let rec pp_invert
      (((vs)(* take in a ppsubst and return a substitution (which may involve VarOptDots) that is its inverse. *)),
       shift)
      =
      let inds = List.tabulate (shift, (function | x -> x)) in
      let search arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | (n, [], (x : int)) -> NONE
        | (n, h::tl, x) -> if x = h then SOME n else search (n + 1) tl x in
      makesubst ((map (search 0 vs) inds), (length vs))
    let rec flex_left =
      function
      | (((ref
             ((NONE)(* Here begins all the matching code.
           flex_left takes an uninstantiated evar, a substitution, and a right-hand-side of an equation.
           The equation is
           E[sl] = RHS
           If it can successfully instantiate E with RHS[sl^-1], then it does so
           imperatively and returns ().

           If sl is not pattern it raises NonPattern.
           If RHS is not in the range of sl, then MissingVar is raised by substitution *))
             as r),
          a),
         (s : subst), rhs) ->
          let pps = try prepattern s with | Domain -> raise NonPattern in
          let _ = if pp_ispat pps then () else raise NonPattern in
          let ppsi = pp_invert pps in
          let rhs' = subst_term ppsi (termof rhs) in
          let _ = (:=) r SOME rhs' in ()
      | _ -> raise (Error "evar invariant violated")
    let rec just_one
      ((c)(* match_one' takes an equation (which by invariant does not
           have an instantiated evar on the left, and is ground on the
           right) and returns a list of smaller equations that are
           equivalent to it, or else throws NonPattern in the event
           that it finds a flex-rigid equation where the flex side is
           not pattern. *)
      (* XXX this just_one stuff is here for debugging: replace with match_one *))
      = [c]
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
      | EltC
          (((elt)(* PERF: this second elt_eroot_elim on elt' seems like it ought to be unnecessary if
	     I eliminate all eroots at synth time *)),
           elt')
          -> match_one' (EltC ((elt_eroot_elim elt), (elt_eroot_elim elt')))
      | e -> match_one' e
    let rec match_two e1 e2 = [e1; e2]
    let rec match_const_head (n, n', s, s', elt, elt', err) =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let redux t n sp =
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
    let rec match_type_const_head (n, n', s, s', err) =
      let def = Sgn.def n in
      let def' = Sgn.def n' in
      let eq_and_strict =
        (n = n') && ((def = Sgn.DEF_NONE) || (not (Sgn.abbreviation n))) in
      let redux a n sp = tp_reduce (a, (kindOf (Sgn.classifier n)), sp) in
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
      let matching' =
        function
        | (c::p, p') ->
            (try let eqs = match_one c in matching' ((eqs @ p), p')
             with | NonPattern -> matching' (p, (c :: p')))
        | ([], p') -> p' in
      matching' (p, [])
    let rec ctxcons
      (((a)(*	fun ctxcons (a, g) = map (shift_tp 0) (a::g) *)),
       g)
      = a :: g
    type cg_mode =
      | CG_SYNTH 
      | CG_CHECK of tp 
    let rec constraint_gen
      ((g)(* 	val constraint_gen : tp list -> spine * tp * cg_mode -> eq_c list * tp_c list
        fun constraint_gen g (s, z, c) = (p, q, aopt) *)
      (* invariants: 
	   s is ground
	   if c is CG_CHECK c', then c' is ground 
           right-hand sides of p,q are ground
           left-hand sides of p,q and z may involve evars
           
           the returned aopt...
           ... is SOME of a type if c was CG_SYNTH
           ... is NONE           if c was CG_CHECK of something *))
      (s, z, c) = constraint_gen' g (s, z, c)
    let rec constraint_gen' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, ([], (TRoot _ as a), CG_CHECK (TRoot _ as a'))) ->
          ([TypeC (a, a')], [], NONE)
      | (((g)(* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)),
         ([], TRoot (n, s), CG_SYNTH)) -> ([], [], (SOME (TRoot (n, s))))
      | (g, ((Omit)::s, TPi (OMIT, a, z), c)) ->
          let (ev : evar) = ((ref NONE), a) in
          let z' = subst_tp (EVarDotId ev) z in
          let (p, q, aa) = constraint_gen' g (s, z', c) in (p, q, aa)
      | (g, ((Elt m)::s, TPi (MINUS, a, z), c)) ->
          let z' = subst_tp (TermDot (m, a, Id)) z in
          let (p, q, aa) = constraint_gen' g (s, z', c) in
          (p, ((m, a) :: q), aa)
      | (g, ((AElt m)::s, TPi (PLUS, a, z), c)) ->
          let a' = synth (g, m) in
          let z' = subst_tp (TermDot ((ATerm m), a, Id)) z in
          let (p, q, aa) = constraint_gen' g (s, z', c) in
          (((TypeC
               (((a)(* Same PERF comment here as above *)),
                 a'))
              :: p), q, aa)
      | (g, ((Ascribe (m, a'))::s, TPi (PLUS, a, z), c)) ->
          let z' = subst_tp (TermDot ((NTerm m), a, Id)) z in
          let (p, q, aa) = constraint_gen' g (s, z', c) in
          (((TypeC (((a)(* As well as here *)), a')) :: p),
            q, aa)
      | (_, _) -> raise (Error "spine doesn't match type")
    let rec tp_constraint_gen arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((g)(* similar to above but we just have a putative type and its kind, and return nothing but constraints *)),
         ([], Type)) -> ([], [])
      | (g, ((Omit)::s, KPi (OMIT, a, z))) ->
          let (ev : evar) = ((ref NONE), a) in
          let z' = subst_knd (EVarDotId ev) z in
          let (p, q) = tp_constraint_gen g (s, z') in (p, q)
      | (g, ((Elt m)::s, KPi (MINUS, a, z))) ->
          let z' = subst_knd (TermDot (m, a, Id)) z in
          let (p, q) = tp_constraint_gen g (s, z') in (p, ((m, a) :: q))
      | (g, ((AElt m)::s, KPi (PLUS, a, z))) ->
          let a' = synth (g, m) in
          let z' = subst_knd (TermDot ((ATerm m), a, Id)) z in
          let (p, q) = tp_constraint_gen g (s, z') in
          (((TypeC (a, a')) :: p), q)
      | (g, ((Ascribe (m, a'))::s, KPi (PLUS, a, z))) ->
          let z' = subst_knd (TermDot ((NTerm m), a, Id)) z in
          let (p, q) = tp_constraint_gen g (s, z') in
          (((TypeC (a, a')) :: p), q)
      | (_, _) -> raise (Error "spine doesn't match type")
    let rec check_equality_constraints p = List.all eq_c_true p
    let rec check_typing_constraints (g) q =
      List.all (function | (m, a) -> check (g, m, a)) q
    let rec matching_succeeds
      ((g)(* returns true on success or raises Matching on failure *))
      (p, q) =
      let p' = matching p in
      let ((_)(* evar side-effects affect q, raises Matching if matching fails *))
        =
        if check_equality_constraints p'
        then ()
        else raise (Matching "residual equality constraints failed") in
      let _ =
        if check_typing_constraints g q
        then ()
        else raise (Matching "residual typing constraints failed") in
      true__
    let rec check_spinelt =
      function
      | (g, Elt t, a) -> check (g, t, a)
      | (g, AElt t, a) -> check (g, (ATerm t), a)
      | (g, Ascribe (t, a), a') ->
          (tp_eq (a, a')) && (check (g, (NTerm t), a))
      | (g, Omit, _) -> raise (Error "cannot check omitted arguments")
    let rec check =
      function
      | (g, NTerm (Lam t), TPi (_, a, b)) -> check ((ctxcons (a, g)), t, b)
      | (g, ATerm t, a) ->
          (try tp_eq ((synth (g, t)), a) with | Error s -> false__)
      | (g, NTerm (NRoot (Const n, s)), a) ->
          let b =
            match Sgn.classifier n with
            | tclass b -> b
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q, _) = constraint_gen g (s, b, (CG_CHECK a)) in
          matching_succeeds ((g)
            (* creates ref cells for evars *)) (p, q)
      | _ -> false__
    let rec check_kind =
      function
      | (g, Type) -> true__
      | (g, KPi (OMIT, a, k)) ->
          (check_type CON_LF (g, a)) &&
            ((check_kind ((ctxcons (a, g)), k)) &&
               (Strict.check_strict_kind k))
      | (g, KPi (_, a, k)) ->
          (check_type CON_LF (g, a)) && (check_kind ((ctxcons (a, g)), k))
    let rec check_type arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (_, (g, TRoot (n, s))) ->
          let k =
            match Sgn.classifier n with
            | kclass k -> k
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q) = tp_constraint_gen g (s, k) in
          matching_succeeds ((g)
            (* creates ref cells for evars *)) (p, q)
      | (con, (g, TPi (OMIT, a, b))) ->
          let plusconst =
            match con with
            | CON_LF ->
                raise
                  (Error "TPi(OMIT) where a pure LF function type expected")
            | CON_PLUS -> true__
            | CON_MINUS -> false__ in
          (check_type CON_LF (g, a)) &&
            ((check_type con ((ctxcons (a, g)), b)) &&
               (Strict.check_strict_type plusconst b))
      | (con, (g, TPi (m, a, b))) ->
          (match (con, m) with
           | (CON_LF, PLUS) ->
               raise
                 (Error "TPi(PLUS) where a pure LF function type expected")
           | _ ->
               (check_type CON_LF (g, a)) &&
                 (check_type con ((ctxcons (a, g)), b)))
    let rec check_type' =
      function
      | (((g)(* check a type spine *)), Type, []) -> true__
      | (g, KPi (_, a, k), m::s) ->
          let _ =
            if check_spinelt (g, m, a)
            then ()
            else raise (Error "argument type mismatch") in
          let k' = subst_knd (TermDot ((termof m), a, Id)) k in
          check_type' (g, k', s)
      | _ -> false__
    let rec synth =
      function
      | (g, ARoot (Var n, s)) -> synth' (g, (ctxLookup (g, n)), s)
      | (g, ARoot (Const n, s)) ->
          let b =
            match Sgn.classifier n with
            | tclass b -> b
            | _ -> raise (Error "signature invariant violated!") in
          let (p, q, aopt) = constraint_gen g (s, b, CG_SYNTH) in
          let ((_)(* creates ref cells for evars *)(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *))
            = matching_succeeds g (p, q) in
          ((Option.valOf ((aopt)
              (* raises Matching if not *)))
            (* by invariant, aopt must be SOME *))
      | (g, (ERoot _ as t)) -> elt_synth (g, (eroot_elim_plus t))
    let rec synth' =
      function
      | (g, (TRoot (_, _) as a), []) -> a
      | (g, TPi (_, a, b), m::s) ->
          let _ =
            if check_spinelt (g, m, a)
            then ()
            else raise (Error "argument type mismatch") in
          let b' = subst_tp (TermDot ((termof m), a, Id)) b in
          synth' (g, b', s)
      | _ -> raise (Error "applying nonfunction to argument")
    let rec elt_synth =
      function
      | (g, AElt t) -> synth (g, t)
      | (g, Ascribe (t, a)) ->
          if check (g, (NTerm t), a)
          then a
          else raise (Error "ascription doesn't check")
      | (g, Elt _) ->
          raise (Error "trying to synthesize a merely checkable element")
      | (g, Omit) -> raise (Error "trying to synthesize an omitted argument")
    let rec check_plusconst_type t = check_type CON_PLUS ([], t)
    let rec check_minusconst_type t = check_type CON_MINUS ([], t)
    let rec check_strictness_type arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((_)(* check_strictness_type : bool -> tp -> bool

   For a type B = Pi x1 : A1 . Pi x2 : A2 ... a . S (where the Pis
   may be omit or plus or minus) 
   and plus_const : bool
   the call
   check_strictness_type plus_const B
   returns true iff for every i, the following holds:
     the variable xi has either a strict occurrence in Aj for
     some j > i where xj is bound by a plus-Pi, or else 
     plus_const = false and xi has a strict occurrence in a . S.

  This function does *not* check to make sure types such as A1
  do not contain omit-Pis and plus-Pis. This test is carried
  out in check_type. check_strictness_type is useful mainly when
  we are simply deciding, by trial and error, which of the arguments
  to B we should omit and which to force to be synthesizing.
 *)),
         TRoot (n, s)) -> true__
      | (plusconst, TPi (OMIT, _, b)) ->
          (check_strictness_type plusconst b) &&
            (Strict.check_strict_type plusconst b)
      | (plusconst, TPi (_, _, b)) -> check_strictness_type plusconst b
    let check_plusconst_strictness = check_strictness_type true__
    let check_minusconst_strictness = check_strictness_type false__
  end;;
