
module Syntax =
  struct
    exception Syntax of string 
    exception MissingVar 
    type mode =
      | MINUS 
      | PLUS 
      | OMIT 
    type nterm =
      | Lam of term 
      | NRoot of (head * spine) 
    and aterm =
      | ARoot of (head * spine) 
      | ERoot of (evar * subst) 
    and head =
      | Var of int 
      | Const of int 
    and tp =
      | TRoot of (int * spine) 
      | TPi of (mode * tp * tp) 
    and knd =
      | Type 
      | KPi of (mode * tp * knd) 
    and spinelt =
      | Elt of term 
      | AElt of aterm 
      | Ascribe of (nterm * tp) 
      | Omit 
    and term =
      | NTerm of nterm 
      | ATerm of aterm 
    and subst =
      | Id 
      | Shift of (int * int) 
      | ZeroDotShift of subst 
      | TermDot of (term * tp * subst) 
      | EVarDot of (evar * subst list * subst) 
      | VarOptDot of (int option * subst) 
      | Compose of subst list 
    type spine = spinelt list
    and evar = (term option ref * tp)
    (* special hack for type functions used only in tp_reduce *)
    type tpfn =
      | TpfnType of tp [@sml.renamed "tpfnType"]
      | TpfnLam of tpfn [@sml.renamed "tpfnLam"]
    let rec EVarDotId ev = EVarDot (ev, [], Id)
    (*	type decl = string * Parse.term *)
    (*	type ctx = decl list *)
    type class__ =
      | Kclass of knd [@sml.renamed "kclass"]
      | Tclass of tp [@sml.renamed "tclass"]
    (* termof elm
        returns the term part of the spine element elm *)
    let rec termof =
      function
      | Elt t -> t
      | AElt t -> ATerm t
      | Ascribe (t, a) -> NTerm t
      | Omit ->
          raise
            (Syntax
               "invariant violated: arguments to variables cannot be omitted")
    type subst_result =
      | srVar of int [@sml.renamed "srVar"]
      | srTerm of (term * tp) [@sml.renamed "srTerm"]
      | srEVar of (evar * subst list)
      [@sml.renamed "srEVar"]
    exception Debugs of (subst_result * spinelt list) 
    let rec curryfoldr sf sl x = foldr (function | (s, x') -> sf s x') x sl
    (* lower (a, sp)
           supposing we have an evar of (potentially higher-order)
           type a, applied to a spine sp, return the lowered type of
           that evar and a substitution to apply it to *)
    (* XXX: so we're not carrying out substitutions over the type
                as we recurse down: is this right? I think it is. *)
    let rec lower arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (acc, ((TRoot _ as a), [])) -> (a, acc)
      | (acc, (TPi (m, a, b), elt::sp)) ->
          let newacc = TermDot ((termof elt), (subst_tp acc a), acc) in
          lower newacc (b, sp)
      | (_, _) -> raise (Syntax "type mismatch in lowering")(*
	  | lower base (TPi(m,a,b), elt::sp) = 
	    let
		val (aa,subst) = lower base (b, sp)
	    in
		(aa, TermDot(termof elt, a, subst))
	    end *)
    let rec substNth =
      function
      | (Id, n) -> srVar n
      | (ZeroDotShift s, n) ->
          if n = 0
          then srVar 0
          else
            (match substNth (s, (n - 1)) with
             | srTerm (t, a) -> srTerm ((shift t), (shift_tp 0 a))
             | srVar n -> srVar (n + 1)
             | srEVar (ev, sl) -> srEVar (ev, ((Shift (0, 1)) :: sl)))
      | (TermDot (m, a, s), n) ->
          if n = 0 then srTerm (m, a) else substNth (s, (n - 1))
      | (EVarDot (ev, sl, s), n) ->
          if n = 0 then srEVar (ev, sl) else substNth (s, (n - 1))
      | (Shift (n, m), n') -> if n' >= n then srVar (n' + m) else srVar n'
      | (VarOptDot (no, s), n') ->
          if n' = 0
          then (match no with | Some n -> srVar n | None -> raise MissingVar)
          else substNth (s, (n' - 1))
      | (Compose [], n) -> srVar n
      | (Compose (h::tl), n) -> subst_sr h (substNth ((Compose tl), n))
    let rec subst_sr arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, srTerm (t, a)) -> srTerm ((subst_term s t), (subst_tp s a))
      | (s, srVar n) -> substNth (s, n)
      | (s, srEVar (ev, sl)) -> srEVar (ev, (s :: sl))
    let rec subst_spinelt arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (Id, x) -> x
      | (s, Elt t) -> Elt (subst_term s t)
      | (s, AElt t) -> subst_aterm_plus s t
      | (s, Ascribe (t, a)) -> Ascribe ((subst_nterm s t), (subst_tp s a))
      | (s, Omit) -> Omit
    let rec subst_spine s sp = map (subst_spinelt s) sp
    let rec subst_term arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, ATerm t) -> subst_aterm s t
      | (s, NTerm t) -> NTerm (subst_nterm s t)
    let rec subst_nterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, Lam t) -> Lam (subst_term (ZeroDotShift s) t)
      | (s, NRoot (h, sp)) -> NRoot (h, (subst_spine s sp))
    let rec subst_aterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, ARoot (Const n, sp)) ->
          ATerm (ARoot ((Const n), (subst_spine s sp)))
      | (s, ARoot (Var n, sp)) ->
          reduce ((substNth (s, n)), (subst_spine s sp))
      | (s, ERoot (((ref (None), _) as ev), sl)) ->
          ATerm (ERoot (ev, (subst_compose (s, sl))))
      | (s, (ERoot _ as t)) -> subst_term s (eroot_elim t)(* XXX right??? *)
    let rec subst_aterm_plus arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, ARoot (Const n, sp)) ->
          AElt (ARoot ((Const n), (subst_spine s sp)))
      | (s, ARoot (Var n, sp)) ->
          reduce_plus ((substNth (s, n)), (subst_spine s sp))
      | (s, ERoot (((ref (None), _) as ev), sl)) ->
          AElt (ERoot (ev, (subst_compose (s, sl))))
      | (s, (ERoot _ as t)) -> subst_spinelt s (eroot_elim_plus t)
    let rec subst_tp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, TRoot (h, sp)) -> TRoot (h, (subst_spine s sp))
      | (s, TPi (m, b, b')) ->
          TPi (m, (subst_tp s b), (subst_tp (ZeroDotShift s) b'))
    let rec subst_knd arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (s, Type) -> Type
      | (s, KPi (m, b, k)) ->
          KPi (m, (subst_tp s b), (subst_knd (ZeroDotShift s) k))
    let rec reduce =
      function
      | (srVar n, sp) -> ATerm (ARoot ((Var n), sp))
      | (srTerm (NTerm (Lam n), TPi (_, a, b)), h::sp) ->
          let s = TermDot ((termof h), a, Id) in
          let n' = subst_term s n in
          let b' = subst_tp s b in reduce ((srTerm (n', b')), sp)
      | (srTerm ((NTerm (NRoot (h, sp)) as t), a), []) -> t
      | (srTerm ((ATerm (ARoot (h, sp)) as t), a), []) -> t
      | (srTerm (ATerm (ERoot ((ref (Some _), _), _) as t), a), []) ->
          reduce ((srTerm ((eroot_elim t), a)), [])
      | (srTerm (ATerm (ERoot ((ref (None), _), _) as t), a), []) -> ATerm t
      | (srEVar ((x, a), sl), sp) ->
          let (a', subst) = lower (substs_comp sl) (a, sp) in
          ATerm (ERoot ((x, a'), subst))
      | _ -> raise (Syntax "simplified-type mismatch in reduction")
    let rec reduce_plus =
      function
      | (srVar n, sp) -> AElt (ARoot ((Var n), sp))
      | (srTerm (NTerm (Lam n), TPi (_, a, b)), h::sp) ->
          let s = TermDot ((termof h), a, Id) in
          let n' = subst_term s n in
          let b' = subst_tp s b in reduce_plus ((srTerm (n', b')), sp)
      | (srTerm (NTerm (NRoot (h, sp) as t), a), []) -> Ascribe (t, a)
      | (srTerm (ATerm (ARoot (h, sp) as t), a), []) -> AElt t
      | (srTerm (ATerm (ERoot ((ref (Some _), _), _) as t), a), []) ->
          reduce_plus ((srTerm ((eroot_elim t), a)), [])
      | (srTerm (ATerm (ERoot ((ref (None), _), _) as t), a), []) -> AElt t
      | (srEVar ((x, a), sl), sp) ->
          let (a', subst) = lower (substs_comp sl) (a, sp) in
          AElt (ERoot ((x, a'), subst))
      | (x, y) ->
          (raise (Debugs (x, y));
           raise (Syntax "simplified-type mismatch in reduction"))
    let rec tp_reduce (a, k, sp) =
      let rec subst_tpfn arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (s, tpfnLam a) -> tpfnLam (subst_tpfn (ZeroDotShift s) a)
        | (s, tpfnType a) -> tpfnType (subst_tp s a) in
      let rec tp_reduce' =
        function
        | (tpfnLam a, KPi (_, b, k), h::sp) ->
            let s = TermDot ((termof h), b, Id) in
            let a' = subst_tpfn s a in
            let k' = subst_knd s k in tp_reduce' (a', k', sp)
        | (tpfnType a, Type, []) -> a
        | _ -> raise (Syntax "simplified-kind mismatch in type reduction") in
      let rec wrap =
        function
        | (a, KPi (_, b, k)) -> tpfnLam (wrap (a, k))
        | (a, Type) -> tpfnType a in
      let aw = wrap (a, k) in tp_reduce' (aw, k, sp)
    let rec substs_term x = curryfoldr subst_term x
    let rec substs_tp x = curryfoldr subst_tp x
    let rec eroot_elim =
      function
      | ERoot ((ref (Some t), a), subst) -> subst_term subst t
      | x -> ATerm x
    let rec eroot_elim_plus =
      function
      | ERoot ((ref (Some t), a), subst) ->
          let newt = subst_term subst t in
          (match newt with
           | ATerm t -> AElt t
           | NTerm t -> Ascribe (t, (subst_tp subst a)))
      | x -> AElt x
    let rec composeNth (s, n, s') =
      let s'' = subst_compose (s, s') in
      match substNth (s, n) with
      | srVar n' -> VarOptDot ((Some n'), s'')
      | srTerm (t, a) -> TermDot (t, a, s'')
      | srEVar (ev, sl) -> EVarDot (ev, sl, s'')
    let rec subst_compose =
      function
      | (Id, s) -> s
      | (s, Id) -> s
      | (s, Shift (_, 0)) -> s
      | (Shift (_, 0), s) -> s
      | (s, Compose []) -> s
      | (Compose [], s) -> s
      | (s, Compose (h::tl)) ->
          subst_compose ((subst_compose (s, h)), (Compose tl))
      | (Compose (h::tl), s) ->
          subst_compose (h, (subst_compose ((Compose tl), s)))
      | (ZeroDotShift s, Shift (0, m)) ->
          subst_compose
            ((subst_compose ((Shift (0, 1)), s)), (Shift (0, (m - 1))))
      | (TermDot (_, _, s), Shift (0, m)) ->
          subst_compose (s, (Shift (0, (m - 1))))
      | (EVarDot (_, _, s), Shift (0, m)) ->
          subst_compose (s, (Shift (0, (m - 1))))
      | (VarOptDot (_, s), Shift (0, m)) ->
          subst_compose (s, (Shift (0, (m - 1))))
      | (Shift (0, m), Shift (0, m')) -> Shift (0, (m + m'))
      | (Shift (n, m'), (Shift (0, m) as t)) ->
          subst_compose ((ZeroDotShift (Shift ((n - 1), m'))), t)
      | (s, Shift (n, m)) ->
          subst_compose (s, (ZeroDotShift (Shift ((n - 1), m))))
      | (s, ZeroDotShift s') ->
          composeNth (s, 0, (subst_compose ((Shift (0, 1)), s')))
      | (s, TermDot (t, a, s')) ->
          TermDot ((subst_term s t), (subst_tp s a), (subst_compose (s, s')))
      | (s, EVarDot (ev, sl, s')) ->
          EVarDot (ev, (s :: sl), (subst_compose (s, s')))
      | (s, VarOptDot (no, s')) ->
          (match no with
           | None -> VarOptDot (None, (subst_compose (s, s')))
           | Some n -> composeNth (s, n, s'))(* ZeroDotShift (Shift (n-1,m)) = Shift(n,m) but the former is 'smaller' *)
    let rec shift t = shift_term 0 t
    let rec shift_nterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, Lam t) -> Lam (shift_term (n + 1) t)
      | (n, NRoot (h, sp)) -> NRoot (h, (shift_spine n sp))
    let rec shift_aterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, ARoot (Const n', sp)) -> ARoot ((Const n'), (shift_spine n sp))
      | (n, ERoot (ev, sl)) ->
          ERoot (ev, (subst_compose ((Shift (n, 1)), sl)))
      | (n, ARoot (Var n', sp)) ->
          let sp' = shift_spine n sp in
          if n' >= n
          then ARoot ((Var (n' + 1)), sp')
          else ARoot ((Var n'), sp')
    let rec shift_spinelt arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, Elt (ATerm t)) -> Elt (ATerm (shift_aterm n t))
      | (n, Elt (NTerm t)) -> Elt (NTerm (shift_nterm n t))
      | (n, AElt t) -> AElt (shift_aterm n t)
      | (n, Ascribe (t, a)) -> Ascribe ((shift_nterm n t), (shift_tp n a))
      | (n, Omit) -> Omit
    let rec shift_spine n = map (shift_spinelt n)
    let rec shift_tp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, TPi (m, a, b)) -> TPi (m, (shift_tp n a), (shift_tp (n + 1) b))
      | (n, TRoot (h, sp)) -> TRoot (h, (shift_spine n sp))
    let rec shift_term arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, NTerm t) -> NTerm (shift_nterm n t)
      | (n, ATerm t) -> ATerm (shift_aterm n t)
    let rec substs_comp sl = foldr subst_compose Id sl
    let rec elt_eroot_elim =
      function
      | AElt t -> eroot_elim_plus t
      | Elt (ATerm t) -> Elt (eroot_elim t)
      | x -> x
    let rec ntm_eroot_elim =
      function | Lam (ATerm t) -> Lam (eroot_elim t) | x -> x
    let rec ctxLookup (__g, n) =
      subst_tp (Shift (0, (n + 1))) (List.nth (__g, n))
    let rec typeOf (tclass a) = a
    let rec kindOf (kclass k) = k
    let sum = foldl (+) 0
    let rec size_term =
      function
      | NTerm (Lam t) -> 1 + (size_term t)
      | NTerm (NRoot (_, s)) -> (+) 1 size_spine s
      | ATerm (ARoot (_, s)) -> (+) 1 size_spine s
      | ATerm (ERoot _) -> 1
    let rec size_spine s = sum (map size_spinelt s)
    let rec size_spinelt =
      function
      | Elt t -> size_term t
      | AElt t -> size_term (ATerm t)
      | Ascribe (t, a) -> (+) (size_term (NTerm t)) size_tp a
      | Omit -> 0
    let rec size_tp =
      function
      | TRoot (_, s) -> (+) 1 size_spine s
      | TPi (_, a, b) -> (+) ((+) 1 size_tp a) size_tp b
    let rec size_knd =
      function
      | Type -> 1
      | KPi (_, a, b) -> (+) ((+) 1 size_tp a) size_knd b
    (* convert a kind to a context of all the pi-bound variables in it *)
    let rec explodeKind =
      function | Type -> [] | KPi (_, a, k) -> (explodeKind k) @ [a]
  end;;
