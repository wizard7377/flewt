
module type COMPRESS  =
  sig
    val sgnReset :
      unit ->
        ((unit)(*  type ConDec*)(* `Compressed' terms with omitted redundant arguments *))
    val sgnLookup : IntSyn.cid -> Sgn.sigent
    val sgnResetUpTo :
      int ->
        ((unit)(*    val sgnApp       : (IntSyn.cid -> unit) -> unit *))
    val sgnCompressUpTo : int -> unit
    val check : (Syntax.tp list * Syntax.term * Syntax.tp) -> bool
    val set_modes : (int * Syntax.mode list) -> unit
  end;;




module Compress(Compress:sig module Global : GLOBAL end) =
  struct
    module I = IntSyn
    module S = Syntax
    module Sgn = Sgn
    exception Unimp 
    exception NoModes 
    let ((debug)(* modes are not appropriate for the given I.ConDec *))
      = ref (-1)
    let rec sgnReset () = Sgn.clear ()
    let rec xlate_type =
      function
      | Pi
          ((Dec
            (((_)(* xlate_type : IntSyn.Exp -> Syntax.tp *)),
             e1),
            _),
           e2)
          -> S.TPi (S.MINUS, (xlate_type e1), (xlate_type e2))
      | Root (Const cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root (Def cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root
          (NSDef
           ((cid)(* assuming cids of consts and defs to be disjoint *)),
           sp)
          -> S.TRoot (cid, (xlate_spine sp))
      | Lam (((_)(* ditto *)), t) -> xlate_type t
    let rec xlate_spine =
      function
      | ((I.Nil)(* for type definitions, simply strip off the lambdas and leave
                                                   the variables free*))
          -> []
      | App (e, s) -> (::) (xlate_spinelt e) xlate_spine s
    let rec xlate_spinelt e = S.Elt (xlate_term e)
    let rec xlate_term =
      function
      | Root (Const cid, sp) ->
          S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root (Def cid, sp) ->
          S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root
          (NSDef
           ((cid)(* assuming cids of consts and defs to be disjoint *)),
           sp)
          -> S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root (BVar ((vid)(* ditto *)), sp) ->
          S.ATerm (S.ARoot ((S.Var (vid - 1)), (xlate_spine sp)))
      | Lam (_, e) -> S.NTerm (S.Lam (xlate_term e))
    let rec xlate_kind =
      function
      | Pi
          ((Dec
            (((_)(* xlate_kind : IntSyn.Exp -> Syntax.knd *)),
             e1),
            _),
           e2)
          -> S.KPi (S.MINUS, (xlate_type e1), (xlate_kind e2))
      | Uni (I.Type) -> S.Type
    open Syntax
    type simple_tp =
      | Base 
      | Arrow of
      (((simple_tp)(* simple skeletal form of types
     omits all dependencies, type constants *))
      * simple_tp) 
    let rec simplify_tp =
      function
      | TPi (_, t1, t2) -> Arrow ((simplify_tp t1), (simplify_tp t2))
      | TRoot _ -> Base
    let rec simplify_knd =
      function
      | KPi (_, t1, k2) -> Arrow ((simplify_tp t1), (simplify_knd k2))
      | Type -> Base
    let rec eta_expand_term arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (((g)(* hereditarily perform some eta-expansions on
     a (term, type, spine, etc.) in a context
    (and if not synthesizing) at a simple type.

    The only type of eta-expansion performed is when we
    encounter
    x . (M_1, M_2, ... M_n)
    for a variable x, and M_1, ..., M_n have fewer lambda abstractions
    than their (skeletal) type would suggest.

    The complication with doing full eta-expansion is that if
    we were to wrap lambda abstractions around terms that occur
    in a synthesizing position, we would need to add ascriptions,
    and thus carry full types around everywhere.

    Fortunately, this weakened form of eta-expansion is all
    we need to reconcile the discrepancy between what twelf
    maintains as an invariant, and full eta-longness. *)),
         NTerm t, T) -> NTerm (eta_expand_nterm g t T)
      | (g, ATerm t, T) -> ATerm (eta_expand_aterm g t)
    let rec eta_expand_nterm arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (g, Lam t, Arrow (t1, t2)) -> Lam (eta_expand_term (t1 :: g) t t2)
      | (g, NRoot (h, s), T) -> NRoot (h, (eta_expand_spine g s T))
      | (g, Lam t, Base) ->
          raise (Syntax "Lambda occurred where term of base type expected")
    let rec eta_expand_aterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, ARoot (Const n, s)) ->
          let stp = simplify_tp (typeOf (Sgn.o_classifier n)) in
          ARoot ((Const n), (eta_expand_spine g s stp))
      | (g, ARoot (Var n, s)) ->
          let stp = List.nth (g, n) in
          ARoot ((Var n), (eta_expand_var_spine g s stp))
      | (g, ERoot _) ->
          raise (Syntax "invariant violated in eta_expand_aterm")
    let rec eta_expand_tp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, TRoot (n, s)) ->
          let stp = simplify_knd (kindOf (Sgn.o_classifier n)) in
          TRoot (n, (eta_expand_spine g s stp))
      | (g, TPi (m, a, b)) ->
          TPi
            (m, (eta_expand_tp g a),
              (eta_expand_tp ((simplify_tp a) :: g) b))
    let rec eta_expand_knd arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, Type) -> Type
      | (g, KPi (m, a, b)) ->
          KPi
            (m, (eta_expand_tp g a),
              (eta_expand_knd ((simplify_tp a) :: g) b))
    let rec eta_expand_spine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (g, [], Base) -> []
      | (((g)(* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)),
         (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_term g m t1)) eta_expand_spine g tl t2
      | (g, (AElt m)::tl, Arrow (t1, t2)) ->
          (::) (AElt (eta_expand_aterm g m)) eta_expand_spine g tl t2
      | (g, (Ascribe (m, a))::tl, Arrow (t1, t2)) ->
          (::) (Ascribe ((eta_expand_nterm g m t1), (eta_expand_tp g a)))
            eta_expand_spine g tl t2
      | (g, (Omit)::tl, Arrow (t1, t2)) -> (::) Omit eta_expand_spine g tl t2
      | (_, _, _) ->
          raise (Syntax "Can't figure out how to eta expand spine")
    let rec eta_expand_var_spine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (((g)(* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *)),
         [], _) -> []
      | (((g)(* in fact this spine may not be eta-long yet *)),
         (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_immediate ((eta_expand_term g m t1), t1)))
            eta_expand_spine g tl t2
      | (_, _, _) ->
          raise
            (Syntax "Can't figure out how to eta expand var-headed spine")
    let rec eta_expand_immediate =
      function
      | (((m)(* here's where the actual expansion takes place *)),
         Base) -> m
      | (NTerm (Lam m), Arrow (t1, t2)) ->
          NTerm (Lam (eta_expand_immediate (m, t2)))
      | (m, Arrow (t1, t2)) ->
          let variable =
            eta_expand_immediate ((ATerm (ARoot ((Var 0), []))), t1) in
          NTerm
            (Lam
               (eta_expand_immediate ((apply_to ((shift m), variable)), t2)))
    let rec apply_to =
      function
      | (ATerm (ARoot (h, s)), m) -> ATerm (ARoot (h, (s @ [Elt m])))
      | (NTerm (NRoot (h, s)), m) -> NTerm (NRoot (h, (s @ [Elt m])))
      | _ -> raise (Syntax "Invariant violated in apply_to")
    let typeOf = S.typeOf
    let kindOf = S.kindOf
    exception Debug of (S.spine * S.tp * S.tp) 
    let rec compress_type
      ((g)(* val compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *)
      (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat SOME of empty list
    as if it were NONE. This doesn't seem right. *))
      s =
      compress_type' ((g)
        (* if !debug < 0
                          then *))
        s
    let rec compress_type' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((g)(* else  (if !debug = 0 then raise Debug(g, s) else ();
                                debug := !debug - 1; compress_type' g s) *)),
         (NONE, TPi (_, a, b))) ->
          S.TPi
            (S.MINUS, (compress_type g (NONE, a)),
              (compress_type (a :: g) (NONE, b)))
      | (g, (SOME (m::ms), TPi (_, a, b))) ->
          S.TPi
            (m, (compress_type g (NONE, a)),
              (compress_type (a :: g) ((SOME ms), b)))
      | (g, (SOME [], TRoot (cid, sp))) ->
          S.TRoot
            (cid,
              (compress_type_spine g
                 (sp, (kindOf (Sgn.o_classifier cid)),
                   (kindOf (Sgn.classifier cid)))))
      | (g, (NONE, (TRoot _ as a))) -> compress_type g ((SOME []), a)
      | (g, (SOME [], (TPi _ as a))) -> compress_type g (NONE, a)
    let rec compress_type_spine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((g)(* XXX sketchy *)(* XXX: optimization: don't compute mstar if omit? *)),
         ([], w, wstar)) -> []
      | (g, ((Elt m)::sp, KPi (_, a, v), KPi (mode, astar, vstar))) ->
          let mstar = compress_term g (m, a) in
          let sstar =
            compress_type_spine g
              (sp, (S.subst_knd (S.TermDot (m, a, S.Id)) v),
                (S.subst_knd (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type g (NONE, a)))) :: sstar)
    let rec compress_spine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, ([], w, wstar)) -> []
      | (g, ((Elt m)::sp, TPi (_, a, v), TPi (mode, astar, vstar))) ->
          let mstar = compress_term g (m, a) in
          let sstar =
            compress_spine g
              (sp, (S.subst_tp (S.TermDot (m, a, S.Id)) v),
                (S.subst_tp (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type g (NONE, a)))) :: sstar)
    let rec compress_term arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, (ATerm (ARoot (Var n, sp)), _)) ->
          let a = S.ctxLookup (g, n) in
          let astar = compress_type g (NONE, a) in
          S.ATerm (S.ARoot ((S.Var n), (compress_spine g (sp, a, astar))))
      | (g, (ATerm (ARoot (Const n, sp)), _)) ->
          let a = typeOf (Sgn.o_classifier n) in
          let astar = typeOf (Sgn.classifier n) in
          let term_former =
            match Sgn.get_p n with
            | SOME false__ -> S.NTerm o S.NRoot
            | _ -> S.ATerm o S.ARoot in
          term_former ((S.Const n), (compress_spine g (sp, a, astar)))
      | (g, (NTerm (Lam t), TPi (_, a, b))) ->
          S.NTerm (S.Lam (compress_term (a :: g) (t, b)))
    let rec compress_kind arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (g, (NONE, KPi (_, a, k))) ->
          S.KPi
            (S.MINUS, (compress_type g (NONE, a)),
              (compress_kind (a :: g) (NONE, k)))
      | (g, (SOME (m::ms), KPi (_, a, k))) ->
          S.KPi
            (m, (compress_type g (NONE, a)),
              (compress_kind (a :: g) ((SOME ms), k)))
      | (g, (SOME [], S.Type)) -> S.Type
      | (g, (NONE, S.Type)) -> S.Type
    let rec compress =
      function
      | (((cid)(* compress : cid * IntSyn.ConDec -> ConDec *)),
         ConDec (name, NONE, _, IntSyn.Normal, a, IntSyn.Type)) ->
          let x = xlate_type a in
          let x = eta_expand_tp [] x in
          let modes = Sgn.get_modes cid in
          Sgn.condec (name, (compress_type [] (modes, x)), x)
      | (cid, ConDec (name, NONE, _, IntSyn.Normal, k, IntSyn.Kind)) ->
          let x = xlate_kind k in
          let modes = Sgn.get_modes cid in
          Sgn.tycondec (name, (compress_kind [] (modes, x)), x)
      | (cid, ConDef (name, NONE, _, m, a, IntSyn.Type, _)) ->
          let m = xlate_term m in
          let a = xlate_type a in
          let astar = compress_type [] (NONE, a) in
          let mstar = compress_term [] (m, a) in
          Sgn.defn (name, astar, a, mstar, m)
      | (cid, ConDef (name, NONE, _, a, k, IntSyn.Kind, _)) ->
          let a = xlate_type a in
          let k = xlate_kind k in
          let kstar = compress_kind [] (NONE, k) in
          let astar = compress_type (Syntax.explodeKind kstar) (NONE, a) in
          Sgn.tydefn (name, kstar, k, astar, a)
      | (cid, AbbrevDef (name, NONE, _, m, a, IntSyn.Type)) ->
          let m = xlate_term m in
          let a = xlate_type a in
          let astar = compress_type [] (NONE, a) in
          let mstar = compress_term [] (m, a) in
          Sgn.abbrev (name, astar, a, mstar, m)
      | (cid, AbbrevDef (name, NONE, _, a, k, IntSyn.Kind)) ->
          let a = xlate_type a in
          let k = xlate_kind k in
          let kstar = compress_kind [] (NONE, k) in
          let astar = compress_type (Syntax.explodeKind kstar) (NONE, a) in
          Sgn.tyabbrev (name, kstar, k, astar, a)
      | _ -> raise Unimp
    let rec sgnLookup cid =
      let c = Sgn.sub cid in
      match c with
      | NONE ->
          let c' = compress (cid, (I.sgnLookup cid)) in
          let _ = Sgn.update (cid, c') in
          let _ = print ((Int.toString cid) ^ "\n") in c'
      | SOME x -> x
    let rec sgnCompressUpTo
      ((x)(*  val sgnApp  = IntSyn.sgnApp

  fun sgnCompress () = sgnApp (ignore o sgnLookup) *))
      = if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())
    let check = Reductio.check
    let rec extract f = try f (); raise Match with | Debug x -> x
    let set_modes = Sgn.set_modes
    let rec naiveModes
      ((cid)(* val log : Sgn.sigent list ref = ref [] *)
      (* given a cid, pick some vaguely plausible omission modes *))
      =
      let (ak, omitted_args, uni) =
        match I.sgnLookup cid with
        | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a, uni)
        | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a, uni)
        | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a, uni)
        | _ -> raise NoModes in
      let count_args =
        function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 in
      let total_args = count_args ak in
      let can_omit ms =
        let _ = Sgn.set_modes (cid, ms) in
        let s = compress (cid, (I.sgnLookup cid)) in
        let t = Sgn.typeOfSigent s in
        let ((isValid)(*                val _ = if true then log := !log @ [s] else () *))
          = Reductio.check_plusconst_strictness t in
        ((isValid)
          (*                val _ = if isValid then print "yup\n" else print "nope\n" *)) in
      let optimize' arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (ms, []) -> rev ms
        | (ms, (S.PLUS)::ms') ->
            if can_omit ((rev ms) @ (S.MINUS :: ms'))
            then optimize' (S.MINUS :: ms) ms'
            else optimize' (S.PLUS :: ms) ms'
        | (ms, (S.MINUS)::ms') ->
            if can_omit ((rev ms) @ (S.OMIT :: ms'))
            then optimize' (S.OMIT :: ms) ms'
            else optimize' (S.MINUS :: ms) ms' in
      let optimize ms = optimize' [] ms in
      if uni = I.Kind
      then List.tabulate (total_args, (function | _ -> S.MINUS))
      else
        optimize
          (List.tabulate
             (total_args,
               (function | x -> if x < omitted_args then S.MINUS else S.PLUS)))
    let rec idealModes
      ((cid)(* Given a cid, return the "ideal" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting signature will not typecheck. *))
      =
      let (ak, omitted_args) =
        match I.sgnLookup cid with
        | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a)
        | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a)
        | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a)
        | _ -> raise NoModes in
      let count_args =
        function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 in
      let total_args = count_args ak in
      List.tabulate
        (total_args,
          (function | x -> if x < omitted_args then S.OMIT else S.MINUS))
    let rec setModesUpTo
      ((x)(* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *))
      f =
      if x < 0
      then ()
      else (setModesUpTo (x - 1) f; Sgn.set_modes (x, (f x)); ())
    let rec sgnAutoCompress n f =
      try
        let modes = f n in
        Sgn.set_modes (n, modes);
        Sgn.update (n, (compress (n, (IntSyn.sgnLookup n))))
      with | NoModes -> ()
    let rec sgnAutoCompressUpTo' n0 n f =
      if n0 > n
      then ()
      else
        (let _ =
           match Sgn.sub n0 with
           | SOME _ -> ((())
               (* has this entry already been processed? *))
           | NONE ->
               (try
                  let modes = f n0 in
                  Sgn.set_modes (n0, modes);
                  Sgn.update (n0, (compress (n0, (IntSyn.sgnLookup n0))));
                  if (n0 mod__ 100) = 0
                  then print ((Int.toString n0) ^ "\n")
                  else ()
                with
                | NoModes -> ((())(* if not, compress it *))) in
         sgnAutoCompressUpTo' (n0 + 1) n f)
    let rec sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f
    let check = Reductio.check
  end;;
