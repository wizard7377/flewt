
(* `Compressed' terms with omitted redundant arguments *)
module type COMPRESS  =
  sig
    (*  type ConDec*)
    val sgnReset : unit -> unit
    val sgnLookup : IntSyn.cid -> Sgn.sigent
    (*    val sgnApp       : (IntSyn.cid -> unit) -> unit *)
    val sgnResetUpTo : int -> unit
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
    (* modes are not appropriate for the given I.ConDec *)
    let debug = ref (-1)
    let rec sgnReset () = Sgn.clear ()
    (* xlate_type : IntSyn.Exp -> Syntax.tp *)
    let rec xlate_type =
      function
      | Pi ((Dec (_, e1), _), e2) ->
          S.TPi (S.MINUS, (xlate_type e1), (xlate_type e2))
      | Root (Const cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root (Def cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root (NSDef cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Lam (_, t) -> xlate_type t(* ditto *)(* assuming cids of consts and defs to be disjoint *)
    let rec xlate_spine =
      function
      | I.Nil -> []
      | App (e, s) -> (::) (xlate_spinelt e) xlate_spine s
    let rec xlate_spinelt e = S.Elt (xlate_term e)
    let rec xlate_term =
      function
      | Root (Const cid, sp) ->
          S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root (Def cid, sp) ->
          S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root (NSDef cid, sp) ->
          S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
      | Root (BVar vid, sp) ->
          S.ATerm (S.ARoot ((S.Var (vid - 1)), (xlate_spine sp)))
      | Lam (_, e) -> S.NTerm (S.Lam (xlate_term e))(* ditto *)(* assuming cids of consts and defs to be disjoint *)
    (* xlate_kind : IntSyn.Exp -> Syntax.knd *)
    let rec xlate_kind =
      function
      | Pi ((Dec (_, e1), _), e2) ->
          S.KPi (S.MINUS, (xlate_type e1), (xlate_kind e2))
      | Uni (I.Type) -> S.Type
    open Syntax
    (* simple skeletal form of types
     omits all dependencies, type constants *)
    type simple_tp =
      | Base 
      | Arrow of (simple_tp * simple_tp) 
    let rec simplify_tp =
      function
      | TPi (_, t1, t2) -> Arrow ((simplify_tp t1), (simplify_tp t2))
      | TRoot _ -> Base
    let rec simplify_knd =
      function
      | KPi (_, t1, k2) -> Arrow ((simplify_tp t1), (simplify_knd k2))
      | Type -> Base
    (* hereditarily perform some eta-expansions on
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
    maintains as an invariant, and full eta-longness. *)
    let rec eta_expand_term arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (__g, NTerm t, T) -> NTerm (eta_expand_nterm __g t T)
      | (__g, ATerm t, T) -> ATerm (eta_expand_aterm __g t)
    let rec eta_expand_nterm arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (__g, Lam t, Arrow (t1, t2)) -> Lam (eta_expand_term (t1 :: __g) t t2)
      | (__g, NRoot (h, s), T) -> NRoot (h, (eta_expand_spine __g s T))
      | (__g, Lam t, Base) ->
          raise (Syntax "Lambda occurred where term of base type expected")
    let rec eta_expand_aterm arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, ARoot (Const n, s)) ->
          let stp = simplify_tp (typeOf (Sgn.o_classifier n)) in
          ARoot ((Const n), (eta_expand_spine __g s stp))
      | (__g, ARoot (Var n, s)) ->
          let stp = List.nth (__g, n) in
          ARoot ((Var n), (eta_expand_var_spine __g s stp))
      | (__g, ERoot _) ->
          raise (Syntax "invariant violated in eta_expand_aterm")
    let rec eta_expand_tp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, TRoot (n, s)) ->
          let stp = simplify_knd (kindOf (Sgn.o_classifier n)) in
          TRoot (n, (eta_expand_spine __g s stp))
      | (__g, TPi (m, a, b)) ->
          TPi
            (m, (eta_expand_tp __g a),
              (eta_expand_tp ((simplify_tp a) :: __g) b))
    let rec eta_expand_knd arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, Type) -> Type
      | (__g, KPi (m, a, b)) ->
          KPi
            (m, (eta_expand_tp __g a),
              (eta_expand_knd ((simplify_tp a) :: __g) b))
    let rec eta_expand_spine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (__g, [], Base) -> []
      | (__g, (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_term __g m t1)) eta_expand_spine __g tl t2
      | (__g, (AElt m)::tl, Arrow (t1, t2)) ->
          (::) (AElt (eta_expand_aterm __g m)) eta_expand_spine __g tl t2
      | (__g, (Ascribe (m, a))::tl, Arrow (t1, t2)) ->
          (::) (Ascribe ((eta_expand_nterm __g m t1), (eta_expand_tp __g a)))
            eta_expand_spine __g tl t2
      | (__g, (Omit)::tl, Arrow (t1, t2)) -> (::) Omit eta_expand_spine __g tl t2
      | (_, _, _) ->
          raise (Syntax "Can't figure out how to eta expand spine")(* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
    let rec eta_expand_var_spine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (__g, [], _) -> []
      | (__g, (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_immediate ((eta_expand_term __g m t1), t1)))
            eta_expand_spine __g tl t2
      | (_, _, _) ->
          raise
            (Syntax "Can't figure out how to eta expand var-headed spine")
      (* in fact this spine may not be eta-long yet *)
    let rec eta_expand_immediate =
      function
      | (m, Base) -> m
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
    (* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *)
    (* here's where the actual expansion takes place *)
    let typeOf = S.typeOf
    let kindOf = S.kindOf
    exception Debug of (S.spine * S.tp * S.tp) 
    (* val compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *)
    (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat Some of empty list
    as if it were NONE. This doesn't seem right. *)
    let rec compress_type (__g) s = compress_type' __g s(* if !debug < 0
                          then *)
    let rec compress_type' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, (None, TPi (_, a, b))) ->
          S.TPi
            (S.MINUS, (compress_type __g (None, a)),
              (compress_type (a :: __g) (None, b)))
      | (__g, (Some (m::ms), TPi (_, a, b))) ->
          S.TPi
            (m, (compress_type __g (None, a)),
              (compress_type (a :: __g) ((Some ms), b)))
      | (__g, (Some [], TRoot (cid, sp))) ->
          S.TRoot
            (cid,
              (compress_type_spine __g
                 (sp, (kindOf (Sgn.o_classifier cid)),
                   (kindOf (Sgn.classifier cid)))))
      | (__g, (None, (TRoot _ as a))) -> compress_type __g ((Some []), a)
      | (__g, (Some [], (TPi _ as a))) -> compress_type __g (None, a)
    let rec compress_type_spine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, ([], w, wstar)) -> []
      | (__g, ((Elt m)::sp, KPi (_, a, v), KPi (mode, astar, vstar))) ->
          let mstar = compress_term __g (m, a) in
          let sstar =
            compress_type_spine __g
              (sp, (S.subst_knd (S.TermDot (m, a, S.Id)) v),
                (S.subst_knd (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type __g (None, a)))) :: sstar)
    let rec compress_spine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, ([], w, wstar)) -> []
      | (__g, ((Elt m)::sp, TPi (_, a, v), TPi (mode, astar, vstar))) ->
          let mstar = compress_term __g (m, a) in
          let sstar =
            compress_spine __g
              (sp, (S.subst_tp (S.TermDot (m, a, S.Id)) v),
                (S.subst_tp (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type __g (None, a)))) :: sstar)
    let rec compress_term arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, (ATerm (ARoot (Var n, sp)), _)) ->
          let a = S.ctxLookup (__g, n) in
          let astar = compress_type __g (None, a) in
          S.ATerm (S.ARoot ((S.Var n), (compress_spine __g (sp, a, astar))))
      | (__g, (ATerm (ARoot (Const n, sp)), _)) ->
          let a = typeOf (Sgn.o_classifier n) in
          let astar = typeOf (Sgn.classifier n) in
          let term_former =
            match Sgn.get_p n with
            | Some false__ -> S.NTerm o S.NRoot
            | _ -> S.ATerm o S.ARoot in
          term_former ((S.Const n), (compress_spine __g (sp, a, astar)))
      | (__g, (NTerm (Lam t), TPi (_, a, b))) ->
          S.NTerm (S.Lam (compress_term (a :: __g) (t, b)))
    let rec compress_kind arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, (None, KPi (_, a, k))) ->
          S.KPi
            (S.MINUS, (compress_type __g (None, a)),
              (compress_kind (a :: __g) (None, k)))
      | (__g, (Some (m::ms), KPi (_, a, k))) ->
          S.KPi
            (m, (compress_type __g (None, a)),
              (compress_kind (a :: __g) ((Some ms), k)))
      | (__g, (Some [], S.Type)) -> S.Type
      | (__g, (None, S.Type)) -> S.Type
    (* compress : cid * IntSyn.ConDec -> ConDec *)
    let rec compress =
      function
      | (cid, ConDec (name, None, _, IntSyn.Normal, a, IntSyn.Type)) ->
          let x = xlate_type a in
          let x = eta_expand_tp [] x in
          let modes = Sgn.get_modes cid in
          Sgn.condec (name, (compress_type [] (modes, x)), x)
      | (cid, ConDec (name, None, _, IntSyn.Normal, k, IntSyn.Kind)) ->
          let x = xlate_kind k in
          let modes = Sgn.get_modes cid in
          Sgn.tycondec (name, (compress_kind [] (modes, x)), x)
      | (cid, ConDef (name, None, _, m, a, IntSyn.Type, _)) ->
          let m = xlate_term m in
          let a = xlate_type a in
          let astar = compress_type [] (None, a) in
          let mstar = compress_term [] (m, a) in
          Sgn.defn (name, astar, a, mstar, m)
      | (cid, ConDef (name, None, _, a, k, IntSyn.Kind, _)) ->
          let a = xlate_type a in
          let k = xlate_kind k in
          let kstar = compress_kind [] (None, k) in
          let astar = compress_type (Syntax.explodeKind kstar) (None, a) in
          Sgn.tydefn (name, kstar, k, astar, a)
      | (cid, AbbrevDef (name, None, _, m, a, IntSyn.Type)) ->
          let m = xlate_term m in
          let a = xlate_type a in
          let astar = compress_type [] (None, a) in
          let mstar = compress_term [] (m, a) in
          Sgn.abbrev (name, astar, a, mstar, m)
      | (cid, AbbrevDef (name, None, _, a, k, IntSyn.Kind)) ->
          let a = xlate_type a in
          let k = xlate_kind k in
          let kstar = compress_kind [] (None, k) in
          let astar = compress_type (Syntax.explodeKind kstar) (None, a) in
          Sgn.tyabbrev (name, kstar, k, astar, a)
      | _ -> raise Unimp
    let rec sgnLookup cid =
      let c = Sgn.sub cid in
      match c with
      | None ->
          let c' = compress (cid, (I.sgnLookup cid)) in
          let _ = Sgn.update (cid, c') in
          let _ = print ((Int.toString cid) ^ "\n") in c'
      | Some x -> x
    (*  val sgnApp  = IntSyn.sgnApp

  fun sgnCompress () = sgnApp (ignore o sgnLookup) *)
    let rec sgnCompressUpTo x =
      if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())
    let check = Reductio.check
    let rec extract f = try f (); raise Match with | Debug x -> x
    let set_modes = Sgn.set_modes
    (* val log : Sgn.sigent list ref = ref [] *)
    (* given a cid, pick some vaguely plausible omission modes *)
    let rec naiveModes cid =
      let (ak, omitted_args, uni) =
        match I.sgnLookup cid with
        | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a, uni)
        | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a, uni)
        | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a, uni)
        | _ -> raise NoModes in
      let rec count_args =
        function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 in
      let total_args = count_args ak in
      let rec can_omit ms =
        let _ = Sgn.set_modes (cid, ms) in
        let s = compress (cid, (I.sgnLookup cid)) in
        let t = Sgn.typeOfSigent s in
        let isValid = Reductio.check_plusconst_strictness t in ((isValid)
          (*                val _ = if true then log := !log @ [s] else () *)
          (*                val _ = if isValid then print "yup\n" else print "nope\n" *)) in
      let rec optimize' arg__0 arg__1 =
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
      let rec optimize ms = optimize' [] ms in
      if uni = I.Kind
      then List.tabulate (total_args, (function | _ -> S.MINUS))
      else
        optimize
          (List.tabulate
             (total_args,
               (function | x -> if x < omitted_args then S.MINUS else S.PLUS)))
    (* Given a cid, return the "ideal" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting signature will not typecheck. *)
    let rec idealModes cid =
      let (ak, omitted_args) =
        match I.sgnLookup cid with
        | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a)
        | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a)
        | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a)
        | _ -> raise NoModes in
      let rec count_args =
        function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 in
      let total_args = count_args ak in
      List.tabulate
        (total_args,
          (function | x -> if x < omitted_args then S.OMIT else S.MINUS))
    (* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *)
    let rec setModesUpTo x f =
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
           ((match Sgn.sub n0 with
             | Some _ -> ()
             | None ->
                 (try
                    let modes = f n0 in
                    Sgn.set_modes (n0, modes);
                    Sgn.update (n0, (compress (n0, (IntSyn.sgnLookup n0))));
                    if (n0 mod__ 100) = 0
                    then print ((Int.toString n0) ^ "\n")
                    else ()
                  with | NoModes -> ()))
           (* if not, compress it *)) in
         ((sgnAutoCompressUpTo' (n0 + 1) n f)
           (* has this entry already been processed? *)))
    let rec sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f
    let check = Reductio.check
  end;;
