
module type COMPRESS  =
  sig
    val sgnReset : unit -> unit
    val sgnLookup : IntSyn.cid -> Sgn.sigent
    val sgnResetUpTo : int -> unit
    val sgnCompressUpTo : int -> unit
    val check : Syntax.tp list -> Syntax.term -> Syntax.tp -> bool
    val set_modes : int -> Syntax.mode list -> unit
  end;;




module Compress(Compress:sig module Global : GLOBAL end) =
  struct
    module I = IntSyn
    module S = Syntax
    module Sgn = Sgn
    exception Unimp 
    exception NoModes 
    let debug = ref (-1)
    let rec sgnReset () = Sgn.clear ()
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
    let rec xlate_kind =
      function
      | Pi ((Dec (_, e1), _), e2) ->
          S.KPi (S.MINUS, (xlate_type e1), (xlate_kind e2))
      | Uni (I.Type) -> S.Type
    open Syntax
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
    let rec eta_expand_term __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (__G, NTerm t, __T) -> NTerm (eta_expand_nterm __G t __T)
      | (__G, ATerm t, __T) -> ATerm (eta_expand_aterm __G t)
    let rec eta_expand_nterm __3__ __4__ __5__ =
      match (__3__, __4__, __5__) with
      | (__G, Lam t, Arrow (t1, t2)) ->
          Lam (eta_expand_term (t1 :: __G) t t2)
      | (__G, NRoot (h, s), __T) -> NRoot (h, (eta_expand_spine __G s __T))
      | (__G, Lam t, Base) ->
          raise (Syntax "Lambda occurred where term of base type expected")
    let rec eta_expand_aterm __6__ __7__ =
      match (__6__, __7__) with
      | (__G, ARoot (Const n, s)) ->
          let stp = simplify_tp (typeOf (Sgn.o_classifier n)) in
          ARoot ((Const n), (eta_expand_spine __G s stp))
      | (__G, ARoot (Var n, s)) ->
          let stp = List.nth (__G, n) in
          ARoot ((Var n), (eta_expand_var_spine __G s stp))
      | (__G, ERoot _) ->
          raise (Syntax "invariant violated in eta_expand_aterm")
    let rec eta_expand_tp __8__ __9__ =
      match (__8__, __9__) with
      | (__G, TRoot (n, s)) ->
          let stp = simplify_knd (kindOf (Sgn.o_classifier n)) in
          TRoot (n, (eta_expand_spine __G s stp))
      | (__G, TPi (m, a, b)) ->
          TPi
            (m, (eta_expand_tp __G a),
              (eta_expand_tp ((simplify_tp a) :: __G) b))
    let rec eta_expand_knd __10__ __11__ =
      match (__10__, __11__) with
      | (__G, Type) -> Type
      | (__G, KPi (m, a, b)) ->
          KPi
            (m, (eta_expand_tp __G a),
              (eta_expand_knd ((simplify_tp a) :: __G) b))
    let rec eta_expand_spine __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (__G, [], Base) -> []
      | (__G, (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_term __G m t1)) eta_expand_spine __G tl t2
      | (__G, (AElt m)::tl, Arrow (t1, t2)) ->
          (::) (AElt (eta_expand_aterm __G m)) eta_expand_spine __G tl t2
      | (__G, (Ascribe (m, a))::tl, Arrow (t1, t2)) ->
          (::) (Ascribe ((eta_expand_nterm __G m t1), (eta_expand_tp __G a)))
            eta_expand_spine __G tl t2
      | (__G, (Omit)::tl, Arrow (t1, t2)) ->
          (::) Omit eta_expand_spine __G tl t2
      | (_, _, _) ->
          raise (Syntax "Can't figure out how to eta expand spine")(* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
    let rec eta_expand_var_spine __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (__G, [], _) -> []
      | (__G, (Elt m)::tl, Arrow (t1, t2)) ->
          (::) (Elt (eta_expand_immediate ((eta_expand_term __G m t1), t1)))
            eta_expand_spine __G tl t2
      | (_, _, _) ->
          raise
            (Syntax "Can't figure out how to eta expand var-headed spine")
      (* in fact this spine may not be eta-long yet *)
    let rec eta_expand_immediate __18__ __19__ =
      match (__18__, __19__) with
      | (m, Base) -> m
      | (NTerm (Lam m), Arrow (t1, t2)) ->
          NTerm (Lam (eta_expand_immediate (m, t2)))
      | (m, Arrow (t1, t2)) ->
          let variable =
            eta_expand_immediate ((ATerm (ARoot ((Var 0), []))), t1) in
          NTerm
            (Lam
               (eta_expand_immediate ((apply_to ((shift m), variable)), t2)))
    let rec apply_to __20__ __21__ =
      match (__20__, __21__) with
      | (ATerm (ARoot (h, s)), m) -> ATerm (ARoot (h, (s @ [Elt m])))
      | (NTerm (NRoot (h, s)), m) -> NTerm (NRoot (h, (s @ [Elt m])))
      | _ -> raise (Syntax "Invariant violated in apply_to")
    let typeOf = S.typeOf
    let kindOf = S.kindOf
    exception Debug of (S.spine * S.tp * S.tp) 
    let rec compress_type (__G) s = compress_type' __G s(* if !debug < 0
                          then *)
    let rec compress_type' __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | (__G, None, TPi (_, a, b)) ->
          S.TPi
            (S.MINUS, (compress_type __G (None, a)),
              (compress_type (a :: __G) (None, b)))
      | (__G, Some (m::ms), TPi (_, a, b)) ->
          S.TPi
            (m, (compress_type __G (None, a)),
              (compress_type (a :: __G) ((Some ms), b)))
      | (__G, Some [], TRoot (cid, sp)) ->
          S.TRoot
            (cid,
              (compress_type_spine __G
                 (sp, (kindOf (Sgn.o_classifier cid)),
                   (kindOf (Sgn.classifier cid)))))
      | (__G, None, (TRoot _ as a)) -> compress_type __G ((Some []), a)
      | (__G, Some [], (TPi _ as a)) -> compress_type __G (None, a)
    let rec compress_type_spine __25__ __26__ __27__ __28__ =
      match (__25__, __26__, __27__, __28__) with
      | (__G, [], w, wstar) -> []
      | (__G, (Elt m)::sp, KPi (_, a, v), KPi (mode, astar, vstar)) ->
          let mstar = compress_term __G (m, a) in
          let sstar =
            compress_type_spine __G
              (sp, (S.subst_knd (S.TermDot (m, a, S.Id)) v),
                (S.subst_knd (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type __G (None, a)))) :: sstar)
    let rec compress_spine __29__ __30__ __31__ __32__ =
      match (__29__, __30__, __31__, __32__) with
      | (__G, [], w, wstar) -> []
      | (__G, (Elt m)::sp, TPi (_, a, v), TPi (mode, astar, vstar)) ->
          let mstar = compress_term __G (m, a) in
          let sstar =
            compress_spine __G
              (sp, (S.subst_tp (S.TermDot (m, a, S.Id)) v),
                (S.subst_tp (S.TermDot (mstar, astar, S.Id)) vstar)) in
          (match (mode, mstar) with
           | (S.OMIT, _) -> S.Omit :: sstar
           | (S.MINUS, _) -> (S.Elt mstar) :: sstar
           | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
           | (S.PLUS, NTerm t) ->
               (S.Ascribe (t, (compress_type __G (None, a)))) :: sstar)
    let rec compress_term __33__ __34__ __35__ =
      match (__33__, __34__, __35__) with
      | (__G, ATerm (ARoot (Var n, sp)), _) ->
          let a = S.ctxLookup (__G, n) in
          let astar = compress_type __G (None, a) in
          S.ATerm (S.ARoot ((S.Var n), (compress_spine __G (sp, a, astar))))
      | (__G, ATerm (ARoot (Const n, sp)), _) ->
          let a = typeOf (Sgn.o_classifier n) in
          let astar = typeOf (Sgn.classifier n) in
          let term_former =
            match Sgn.get_p n with
            | Some false -> S.NTerm o S.NRoot
            | _ -> S.ATerm o S.ARoot in
          term_former ((S.Const n), (compress_spine __G (sp, a, astar)))
      | (__G, NTerm (Lam t), TPi (_, a, b)) ->
          S.NTerm (S.Lam (compress_term (a :: __G) (t, b)))
    let rec compress_kind __36__ __37__ __38__ =
      match (__36__, __37__, __38__) with
      | (__G, None, KPi (_, a, k)) ->
          S.KPi
            (S.MINUS, (compress_type __G (None, a)),
              (compress_kind (a :: __G) (None, k)))
      | (__G, Some (m::ms), KPi (_, a, k)) ->
          S.KPi
            (m, (compress_type __G (None, a)),
              (compress_kind (a :: __G) ((Some ms), k)))
      | (__G, Some [], S.Type) -> S.Type
      | (__G, None, S.Type) -> S.Type
    let rec compress __39__ __40__ =
      match (__39__, __40__) with
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
    let rec sgnCompressUpTo x =
      if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())
    let check = Reductio.check
    let rec extract f = try f (); raise Match with | Debug x -> x
    let set_modes = Sgn.set_modes
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
      let rec optimize' __41__ __42__ =
        match (__41__, __42__) with
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
      then List.tabulate (total_args, (fun _ -> S.MINUS))
      else
        optimize
          (List.tabulate
             (total_args,
               (fun x -> if x < omitted_args then S.MINUS else S.PLUS)))
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
        (total_args, (fun x -> if x < omitted_args then S.OMIT else S.MINUS))
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
