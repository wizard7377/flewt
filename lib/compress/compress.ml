module type COMPRESS  =
  sig
    val sgnReset : unit -> unit
    val sgnLookup : IntSyn.cid -> Sgn.sigent
    val sgnResetUpTo : int -> unit
    val sgnCompressUpTo : int -> unit
    val check : (Syntax.tp list * Syntax.term * Syntax.tp) -> bool
    val set_modes : (int * Syntax.mode list) -> unit
  end


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
      begin function
      | Pi ((Dec (_, e1), _), e2) ->
          S.TPi (S.MINUS, (xlate_type e1), (xlate_type e2))
      | Root (Const cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root (Def cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Root (NSDef cid, sp) -> S.TRoot (cid, (xlate_spine sp))
      | Lam (_, t) -> xlate_type t end(* ditto *)(* assuming cids of consts and defs to be disjoint *)
    let rec xlate_spine =
      begin function
      | I.Nil -> []
      | App (e, s) -> (::) (xlate_spinelt e) xlate_spine s end
  let rec xlate_spinelt e = S.Elt (xlate_term e)
  let rec xlate_term =
    begin function
    | Root (Const cid, sp) ->
        S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
    | Root (Def cid, sp) ->
        S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
    | Root (NSDef cid, sp) ->
        S.ATerm (S.ARoot ((S.Const cid), (xlate_spine sp)))
    | Root (BVar vid, sp) ->
        S.ATerm (S.ARoot ((S.Var (vid - 1)), (xlate_spine sp)))
    | Lam (_, e) -> S.NTerm (S.Lam (xlate_term e)) end(* ditto *)
  (* assuming cids of consts and defs to be disjoint *)
let rec xlate_kind =
  begin function
  | Pi ((Dec (_, e1), _), e2) ->
      S.KPi (S.MINUS, (xlate_type e1), (xlate_kind e2))
  | Uni (I.Type) -> S.Type end
open Syntax
type simple_tp =
  | Base 
  | Arrow of (simple_tp * simple_tp) 
let rec simplify_tp =
  begin function
  | TPi (_, t1, t2) -> Arrow ((simplify_tp t1), (simplify_tp t2))
  | TRoot _ -> Base end
let rec simplify_knd =
  begin function
  | KPi (_, t1, k2) -> Arrow ((simplify_tp t1), (simplify_knd k2))
  | Type -> Base end
let rec eta_expand_term arg__0 arg__1 arg__2 =
  begin match (arg__0, arg__1, arg__2) with
  | (g_, NTerm t, t_) -> NTerm (eta_expand_nterm g_ t t_)
  | (g_, ATerm t, t_) -> ATerm (eta_expand_aterm g_ t) end
let rec eta_expand_nterm arg__3 arg__4 arg__5 =
  begin match (arg__3, arg__4, arg__5) with
  | (g_, Lam t, Arrow (t1, t2)) -> Lam (eta_expand_term (t1 :: g_) t t2)
  | (g_, NRoot (h, s), t_) -> NRoot (h, (eta_expand_spine g_ s t_))
  | (g_, Lam t, Base) ->
      raise (Syntax "Lambda occurred where term of base type expected") end
let rec eta_expand_aterm arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (g_, ARoot (Const n, s)) ->
      let stp = simplify_tp (typeOf (Sgn.o_classifier n)) in
      ARoot ((Const n), (eta_expand_spine g_ s stp))
  | (g_, ARoot (Var n, s)) ->
      let stp = List.nth (g_, n) in
      ARoot ((Var n), (eta_expand_var_spine g_ s stp))
  | (g_, ERoot _) -> raise (Syntax "invariant violated in eta_expand_aterm") end
let rec eta_expand_tp arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (g_, TRoot (n, s)) ->
      let stp = simplify_knd (kindOf (Sgn.o_classifier n)) in
      TRoot (n, (eta_expand_spine g_ s stp))
  | (g_, TPi (m, a, b)) ->
      TPi
        (m, (eta_expand_tp g_ a), (eta_expand_tp ((simplify_tp a) :: g_) b)) end
let rec eta_expand_knd arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (g_, Type) -> Type
  | (g_, KPi (m, a, b)) ->
      KPi
        (m, (eta_expand_tp g_ a), (eta_expand_knd ((simplify_tp a) :: g_) b)) end
let rec eta_expand_spine arg__12 arg__13 arg__14 =
  begin match (arg__12, arg__13, arg__14) with
  | (g_, [], Base) -> []
  | (g_, (Elt m)::tl, Arrow (t1, t2)) ->
      (::) (Elt (eta_expand_term g_ m t1)) eta_expand_spine g_ tl t2
  | (g_, (AElt m)::tl, Arrow (t1, t2)) ->
      (::) (AElt (eta_expand_aterm g_ m)) eta_expand_spine g_ tl t2
  | (g_, (Ascribe (m, a))::tl, Arrow (t1, t2)) ->
      (::) (Ascribe ((eta_expand_nterm g_ m t1), (eta_expand_tp g_ a)))
        eta_expand_spine g_ tl t2
  | (g_, (Omit)::tl, Arrow (t1, t2)) -> (::) Omit eta_expand_spine g_ tl t2
  | (_, _, _) -> raise (Syntax "Can't figure out how to eta expand spine") end
(* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
let rec eta_expand_var_spine arg__15 arg__16 arg__17 =
  begin match (arg__15, arg__16, arg__17) with
  | (g_, [], _) -> []
  | (g_, (Elt m)::tl, Arrow (t1, t2)) ->
      (::) (Elt (eta_expand_immediate ((eta_expand_term g_ m t1), t1)))
        eta_expand_spine g_ tl t2
  | (_, _, _) ->
      raise (Syntax "Can't figure out how to eta expand var-headed spine") end
(* in fact this spine may not be eta-long yet *)
let rec eta_expand_immediate =
  begin function
  | (m, Base) -> m
  | (NTerm (Lam m), Arrow (t1, t2)) ->
      NTerm (Lam (eta_expand_immediate (m, t2)))
  | (m, Arrow (t1, t2)) ->
      let variable = eta_expand_immediate ((ATerm (ARoot ((Var 0), []))), t1) in
      NTerm
        (Lam (eta_expand_immediate ((apply_to ((shift m), variable)), t2))) end
let rec apply_to =
  begin function
  | (ATerm (ARoot (h, s)), m) -> ATerm (ARoot (h, (s @ [Elt m])))
  | (NTerm (NRoot (h, s)), m) -> NTerm (NRoot (h, (s @ [Elt m])))
  | _ -> raise (Syntax "Invariant violated in apply_to") end
let typeOf = S.typeOf
let kindOf = S.kindOf
exception Debug of (S.spine * S.tp * S.tp) 
let rec compress_type (g_) s = compress_type' g_ s(* if !debug < 0
                          then *)
let rec compress_type' arg__18 arg__19 =
  begin match (arg__18, arg__19) with
  | (g_, (None, TPi (_, a, b))) ->
      S.TPi
        (S.MINUS, (compress_type g_ (None, a)),
          (compress_type (a :: g_) (None, b)))
  | (g_, (Some (m::ms), TPi (_, a, b))) ->
      S.TPi
        (m, (compress_type g_ (None, a)),
          (compress_type (a :: g_) ((Some ms), b)))
  | (g_, (Some [], TRoot (cid, sp))) ->
      S.TRoot
        (cid,
          (compress_type_spine g_
             (sp, (kindOf (Sgn.o_classifier cid)),
               (kindOf (Sgn.classifier cid)))))
  | (g_, (None, (TRoot _ as a))) -> compress_type g_ ((Some []), a)
  | (g_, (Some [], (TPi _ as a))) -> compress_type g_ (None, a) end
let rec compress_type_spine arg__20 arg__21 =
  begin match (arg__20, arg__21) with
  | (g_, ([], w, wstar)) -> []
  | (g_, ((Elt m)::sp, KPi (_, a, v), KPi (mode, astar, vstar))) ->
      let mstar = compress_term g_ (m, a) in
      let sstar =
        compress_type_spine g_
          (sp, (S.subst_knd (S.TermDot (m, a, S.Id)) v),
            (S.subst_knd (S.TermDot (mstar, astar, S.Id)) vstar)) in
      (begin match (mode, mstar) with
       | (S.OMIT, _) -> S.Omit :: sstar
       | (S.MINUS, _) -> (S.Elt mstar) :: sstar
       | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
       | (S.PLUS, NTerm t) ->
           (S.Ascribe (t, (compress_type g_ (None, a)))) :: sstar end) end
let rec compress_spine arg__22 arg__23 =
  begin match (arg__22, arg__23) with
  | (g_, ([], w, wstar)) -> []
  | (g_, ((Elt m)::sp, TPi (_, a, v), TPi (mode, astar, vstar))) ->
      let mstar = compress_term g_ (m, a) in
      let sstar =
        compress_spine g_
          (sp, (S.subst_tp (S.TermDot (m, a, S.Id)) v),
            (S.subst_tp (S.TermDot (mstar, astar, S.Id)) vstar)) in
      (begin match (mode, mstar) with
       | (S.OMIT, _) -> S.Omit :: sstar
       | (S.MINUS, _) -> (S.Elt mstar) :: sstar
       | (S.PLUS, ATerm t) -> (S.AElt t) :: sstar
       | (S.PLUS, NTerm t) ->
           (S.Ascribe (t, (compress_type g_ (None, a)))) :: sstar end) end
let rec compress_term arg__24 arg__25 =
  begin match (arg__24, arg__25) with
  | (g_, (ATerm (ARoot (Var n, sp)), _)) ->
      let a = S.ctxLookup (g_, n) in
      let astar = compress_type g_ (None, a) in
      S.ATerm (S.ARoot ((S.Var n), (compress_spine g_ (sp, a, astar))))
  | (g_, (ATerm (ARoot (Const n, sp)), _)) ->
      let a = typeOf (Sgn.o_classifier n) in
      let astar = typeOf (Sgn.classifier n) in
      let term_former =
        begin match Sgn.get_p n with
        | Some false -> S.NTerm o S.NRoot
        | _ -> S.ATerm o S.ARoot end in
      term_former ((S.Const n), (compress_spine g_ (sp, a, astar)))
  | (g_, (NTerm (Lam t), TPi (_, a, b))) ->
      S.NTerm (S.Lam (compress_term (a :: g_) (t, b))) end
let rec compress_kind arg__26 arg__27 =
  begin match (arg__26, arg__27) with
  | (g_, (None, KPi (_, a, k))) ->
      S.KPi
        (S.MINUS, (compress_type g_ (None, a)),
          (compress_kind (a :: g_) (None, k)))
  | (g_, (Some (m::ms), KPi (_, a, k))) ->
      S.KPi
        (m, (compress_type g_ (None, a)),
          (compress_kind (a :: g_) ((Some ms), k)))
  | (g_, (Some [], S.Type)) -> S.Type
  | (g_, (None, S.Type)) -> S.Type end
let rec compress =
  begin function
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
  | _ -> raise Unimp end
let rec sgnLookup cid =
  let c = Sgn.sub cid in
  begin match c with
  | None ->
      let c' = compress (cid, (I.sgnLookup cid)) in
      let _ = Sgn.update (cid, c') in
      let _ = print ((Int.toString cid) ^ "\n") in c'
  | Some x -> x end
let rec sgnCompressUpTo x = if x < 0 then begin () end
  else begin (begin sgnCompressUpTo (x - 1); sgnLookup x; () end) end
let check = Reductio.check
let rec extract f = begin try begin f (); raise Match end with | Debug x -> x end
let set_modes = Sgn.set_modes
let rec naiveModes cid =
  let (ak, omitted_args, uni) =
    begin match I.sgnLookup cid with
    | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a, uni)
    | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a, uni)
    | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a, uni)
    | _ -> raise NoModes end in
let rec count_args =
  begin function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 end in
let total_args = count_args ak in
let rec can_omit ms =
  let _ = Sgn.set_modes (cid, ms) in
  let s = compress (cid, (I.sgnLookup cid)) in
  let t = Sgn.typeOfSigent s in
  let isValid = Reductio.check_plusconst_strictness t in ((isValid)
    (*                val _ = if true then log := !log @ [s] else () *)
    (*                val _ = if isValid then print "yup\n" else print "nope\n" *)) in
let rec optimize' arg__28 arg__29 =
  begin match (arg__28, arg__29) with
  | (ms, []) -> rev ms
  | (ms, (S.PLUS)::ms') ->
      if can_omit ((rev ms) @ (S.MINUS :: ms'))
      then begin optimize' (S.MINUS :: ms) ms' end
      else begin optimize' (S.PLUS :: ms) ms' end
  | (ms, (S.MINUS)::ms') ->
      if can_omit ((rev ms) @ (S.OMIT :: ms'))
      then begin optimize' (S.OMIT :: ms) ms' end
      else begin optimize' (S.MINUS :: ms) ms' end end in
let rec optimize ms = optimize' [] ms in
if uni = I.Kind
then begin List.tabulate (total_args, (begin function | _ -> S.MINUS end)) end
else begin
  optimize
    (List.tabulate
       (total_args,
         (begin function
          | x -> if x < omitted_args then begin S.MINUS end
              else begin S.PLUS end end))) end
let rec idealModes cid =
  let (ak, omitted_args) =
    begin match I.sgnLookup cid with
    | ConDec (name, package, o_a, status, ak, uni) -> (ak, o_a)
    | ConDef (name, package, o_a, ak, def, uni, _) -> (ak, o_a)
    | AbbrevDef (name, package, o_a, ak, def, uni) -> (ak, o_a)
    | _ -> raise NoModes end in
let rec count_args =
  begin function | Pi (_, ak') -> (+) 1 count_args ak' | _ -> 0 end in
let total_args = count_args ak in
List.tabulate
  (total_args,
    (begin function
     | x -> if x < omitted_args then begin S.OMIT end else begin S.MINUS end end))
let rec setModesUpTo x f = if x < 0 then begin () end
  else begin (begin setModesUpTo (x - 1) f; Sgn.set_modes (x, (f x)); () end) end
let rec sgnAutoCompress n f =
  begin try
          let modes = f n in
          begin Sgn.set_modes (n, modes);
          Sgn.update (n, (compress (n, (IntSyn.sgnLookup n)))) end
  with | NoModes -> () end
let rec sgnAutoCompressUpTo' n0 n f = if n0 > n then begin () end
  else begin
    (let _ =
       ((begin match Sgn.sub n0 with
         | Some _ -> ()
         | None ->
             (begin try
                      let modes = f n0 in
                      begin Sgn.set_modes (n0, modes);
                      Sgn.update (n0, (compress (n0, (IntSyn.sgnLookup n0))));
                      if (n0 mod_ 100) = 0
                      then begin print ((Int.toString n0) ^ "\n") end
                      else begin () end end
       with | NoModes -> () end) end)
(* if not, compress it *)) in
((sgnAutoCompressUpTo' (n0 + 1) n f)
(* has this entry already been processed? *))) end
let rec sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f
let check = Reductio.check
end