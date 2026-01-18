
(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
module type PRINT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    module Formatter : FORMATTER
    val implicit : bool ref
    val printInfix : bool ref
    val printDepth : int option ref
    val printLength : int option ref
    val noShadow : bool ref
    val formatDec : (IntSyn.dctx * IntSyn.__Dec) -> Formatter.format
    val formatDecList : (IntSyn.dctx * IntSyn.__Dec list) -> Formatter.format
    val formatDecList' :
      (IntSyn.dctx * (IntSyn.__Dec list * IntSyn.__Sub)) -> Formatter.format
    val formatExp : (IntSyn.dctx * IntSyn.__Exp) -> Formatter.format
    val formatSpine : (IntSyn.dctx * IntSyn.__Spine) -> Formatter.format list
    val formatConDec : IntSyn.__ConDec -> Formatter.format
    val formatConDecI : IntSyn.__ConDec -> Formatter.format
    val formatCnstr : IntSyn.__Cnstr -> Formatter.format
    val formatCtx : (IntSyn.dctx * IntSyn.dctx) -> Formatter.format
    val decToString : (IntSyn.dctx * IntSyn.__Dec) -> string
    val expToString : (IntSyn.dctx * IntSyn.__Exp) -> string
    val conDecToString : IntSyn.__ConDec -> string
    val cnstrToString : IntSyn.__Cnstr -> string
    val cnstrsToString : IntSyn.cnstr list -> string
    (* assigns names in contexts *)
    val ctxToString : (IntSyn.dctx * IntSyn.dctx) -> string
    val evarInstToString : (IntSyn.__Exp * string) list -> string
    val evarCnstrsToStringOpt : (IntSyn.__Exp * string) list -> string option
    val formatWorlds : Tomega.__Worlds -> Formatter.format
    val worldsToString : Tomega.__Worlds -> string
    val printSgn : unit -> unit
  end;;




(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Roberto Virga *)
module Print(Print:sig
                     (*! structure IntSyn' : INTSYN !*)
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Constraints : CONSTRAINTS
                     module Names : NAMES
                     module Formatter' : FORMATTER
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     module Symbol : SYMBOL
                   end) : PRINT =
  struct
    (*! structure IntSyn = IntSyn' !*)
    module Formatter = Formatter'
    module Tomega = Tomega
    (* Externally visible parameters *)
    let implicit = ref false__
    (* whether to print implicit arguments *)
    let printInfix = ref false__
    (* if implicit is ref true, whether to print infix ops when possible *)
    let printDepth = ref (None : int option)
    (* limit on term depth to print *)
    let printLength = ref (None : int option)
    (* limit on number of arguments to print *)
    let noShadow = ref false__
    (* if true, don't print shadowed constants as "%const%" *)
    (* Shorthands *)
    module I = IntSyn
    module FX = Names.Fixity
    module F = Formatter
    module T = Tomega
    let (lvars : I.__Block option ref list ref) = ref nil
    let rec lookuplvar l =
      let _ =
        if List.exists (function | r -> r = l) (!lvars)
        then ()
        else ((!) ((:=) lvars) lvars) @ [l] in
      let rec find (r::__l) n = if r = l then n else find __l (n + 1) in
      Int.toString (find (!lvars) 0)
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec nameOf = function | Some id -> id | None -> "_"
    let rec fmtEVar (__g, x) = Str0 (Symbol.evar (Names.evarName (__g, x)))
    let rec fmtAVar (__g, x) =
      Str0 (Symbol.evar ((Names.evarName (__g, x)) ^ "_"))
    let rec isNil =
      function | I.Nil -> true__ | App _ -> false__ | SClo (S, _) -> isNil S
    let rec subToSpine (depth, s) =
      let rec sTS =
        function
        | (Shift k, S) ->
            if k < depth
            then sTS ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S)
            else S
        | (Dot (Idx k, s), S) ->
            sTS (s, (I.App ((I.Root ((I.BVar k), I.Nil)), S)))
        | (Dot (Exp (__u), s), S) -> sTS (s, (I.App (__u, S))) in
      sTS (s, I.Nil)
    type __ArgStatus =
      | TooFew 
      | Exact of I.__Spine 
      | TooMany of (I.__Spine * I.__Spine) 
    let rec sclo' =
      function
      | (TooFew, s) -> TooFew
      | (Exact (S), s) -> Exact (I.SClo (S, s))
      | (TooMany (S, S'), s) -> TooMany ((I.SClo (S, s)), (I.SClo (S', s)))
    let rec sclo'' =
      function
      | (TooFew, s) -> TooFew
      | (Exact (S), s) -> Exact S
      | (TooMany (S, S'), s) -> TooMany (S, (I.SClo (S', s)))
    let rec dropImp =
      function
      | (0, S, 0) -> Exact S
      | (0, S, n) ->
          let rec checkArgNumber =
            function
            | (I.Nil, 0) -> Exact S
            | (I.Nil, k) -> TooFew
            | ((App _ as S'), 0) -> TooMany (S, S')
            | (App (__u, S'), k) -> checkArgNumber (S', (k - 1))
            | (SClo (S', s), k) -> sclo'' ((checkArgNumber (S', k)), s) in
          checkArgNumber (S, n)
      | (i, App (__u, S), n) -> dropImp ((i - 1), S, n)
      | (i, SClo (S, s), n) -> sclo' ((dropImp (i, S, n)), s)
      | (i, I.Nil, n) -> TooFew
    let rec exceeded =
      function | (_, None) -> false__ | ((n : int), Some (m : int)) -> n >= m
    type ctxt =
      | Ctxt of (FX.fixity * F.format list * int) 
    type opargs =
      | OpArgs of (FX.fixity * F.format list * I.__Spine) 
      | EtaLong of I.__Exp 
    let noCtxt =
      Ctxt
        ((FX.Prefix (FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec))))), [], 0)
    let binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
    let arrowPrec = FX.dec FX.minPrec
    let juxPrec = FX.inc FX.maxPrec
    let rec arrow (V1, V2) =
      OpArgs
        ((FX.Infix (arrowPrec, FX.Right)), [F.Break; sym "->"; F.space],
          (I.App (V1, (I.App (V2, I.Nil)))))
    let appCtxt = Ctxt (FX.Nonfix, [], 0)
    let rec fixityCon =
      function
      | Const cid -> Names.getFixity cid
      | Skonst cid -> FX.Nonfix
      | Def cid -> Names.getFixity cid
      | NSDef cid -> Names.getFixity cid
      | _ -> FX.Nonfix
    let rec impCon =
      function
      | Const cid -> I.constImp cid
      | Skonst cid -> I.constImp cid
      | Def cid -> I.constImp cid
      | NSDef cid -> I.constImp cid
      | _ -> 0
    let rec argNumber =
      function
      | FX.Nonfix -> 0
      | Infix _ -> 2
      | Prefix _ -> 1
      | Postfix _ -> 1
    let rec fmtConstPath (f, Qid (ids, id)) =
      F.hVbox
        (foldr
           (function
            | (id, fmt) -> ((::) (Str0 (Symbol.str id)) sym ".") :: fmt)
           [Str0 (f id)] ids)
    let rec parmDec =
      function | ((__d)::__l, 1) -> __d | ((__d)::__l, j) -> parmDec (__l, (j - 1))
    let rec parmName (cid, i) =
      let (Gsome, Gblock) = I.constBlock cid in
      match parmDec (Gblock, i) with
      | Dec (Some pname, _) -> pname
      | Dec (None, _) -> Int.toString i
    let rec projName =
      function
      | (__g, Proj (Bidx k, i)) ->
          let BDec (Some bname, (cid, t)) = I.ctxLookup (__g, k) in
          (^) (bname ^ "_") parmName (cid, i)
      | (__g, Proj (LVar (r, _, (cid, t)), i)) -> (^) "_" parmName (cid, i)
      | (__g, Proj (Inst iota, i)) -> "*"
    let rec constQid cid =
      if !noShadow
      then Names.conDecQid (I.sgnLookup cid)
      else Names.constQid cid
    let rec cidToFmt cid = F.String (Names.qidToString (Names.constQid cid))
    let rec formatCids =
      function
      | nil -> nil
      | cid::nil -> [cidToFmt cid]
      | cid::cids ->
          (::) (((::) ((cidToFmt cid) :: F.Break) F.String "|") :: F.space)
            formatCids cids
    let rec formatWorlds (Worlds cids) =
      F.hbox [F.String "("; F.hVbox (formatCids cids); F.String ")"]
    let rec worldsToString (W) = F.makestring_fmt (formatWorlds W)
    let rec fmtCon =
      function
      | (__g, BVar n) -> Str0 (Symbol.bvar (Names.bvarName (__g, n)))
      | (__g, Const cid) -> fmtConstPath (Symbol.const, (constQid cid))
      | (__g, Skonst cid) -> fmtConstPath (Symbol.skonst, (constQid cid))
      | (__g, Def cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (__g, NSDef cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (__g, FVar (name, _, _)) -> Str0 (Symbol.fvar name)
      | (__g, (Proj (Bidx k, i) as H)) -> Str0 (Symbol.const (projName (__g, H)))
      | (__g, (Proj (LVar ((ref (None) as r), sk, (cid, t)), i) as H)) ->
          let n = lookuplvar r in
          fmtConstPath
            ((function
              | l0 ->
                  Symbol.const
                    ((^) ((("#[" ^ l0) ^ n) ^ "]") projName (__g, H))),
              (constQid cid))
      | (__g, FgnConst (cs, conDec)) ->
          let name = I.conDecName conDec in
          (match ((Names.constLookup (Names.Qid (nil, name))), (!noShadow))
           with
           | (Some _, false__) -> Str0 (Symbol.const (("%" ^ name) ^ "%"))
           | _ -> Str0 (Symbol.const name))
    let rec evarArgs (__g, d, x, s) =
      OpArgs (FX.Nonfix, [fmtEVar (__g, x)], (subToSpine ((I.ctxLength __g), s)))
    let rec evarArgs' (__g, d, x, s) =
      OpArgs (FX.Nonfix, [fmtAVar (__g, x)], (subToSpine ((I.ctxLength __g), s)))
    let rec fst =
      function
      | (App (__U1, _), s) -> (__U1, s)
      | (SClo (S, s'), s) -> fst (S, (I.comp (s', s)))
    let rec snd =
      function
      | (App (__U1, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, (I.comp (s', s)))
    let rec elide l =
      match !printLength with | None -> false__ | Some l' -> l > l'
    let ldots = sym "..."
    let rec addots l =
      match !printLength with | None -> false__ | Some l' -> l = l'
    let rec parens ((fixity', fixity), fmt) =
      if FX.leq ((FX.prec fixity), (FX.prec fixity'))
      then F.hbox [sym "("; fmt; sym ")"]
      else fmt
    let rec eqFix =
      function
      | (Infix (p, FX.Left), Infix (p', FX.Left)) -> p = p'
      | (Infix (p, FX.Right), Infix (p', FX.Right)) -> p = p'
      | (Prefix p, Prefix p') -> p = p'
      | (Postfix p, Postfix p') -> p = p'
      | _ -> false__
    let rec addAccum =
      function
      | (fmt, _, nil) -> fmt
      | (fmt, Infix (_, FX.Left), accum) -> F.hVbox ([fmt] @ accum)
      | (fmt, Infix (_, FX.Right), accum) -> F.hVbox (accum @ [fmt])
      | (fmt, Prefix _, accum) -> F.hVbox (accum @ [fmt])
      | (fmt, Postfix _, accum) -> F.hVbox ([fmt] @ accum)
    let rec aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)
    let rec fmtUni = function | I.Type -> sym "type" | I.Kind -> sym "kind"
    let rec fmtExpW =
      function
      | (__g, d, ctx, (Uni (__l), s)) -> aa (ctx, (fmtUni __l))
      | (__g, d, ctx, (Pi (((Dec (_, V1) as __d), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let __d' = Names.decLUName (__g, __d) in
               fmtLevel
                 ((I.Decl (__g, __d')), d, ctx,
                   ((braces (__g, d, ((__d', V2), s))), (I.dot1 s)))
           | I.Meta ->
               let __d' = Names.decLUName (__g, __d) in
               fmtLevel
                 ((I.Decl (__g, __d')), d, ctx,
                   ((braces (__g, d, ((__d', V2), s))), (I.dot1 s)))
           | I.No ->
               fmtLevel
                 ((I.Decl (__g, __d)), d, ctx,
                   ((arrow ((I.EClo (V1, I.shift)), V2)), (I.dot1 s))))
      | (__g, d, ctx, (Pi (((BDec _ as __d), P), V2), s)) ->
          let __d' = Names.decLUName (__g, __d) in
          fmtLevel
            ((I.Decl (__g, __d')), d, ctx,
              ((braces (__g, d, ((__d', V2), s))), (I.dot1 s)))
      | (__g, d, ctx, (Pi (((ADec _ as __d), P), V2), s)) ->
          let braces =
            OpArgs
              ((FX.Prefix binderPrec), [sym "["; sym "_"; sym "]"; F.Break],
                (IntSyn.App (V2, IntSyn.Nil))) in
          fmtLevel ((I.Decl (__g, __d)), d, ctx, (braces, (I.dot1 s)))
      | (__g, d, ctx, ((Root (R) as __u), s)) ->
          fmtOpArgs (__g, d, ctx, (opargs (__g, d, R)), s)
      | (__g, d, ctx, (Lam (__d, __u), s)) ->
          let __d' = Names.decLUName (__g, __d) in
          fmtLevel
            ((I.Decl (__g, __d')), d, ctx,
              ((brackets (__g, d, ((__d', __u), s))), (I.dot1 s)))
      | (__g, d, ctx, ((EVar _ as x), s)) ->
          if !implicit
          then aa (ctx, (F.hVbox ((::) (fmtEVar (__g, x)) fmtSub (__g, d, s))))
          else fmtOpArgs (__g, d, ctx, (evarArgs (__g, d, x, s)), I.id)
      | (__g, d, ctx, ((AVar _ as x), s)) ->
          if !implicit
          then aa (ctx, (F.hVbox ((::) (fmtAVar (__g, x)) fmtSub (__g, d, s))))
          else fmtOpArgs (__g, d, ctx, (evarArgs' (__g, d, x, s)), I.id)
      | (__g, d, ctx, ((FgnExp csfe as __u), s)) ->
          fmtExp (__g, d, ctx, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec opargsImplicit (__g, d, (C, S)) =
      OpArgs (FX.Nonfix, [fmtCon (__g, C)], S)
    let rec opargsImplicitInfix (__g, d, ((C, S) as R)) =
      let fixity = fixityCon C in
      match fixity with
      | Infix _ -> opargsExplicit (__g, d, R)
      | _ -> OpArgs (FX.Nonfix, [fmtCon (__g, C)], S)
    let rec opargsExplicit (__g, d, ((C, S) as R)) =
      let opFmt = fmtCon (__g, C) in
      let fixity = fixityCon C in
      let rec oe =
        function
        | Exact (S') ->
            (match fixity with
             | FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], S')
             | Prefix _ -> OpArgs (fixity, [opFmt; F.Break], S')
             | Postfix _ -> OpArgs (fixity, [F.Break; opFmt], S')
             | Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.space], S'))
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root R))
        | TooMany (S', S'') ->
            let opFmt' = fmtOpArgs (__g, d, noCtxt, (oe (Exact S')), I.id) in
            OpArgs (FX.Nonfix, [F.hbox [sym "("; opFmt'; sym ")"]], S'') in
      oe (dropImp ((impCon C), S, (argNumber fixity)))
    let rec opargs (__g, d, R) =
      if !implicit
      then
        (if !printInfix
         then opargsImplicitInfix (__g, d, R)
         else opargsImplicit (__g, d, R))
      else opargsExplicit (__g, d, R)
    let rec fmtOpArgs =
      function
      | (__g, d, ctx, (OpArgs (_, opFmts, S') as oa), s) ->
          if isNil S'
          then aa (ctx, (List.hd opFmts))
          else fmtLevel (__g, d, ctx, (oa, s))
      | (__g, d, ctx, EtaLong (__u'), s) -> fmtExpW (__g, d, ctx, (__u', s))
    let rec fmtSub (__g, d, s) = (::) (Str "[") fmtSub' (__g, d, 0, s)
    let rec fmtSub' (__g, d, l, s) =
      if elide l then [ldots] else fmtSub'' (__g, d, l, s)
    let rec fmtSub'' =
      function
      | (__g, d, l, Shift k) -> [Str ((^) "^" Int.toString k); Str "]"]
      | (__g, d, l, Dot (Idx k, s)) ->
          (::) (((::) (Str (Names.bvarName (__g, k))) Str ".") :: F.Break)
            fmtSub' (__g, d, (l + 1), s)
      | (__g, d, l, Dot (Exp (__u), s)) ->
          (::) (((::) (fmtExp (__g, (d + 1), noCtxt, (__u, I.id))) Str ".") ::
                  F.Break)
            fmtSub' (__g, d, (l + 1), s)
    let rec fmtExp (__g, d, ctx, (__u, s)) =
      if exceeded (d, (!printDepth))
      then sym "%%"
      else fmtExpW (__g, d, ctx, (Whnf.whnf (__u, s)))
    let rec fmtSpine =
      function
      | (__g, d, l, (I.Nil, _)) -> []
      | (__g, d, l, (SClo (S, s'), s)) ->
          fmtSpine (__g, d, l, (S, (I.comp (s', s))))
      | (__g, d, l, (App (__u, S), s)) ->
          if elide l
          then []
          else
            if addots l
            then [ldots]
            else
              (::) (fmtExp (__g, (d + 1), appCtxt, (__u, s))) fmtSpine'
                (__g, d, l, (S, s))
    let rec fmtSpine' =
      function
      | (__g, d, l, (I.Nil, _)) -> []
      | (__g, d, l, (SClo (S, s'), s)) ->
          fmtSpine' (__g, d, l, (S, (I.comp (s', s))))
      | (__g, d, l, (S, s)) -> (::) F.Break fmtSpine (__g, d, (l + 1), (S, s))
    let rec fmtLevel =
      function
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((FX.Nonfix as fixity), fmts, S), s)) ->
          let atm = fmtSpine (__g, d, 0, (S, s)) in
          addAccum
            ((parens
                ((fixity', fixity), (F.hVbox ((fmts @ [F.Break]) @ atm)))),
              fixity', accum)
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (p, FX.Left) as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity, fixity') in
          let rhs =
            if accMore && (elide l)
            then []
            else
              if accMore && (addots l)
              then fmts @ [ldots]
              else
                fmts @
                  [fmtExp
                     (__g, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                       (snd (S, s)))] in
          if accMore
          then
            fmtExp
              (__g, d, (Ctxt (fixity, (rhs @ accum), (l + 1))), (fst (S, s)))
          else
            (let both = fmtExp (__g, d, (Ctxt (fixity, rhs, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (p, FX.Right) as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity, fixity') in
          let lhs =
            if accMore && (elide l)
            then []
            else
              if accMore && (addots l)
              then [ldots] @ fmts
              else
                [fmtExp
                   (__g, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                     (fst (S, s)))]
                  @ fmts in
          if accMore
          then
            fmtExp
              (__g, d, (Ctxt (fixity, (accum @ lhs), (l + 1))), (snd (S, s)))
          else
            (let both = fmtExp (__g, d, (Ctxt (fixity, lhs, 0)), (snd (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (_, FX.None) as fixity), fmts, S), s)) ->
          let lhs =
            fmtExp (__g, (d + 1), (Ctxt (fixity, nil, 0)), (fst (S, s))) in
          let rhs =
            fmtExp (__g, (d + 1), (Ctxt (fixity, nil, 0)), (snd (S, s))) in
          addAccum
            ((parens ((fixity', fixity), (F.hVbox (([lhs] @ fmts) @ [rhs])))),
              fixity', accum)
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Prefix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [ldots; F.Break] else fmts in
          if accMore
          then
            fmtExp
              (__g, d, (Ctxt (fixity, (accum @ pfx), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (__g, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
      | (__g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Postfix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [F.Break; ldots] else fmts in
          if accMore
          then
            fmtExp
              (__g, d, (Ctxt (fixity, (pfx @ accum), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (__g, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
    let rec braces (__g, d, ((__d, __v), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "{"; fmtDec (__g, d, (__d, s)); sym "}"; F.Break],
          (IntSyn.App (__v, IntSyn.Nil)))
    let rec brackets (__g, d, ((__d, __u), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "["; fmtDec (__g, d, (__d, s)); sym "]"; F.Break],
          (IntSyn.App (__u, IntSyn.Nil)))
    let rec fmtDec =
      function
      | (__g, d, (Dec (x, __v), s)) ->
          F.hVbox
            [Str0 (Symbol.bvar (nameOf x));
            sym ":";
            fmtExp (__g, (d + 1), noCtxt, (__v, s))]
      | (__g, d, (BDec (x, (cid, t)), s)) ->
          let (Gsome, Gblock) = I.constBlock cid in
          F.hVbox
            ((@) [Str0 (Symbol.const (nameOf x)); sym ":"] fmtDecList'
               (__g, (Gblock, (I.comp (t, s)))))
      | (__g, d, (ADec (x, _), s)) ->
          F.hVbox [Str0 (Symbol.bvar (nameOf x)); sym ":_"]
      | (__g, d, (NDec (Some name), s)) -> F.hVbox [sym name]
    let rec fmtDecList' =
      function
      | (G0, (nil, s)) -> nil
      | (G0, ((__d)::nil, s)) ->
          ((::) ((::) (sym "{") fmtDec (G0, 0, (__d, s))) sym "}") :: nil
      | (G0, ((__d)::__l, s)) ->
          (::) (((::) ((::) (sym "{") fmtDec (G0, 0, (__d, s))) sym "}") ::
                  F.Break)
            fmtDecList' ((I.Decl (G0, __d)), (__l, (I.dot1 s)))
    let rec skipI =
      function
      | (0, __g, __v) -> (__g, __v)
      | (i, __g, Pi ((__d, _), __v)) ->
          skipI ((i - 1), (I.Decl (__g, (Names.decEName (__g, __d)))), __v)
    let rec skipI2 =
      function
      | (0, __g, __v, __u) -> (__g, __v, __u)
      | (i, __g, Pi ((__d, _), __v), Lam (__d', __u)) ->
          skipI2 ((i - 1), (I.Decl (__g, (Names.decEName (__g, __d')))), __v, __u)
    let rec ctxToDecList =
      function
      | (I.Null, __l) -> __l
      | (Decl (__g, __d), __l) -> ctxToDecList (__g, (__d :: __l))
    let rec fmtDecList =
      function
      | (G0, nil) -> nil
      | (G0, (__d)::nil) ->
          ((::) ((::) (sym "{") fmtDec (G0, 0, (__d, I.id))) sym "}") :: nil
      | (G0, (__d)::__l) ->
          (::) (((::) ((::) (sym "{") fmtDec (G0, 0, (__d, I.id))) sym "}") ::
                  F.Break)
            fmtDecList ((I.Decl (G0, __d)), __l)
    let rec fmtCtx (G0, __g) = fmtDecList (G0, (ctxToDecList (__g, nil)))
    let rec fmtBlock =
      function
      | (I.Null, Lblock) ->
          [sym "block"; F.Break] @ (fmtDecList (I.Null, Lblock))
      | (Gsome, Lblock) ->
          [F.hVbox ([sym "some"; F.space] @ (fmtCtx (I.Null, Gsome)));
          F.Break;
          F.hVbox ([sym "block"; F.space] @ (fmtDecList (Gsome, Lblock)))]
    let rec fmtConDec =
      function
      | (hide, (ConDec (_, _, imp, _, __v, __l) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__g, __v) = if hide then skipI (imp, I.Null, __v) else (I.Null, __v) in
          let Vfmt = fmtExp (__g, 0, noCtxt, (__v, I.id)) in
          F.hVbox
            [fmtConstPath (Symbol.const, qid);
            F.space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | (hide, (SkoDec (_, _, imp, __v, __l) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__g, __v) = if hide then skipI (imp, I.Null, __v) else (I.Null, __v) in
          let Vfmt = fmtExp (__g, 0, noCtxt, (__v, I.id)) in
          F.hVbox
            [sym "%skolem";
            F.Break;
            fmtConstPath (Symbol.skonst, qid);
            F.space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | (hide, (BlockDec (_, _, Gsome, Lblock) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.hVbox
            (([sym "%block";
              F.Break;
              fmtConstPath (Symbol.label, qid);
              F.space;
              sym ":";
              F.Break] @ (fmtBlock (Gsome, Lblock))) @ [sym "."])
      | (hide, (BlockDef (_, _, W) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.hVbox
            ([sym "%block";
             F.Break;
             fmtConstPath (Symbol.label, qid);
             F.space;
             sym "=";
             F.Break] @ ((formatWorlds (T.Worlds W)) :: [sym "."]))
      | (hide, (ConDef (_, _, imp, __u, __v, __l, _) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__g, __v, __u) =
            if hide then skipI2 (imp, I.Null, __v, __u) else (I.Null, __v, __u) in
          let Vfmt = fmtExp (__g, 0, noCtxt, (__v, I.id)) in
          let Ufmt = fmtExp (__g, 0, noCtxt, (__u, I.id)) in
          F.hVbox
            [fmtConstPath (Symbol.def, qid);
            F.space;
            sym ":";
            F.Break;
            Vfmt;
            F.Break;
            sym "=";
            F.space;
            Ufmt;
            sym "."]
      | (hide, (AbbrevDef (_, _, imp, __u, __v, __l) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__g, __v, __u) =
            if hide then skipI2 (imp, I.Null, __v, __u) else (I.Null, __v, __u) in
          let Vfmt = fmtExp (__g, 0, noCtxt, (__v, I.id)) in
          let Ufmt = fmtExp (__g, 0, noCtxt, (__u, I.id)) in
          F.hVbox
            [fmtConstPath (Symbol.def, qid);
            F.space;
            sym ":";
            F.Break;
            Vfmt;
            F.Break;
            sym "=";
            F.space;
            Ufmt;
            sym "."]
    let rec fmtCnstr =
      function
      | I.Solved -> [Str "Solved Constraint"]
      | Eqn (__g, __U1, __U2) ->
          let __g' = Names.ctxLUName __g in
          [F.hVbox
             [fmtExp (__g', 0, noCtxt, (__U1, I.id));
             F.Break;
             sym "=";
             F.space;
             fmtExp (__g', 0, noCtxt, (__U2, I.id))]]
      | FgnCnstr ((cs, _) as csfc) ->
          let rec fmtExpL =
            function
            | nil -> [Str "Empty Constraint"]
            | (__g, __u)::nil ->
                [fmtExp ((Names.ctxLUName __g), 0, noCtxt, (__u, I.id))]
            | (__g, __u)::expL ->
                (@) [fmtExp ((Names.ctxLUName __g), 0, noCtxt, (__u, I.id));
                    Str ";";
                    F.Break]
                  fmtExpL expL in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ())
    let rec fmtCnstrL =
      function
      | nil -> [Str "Empty Constraint"]
      | (ref (Cnstr))::nil -> (fmtCnstr Cnstr) @ [Str "."]
      | (ref (Cnstr))::cnstrL ->
          ((fmtCnstr Cnstr) @ [Str ";"; F.Break]) @ (fmtCnstrL cnstrL)
    let rec abstractLam =
      function
      | (I.Null, __u) -> __u
      | (Decl (__g, __d), __u) -> abstractLam (__g, (I.Lam (__d, __u)))
    let rec fmtNamedEVar =
      function
      | ((EVar (_, __g, _, _) as __u), name) ->
          let __u' = abstractLam (__g, __u) in
          F.hVbox
            [Str0 (Symbol.evar name);
            F.space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (__u', I.id))]
      | (__u, name) ->
          F.hVbox
            [Str0 (Symbol.evar name);
            F.space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (__u, I.id))]
    let rec fmtEVarInst =
      function
      | nil -> [Str "Empty Substitution"]
      | (__u, name)::nil -> [fmtNamedEVar (__u, name)]
      | (__u, name)::__Xs ->
          (::) (((::) (fmtNamedEVar (__u, name)) Str ";") :: F.Break)
            fmtEVarInst __Xs
    let rec collectEVars =
      function
      | (nil, __Xs) -> __Xs
      | ((__u, _)::Xnames, __Xs) ->
          collectEVars
            (Xnames, (Abstract.collectEVars (I.Null, (__u, I.id), __Xs)))
    let rec eqCnstr r1 r2 = r1 = r2
    let rec mergeConstraints =
      function
      | (nil, cnstrs2) -> cnstrs2
      | (cnstr::cnstrs1, cnstrs2) ->
          if List.exists (eqCnstr cnstr) cnstrs2
          then mergeConstraints (cnstrs1, cnstrs2)
          else cnstr :: (mergeConstraints (cnstrs1, cnstrs2))
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (ref (None), _, _, cnstrs))::__Xs ->
          mergeConstraints
            ((Constraints.simplify (!cnstrs)), (collectConstraints __Xs))
      | _::__Xs -> collectConstraints __Xs
    (* Disambiguation of block logic variable names *)
    (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
    (* fmtEVar (__g, x) = "x", the name of the EVar x *)
    (* Effect: Names.evarName will assign a name if x does not yet have one *)
    (* should probably be a new Symbol constructor for AVars -kw *)
    (* isNil S = true iff S == Nil *)
    (* subToSpine (depth, s) = S
     Invariants:
     If  __g |- s : __g', Gd  with  |Gd| = depth
     then __g |- S : {{Gd}} C > C  for any C

     This is used to print
      __g |- Xl[s] : A[s]  for  __g', Gd |- Xl : A
     as
      __g |- Xr @ S : A[s]  for  __g' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)
    (* k >= depth *)
    (* Eta violation, but probably inconsequential -kw *)
    (* ArgStatus classifies the number of arguments to an operator *)
    (* dropImp (i, S, n) for n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = S0 @ S'' and |S0| = n
  *)
    (* n >= 1 *)
    (* exceeded (n:int, b:bound) = true if n exceeds bound b *)
    (* Type ctxt is the "left context" of an expression to be printed.
     It works as an accumulator and is used to decide whether to insert of parentheses
     or elide nested subexpressions.

     Ctxt (fixity, formats, length)
     is the "left context" of an expression to be printed.  When printed
     it will be the string prefixed to the string representing the
     current expression.

     fixity is the operator and precedence in effect,
     formats is the list of formats which make up the left context
     length is the length of the left context (used for printLength elision)
  *)
    (* Type opargs represent the operator/arguments form of roots.

     OpArgs (fixity, formats, S)
     represents the printed form of a root expression H @ S:
      fixity is the fixity of H (possibly FX.Nonfix),
      formats is a list of formats for printing H (including surrounding breaks
         and whitespace),
      S is the spine of arguments.
      There may be additional argument in S which are ignored.

     EtaLong (__u)
     represents an expression __u' which had to be eta-expanded to __u
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)
    (* empty left context *)
    (* braces and brackets as a prefix operator *)
    (* colon is of FX.minPrec-2, but doesn't occur in printing *)
    (* arrow as infix operator *)
    (* juxtaposition as infix operator *)
    (* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)
    (* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)
    (* fixityCon (c) = fixity of c *)
    (* BVar, FVar *)
    (* impCon (c) = number of implicit arguments to c *)
    (* BVar, FVar *)
    (* argNumber (fixity) = number of required arguments to head with fixity *)
    (* FIX: this is certainly not correct -kw *)
    (* names should have been assigned by invar
         iant, None imppossible *)
    (* note: this obscures LVar identity! *)
    (* no longer Tue Mar  1 13:32:21 2011 -cs *)
    (* to be fixed --cs *)
    (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
    (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
    (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
    (* the user has re-defined this name *)
    (* evarArgs (__g, d, x, s)
     formats x[s] by printing x @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
    (* fst (S, s) = __U1, the first argument in S[s] *)
    (* snd (S, s) = __U2, the second argument in S[s] *)
    (* elide (l) = true  iff  l exceeds the optional printLength bound *)
    (* addots (l) = true  iff  l is equal to the optional printLength bound *)
    (* parens ((fixity', fixity), fmt) = fmt'
     where fmt' contains additional parentheses when the precedence of
     fixity' is greater or equal to that of fixity, otherwise it is unchanged.
  *)
    (* eqFix (fixity, fixity') = true iff fixity and fixity' have the same precedence
     Invariant: only called when precedence comparison is necessary to resolve
                the question if parentheses should be added
  *)
    (* Infix(_,None) should never be asked *)
    (* Nonfix should never be asked *)
    (* addAccum (fmt, fixity, accum) = fmt'
     Extend the current "left context" with operator fixity
     and format list accum by fmt.

     This is not very efficient, since the accumulator is copied
     for right associative or prefix operators.
  *)
    (* FX.Infix(None,_), FX.Nonfix should never arise *)
    (* aa (ctx, fmt) = fmt'
     Extend the current "left context" by fmt.
  *)
    (* fmtUni (__l) = "__l" *)
    (* impossible, included for robustness *)
    (* fmtExpW (__g, d, ctx, (__u, s)) = fmt

     format the expression __u[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       __g is a "printing context" (names in it are unique, but
            types may be incorrect) approximating __g'
       __g'' |- __u : __v   __g' |- s : __g''  (so  __g' |- __u[s] : __v[s])
       (__u,s) in whnf
  *)
    (* if Pi is dependent but anonymous, invent name here *)
    (* could sometimes be EName *)
    (* I.decSub (__d', s) *)
    (* I.decSub (__d', s) *)
    (* I.decSub (__d, s) *)
    (* -bp *)
    (*      val __d' = Names.decLUName (__g, __d) *)
    (* s = id *)
    (* I.Redex not possible *)
    (* I.decSub (__d', s) *)
    (* assume dereferenced during whnf *)
    (* assume dereferenced during whnf *)
    (* I.EClo not possible for Whnf *)
    (* for internal printing *)
    (* opargsImplicit (__g, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
    (* for flit printing -jcreed 6/2005 *)
    (* opargsImplicit (__g, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix declarations are obeyed. It is an
     error to call this function if an infix declaration has been made for
     a term which has more than two arguments. (This could have happened if the term
     had two explicit arguments and further implicit arguments)

     In other words, it is an error if an infix declaration had any
     implicit arguments.
  *)
    (* Can't have implicit arguments by invariant *)
    (* for external printing *)
    (* opargsExplicit (__g, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     __g |- C @ S (no substitution involved)
  *)
    (* extra arguments to infix operator *)
    (* S' - all non-implicit arguments *)
    (* S'' - extra arguments *)
    (* parens because juxtaposition has highest precedence *)
    (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
    (* opargs (__g, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
    (* fmtOpArgs (__g, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     __g is a printing context approximating __g', and __g' |- oa[s] is valid.
  *)
    (* opFmts = [fmtCon(__g,C)] *)
    (* fmtSub (__g, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
    (* fmtExp (__g, d, ctx, (__u, s)) = fmt
     format or elide __u[s] at printing depth d and add to the left context ctx.

     __g is a printing context approximation __g' and __g' |- __u[s] is valid.
  *)
    (* fmtSpine (__g, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context __g which approximates __g', where __g' |- S[s] is valid
  *)
    (* necessary? *)
    (* fmtSpine' (__g, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading "Break" and increment printing length
  *)
    (* fmtLevel (__g, d, ctx, (oa, s)) = fmt

     format operator/arguments form oa[s] at printing depth d and add the result
     to the left context ctx.

     This is the main function flattening out infix/prefix/postfix operator
     sequences.  It compares the fixity of the operator of the current left
     context with the operator at the head of the current operator/arguments
     form and decides how to extend the accumulator and whether to insert
     parentheses.
  *)
    (* atm must not be empty, otherwise bug below *)
    (* F.hVbox doesn't work if last item of HVbox is F.Break *)
    (* possible improvement along the following lines: *)
    (*
           if (#2 (F.width (F.hbox (fmts)))) < 4
           then F.hbox [F.hbox(fmts), F.hVbox0 1 1 1 atm]
           else ...
        *)
    (* braces (__g, d, ((__d, __v), s)) = oa
     convert declaration __d[s] as a prefix pi-abstraction into operator/arguments
     form with prefix "{__d}" and argument __v at printing depth d in printing
     context __g approximating __g'.

     Invariants:
      __g' |- __d[s] decl
      __g' |- __v : __l  [NOTE: s does not apply to __v!]
  *)
    (* brackets (__g, d, ((__d, __u), s)) = oa
     convert declaration __d[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix "[__d]" and argument __u at printing depth d in printing
     context __g approximating __g'.

     Invariants:
      __g' |- __d[s] decl
      __g' |- __u : __v  [NOTE: s does not apply to __u!]
  *)
    (* fmtDec (__g, d, (__d, s)) = fmt
     format declaration __d[s] at printing depth d in printing context __g approximating __g'.

     Invariants:
      __g' |- __d[s] decl
  *)
    (* alternative with more whitespace *)
    (* F.hVbox [Str0 (Symbol.bvar (nameOf (x))), F.space, sym ":", F.Break,
                  fmtExp (__g, d+1, noCtxt, (__v,s))]
      *)
    (* alternative with more whitespace *)
    (* F.hVbox [Str0 (Symbol.bvar (nameOf (x))), F.space, sym ":", F.Break,
                  fmtExp (__g, d+1, noCtxt, (__v,s))]
      *)
    (* Assume unique names are already assigned in G0 and __g! *)
    (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
    (* reset variable names in between to align names of type __v and definition __u *)
    (* val _ = Names.varReset () *)
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.hVbox [Str0 (Symbol.def (name)), F.space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.space,
                         Ufmt, sym "."],
                F.Break,
                F.hVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*)
    (* reset variable names in between to align names of type __v and definition __u *)
    (* val _ = Names.varReset () *)
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.hVbox [Str0 (Symbol.def (name)), F.space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.space,
                         Ufmt, sym "."],
                F.Break,
                F.hVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
*)
    (* fmtNamedEVar, fmtEVarInst and evarInstToString are used to print
     instantiations of EVars occurring in queries.  To that end, a list of
     EVars paired with their is passed, thereby representing a substitution
     for logic variables.

     We always raise AVars to the empty context.
  *)
    (* used for proof term variables in queries *)
    (* collectEVars and collectConstraints are used to print constraints
     associated with EVars in a instantiation of variables occurring in queries.
  *)
    (* In the functions below, __g must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
    let rec formatDec (__g, __d) = fmtDec (__g, 0, (__d, I.id))
    let rec formatDecList (__g, __d) = F.hVbox (fmtDecList (__g, __d))
    let rec formatDecList' (__g, (__d, s)) = F.hVbox (fmtDecList' (__g, (__d, s)))
    let rec formatExp (__g, __u) = fmtExp (__g, 0, noCtxt, (__u, I.id))
    let rec formatSpine (__g, S) = fmtSpine (__g, 0, 0, (S, I.id))
    let rec formatConDec condec = fmtConDec (false__, condec)
    let rec formatConDecI condec = fmtConDec (true__, condec)
    let rec formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
    let rec formatCnstrs cnstrL = F.Vbox0 0 1 (fmtCnstrL cnstrL)
    let rec formatCtx (G0, __g) = F.hVbox (fmtCtx (G0, __g))
    (* assumes G0 and __g are named *)
    let rec decToString (__g, __d) = F.makestring_fmt (formatDec (__g, __d))
    let rec expToString (__g, __u) = F.makestring_fmt (formatExp (__g, __u))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
    let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
    let rec ctxToString (G0, __g) = F.makestring_fmt (formatCtx (G0, __g))
    let rec evarInstToString (Xnames) =
      F.makestring_fmt (F.hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
    let rec evarCnstrsToStringOpt (Xnames) =
      let __Ys = collectEVars (Xnames, nil) in
      let cnstrL = collectConstraints __Ys in
      ((match cnstrL with | nil -> None | _ -> Some (cnstrsToString cnstrL))
        (* collect EVars in instantiations *))
    let rec printSgn () =
      IntSyn.sgnApp
        (function
         | cid ->
             (print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
              print "\n"))
    let formatWorlds = formatWorlds
    let worldsToString = worldsToString
  end ;;




module SymbolAscii = (Make_SymbolAscii)(struct  end)
module SymbolTeX = (Make_SymbolTeX)(struct  end)
(*
structure WorldPrint = WorldPrint 
  (structure Global = Global
   ! structure IntSyn = IntSyn !*)
(*! structure Tomega' = Tomega !*)
module Print =
  (Make_Print)(struct
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolAscii
               end)
module ClausePrint =
  (Make_ClausePrint)(struct
                       (*! structure IntSyn' = IntSyn !*)
                       module Whnf = Whnf
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = Print
                       module Symbol = SymbolAscii
                     end)
module PrintTeX =
  (Make_Print)(struct
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolTeX
               end)
module ClausePrintTeX =
  (Make_ClausePrint)(struct
                       (*! structure IntSyn' = IntSyn !*)
                       module Whnf = Whnf
                       module Constraints = Constraints
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = PrintTeX
                       module Symbol = SymbolTeX
                     end)
module PrintTwega =
  (Make_PrintTwega)(struct
                      (*! structure IntSyn' = IntSyn !*)
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end)
module PrintXML =
  (Make_PrintXML)(struct
                    (*! structure IntSyn' = IntSyn !*)
                    module Whnf = Whnf
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Names = Names
                    module Formatter' = Formatter
                  end)
module PrintOMDoc =
  (Make_PrintOMDoc)(struct
                      (*! structure IntSyn' = IntSyn !*)
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end);;
