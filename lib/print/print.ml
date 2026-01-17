
module type PRINT  =
  sig
    module Formatter :
    ((FORMATTER)(* Printing *)(* Author: Frank Pfenning *)
    (* Modified: Jeff Polakow *)(*! structure IntSyn : INTSYN !*))
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
    val ctxToString :
      (IntSyn.dctx * IntSyn.dctx) ->
        ((string)(* assigns names in contexts *))
    val evarInstToString : (IntSyn.__Exp * string) list -> string
    val evarCnstrsToStringOpt : (IntSyn.__Exp * string) list -> string option
    val formatWorlds : Tomega.__Worlds -> Formatter.format
    val worldsToString : Tomega.__Worlds -> string
    val printSgn : unit -> unit
  end;;




module Print(Print:sig
                     module Whnf : WHNF
                     module Abstract : ABSTRACT
                     module Constraints : CONSTRAINTS
                     module Names : NAMES
                     module Formatter' : FORMATTER
                     module Symbol :
                     ((SYMBOL)(* Printing *)(* Author: Frank Pfenning *)
                     (* Modified: Jeff Polakow, Roberto Virga *)
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)(*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*))
                   end) : PRINT =
  struct
    module Formatter =
      ((Formatter')(*! structure IntSyn = IntSyn' !*))
    module Tomega = Tomega
    let ((implicit)(* Externally visible parameters *)) =
      ref false__
    let ((printInfix)(* whether to print implicit arguments *))
      = ref false__
    let ((printDepth)(* if implicit is ref true, whether to print infix ops when possible *))
      = ref (NONE : int option)
    let ((printLength)(* limit on term depth to print *)) =
      ref (NONE : int option)
    let ((noShadow)(* limit on number of arguments to print *))
      = ref false__
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
      let find (r::L) n = if r = l then n else find L (n + 1) in
      Int.toString (find (!lvars) 0)
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec nameOf = function | SOME id -> id | NONE -> "_"
    let rec fmtEVar (g, X) = Str0 (Symbol.evar (Names.evarName (g, X)))
    let rec fmtAVar (g, X) =
      Str0 (Symbol.evar ((Names.evarName (g, X)) ^ "_"))
    let rec isNil =
      function | I.Nil -> true__ | App _ -> false__ | SClo (S, _) -> isNil S
    let rec subToSpine (depth, s) =
      let sTS =
        function
        | (Shift k, S) ->
            if k < depth
            then sTS ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S)
            else S
        | (Dot (Idx k, s), S) ->
            sTS (s, (I.App ((I.Root ((I.BVar k), I.Nil)), S)))
        | (Dot (Exp (U), s), S) -> sTS (s, (I.App (U, S))) in
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
          let checkArgNumber =
            function
            | (I.Nil, 0) -> Exact S
            | (I.Nil, k) -> TooFew
            | ((App _ as S'), 0) -> TooMany (S, S')
            | (App (U, S'), k) -> checkArgNumber (S', (k - 1))
            | (SClo (S', s), k) -> sclo'' ((checkArgNumber (S', k)), s) in
          checkArgNumber (S, n)
      | (i, App (U, S), n) -> dropImp ((i - 1), S, n)
      | (i, SClo (S, s), n) -> sclo' ((dropImp (i, S, n)), s)
      | (i, I.Nil, n) -> TooFew
    let rec exceeded =
      function | (_, NONE) -> false__ | ((n : int), SOME (m : int)) -> n >= m
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
        ((FX.Infix (arrowPrec, FX.Right)), [F.Break; sym "->"; F.Space],
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
      F.HVbox
        (foldr
           (function
            | (id, fmt) -> ((::) (Str0 (Symbol.str id)) sym ".") :: fmt)
           [Str0 (f id)] ids)
    let rec parmDec =
      function | ((D)::L, 1) -> D | ((D)::L, j) -> parmDec (L, (j - 1))
    let rec parmName (cid, i) =
      let (Gsome, Gblock) = I.constBlock cid in
      match parmDec (Gblock, i) with
      | Dec (SOME pname, _) -> pname
      | Dec (NONE, _) -> Int.toString i
    let rec projName =
      function
      | (g, Proj (Bidx k, i)) ->
          let BDec (SOME bname, (cid, t)) = I.ctxLookup (g, k) in
          (^) (bname ^ "_") parmName (cid, i)
      | (g, Proj (LVar (r, _, (cid, t)), i)) -> (^) "_" parmName (cid, i)
      | (g, Proj (Inst iota, i)) -> "*"
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
          (::) (((::) ((cidToFmt cid) :: F.Break) F.String "|") :: F.Space)
            formatCids cids
    let rec formatWorlds (Worlds cids) =
      F.Hbox [F.String "("; F.HVbox (formatCids cids); F.String ")"]
    let rec worldsToString (W) = F.makestring_fmt (formatWorlds W)
    let rec fmtCon =
      function
      | (g, BVar n) -> Str0 (Symbol.bvar (Names.bvarName (g, n)))
      | (g, Const cid) -> fmtConstPath (Symbol.const, (constQid cid))
      | (g, Skonst cid) -> fmtConstPath (Symbol.skonst, (constQid cid))
      | (g, Def cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (g, NSDef cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (g, FVar (name, _, _)) -> Str0 (Symbol.fvar name)
      | (g, (Proj (Bidx k, i) as H)) -> Str0 (Symbol.const (projName (g, H)))
      | (g, (Proj (LVar ((ref (NONE) as r), sk, (cid, t)), i) as H)) ->
          let n = lookuplvar r in
          fmtConstPath
            ((function
              | l0 ->
                  Symbol.const
                    ((^) ((("#[" ^ l0) ^ n) ^ "]") projName (g, H))),
              (constQid cid))
      | (g, FgnConst (cs, conDec)) ->
          let name = I.conDecName conDec in
          (match ((Names.constLookup (Names.Qid (nil, name))), (!noShadow))
           with
           | (SOME _, false__) -> Str0 (Symbol.const (("%" ^ name) ^ "%"))
           | _ -> Str0 (Symbol.const name))
    let rec evarArgs (g, d, X, s) =
      OpArgs (FX.Nonfix, [fmtEVar (g, X)], (subToSpine ((I.ctxLength g), s)))
    let rec evarArgs' (g, d, X, s) =
      OpArgs (FX.Nonfix, [fmtAVar (g, X)], (subToSpine ((I.ctxLength g), s)))
    let rec fst =
      function
      | (App (u1, _), s) -> (u1, s)
      | (SClo (S, s'), s) -> fst (S, (I.comp (s', s)))
    let rec snd =
      function
      | (App (u1, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, (I.comp (s', s)))
    let rec elide l =
      match !printLength with | NONE -> false__ | SOME l' -> l > l'
    let ldots = sym "..."
    let rec addots l =
      match !printLength with | NONE -> false__ | SOME l' -> l = l'
    let rec parens ((fixity', fixity), fmt) =
      if FX.leq ((FX.prec fixity), (FX.prec fixity'))
      then F.Hbox [sym "("; fmt; sym ")"]
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
      | (fmt, Infix (_, FX.Left), accum) -> F.HVbox ([fmt] @ accum)
      | (fmt, Infix (_, FX.Right), accum) -> F.HVbox (accum @ [fmt])
      | (fmt, Prefix _, accum) -> F.HVbox (accum @ [fmt])
      | (fmt, Postfix _, accum) -> F.HVbox ([fmt] @ accum)
    let rec aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)
    let rec fmtUni = function | I.Type -> sym "type" | I.Kind -> sym "kind"
    let rec fmtExpW =
      function
      | (g, d, ctx, (Uni (L), s)) -> aa (ctx, (fmtUni L))
      | (g, d, ctx, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (g, D) in
               fmtLevel
                 ((I.Decl (g, D')), d, ctx,
                   ((braces (g, d, ((D', V2), s))), (I.dot1 s)))
           | I.Meta ->
               let D' = Names.decLUName (g, D) in
               fmtLevel
                 ((I.Decl (g, D')), d, ctx,
                   ((braces (g, d, ((D', V2), s))), (I.dot1 s)))
           | I.No ->
               fmtLevel
                 ((I.Decl (g, D)), d, ctx,
                   ((arrow ((I.EClo (V1, I.shift)), V2)), (I.dot1 s))))
      | (g, d, ctx, (Pi (((BDec _ as D), P), V2), s)) ->
          let D' = Names.decLUName (g, D) in
          fmtLevel
            ((I.Decl (g, D')), d, ctx,
              ((braces (g, d, ((D', V2), s))), (I.dot1 s)))
      | (g, d, ctx, (Pi (((ADec _ as D), P), V2), s)) ->
          let braces =
            OpArgs
              ((FX.Prefix binderPrec), [sym "["; sym "_"; sym "]"; F.Break],
                (IntSyn.App (V2, IntSyn.Nil))) in
          fmtLevel ((I.Decl (g, D)), d, ctx, (braces, (I.dot1 s)))
      | (g, d, ctx, ((Root (R) as U), s)) ->
          fmtOpArgs (g, d, ctx, (opargs (g, d, R)), s)
      | (g, d, ctx, (Lam (D, U), s)) ->
          let D' = Names.decLUName (g, D) in
          fmtLevel
            ((I.Decl (g, D')), d, ctx,
              ((brackets (g, d, ((D', U), s))), (I.dot1 s)))
      | (g, d, ctx, ((EVar _ as X), s)) ->
          if !implicit
          then aa (ctx, (F.HVbox ((::) (fmtEVar (g, X)) fmtSub (g, d, s))))
          else fmtOpArgs (g, d, ctx, (evarArgs (g, d, X, s)), I.id)
      | (g, d, ctx, ((AVar _ as X), s)) ->
          if !implicit
          then aa (ctx, (F.HVbox ((::) (fmtAVar (g, X)) fmtSub (g, d, s))))
          else fmtOpArgs (g, d, ctx, (evarArgs' (g, d, X, s)), I.id)
      | (g, d, ctx, ((FgnExp csfe as U), s)) ->
          fmtExp (g, d, ctx, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec opargsImplicit (g, d, (C, S)) =
      OpArgs (FX.Nonfix, [fmtCon (g, C)], S)
    let rec opargsImplicitInfix (g, d, ((C, S) as R)) =
      let fixity = fixityCon C in
      match fixity with
      | Infix _ -> opargsExplicit (g, d, R)
      | _ -> OpArgs (FX.Nonfix, [fmtCon (g, C)], S)
    let rec opargsExplicit (g, d, ((C, S) as R)) =
      let opFmt = fmtCon (g, C) in
      let fixity = fixityCon C in
      let oe =
        function
        | Exact (S') ->
            (match fixity with
             | FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], S')
             | Prefix _ -> OpArgs (fixity, [opFmt; F.Break], S')
             | Postfix _ -> OpArgs (fixity, [F.Break; opFmt], S')
             | Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.Space], S'))
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root R))
        | TooMany (S', S'') ->
            let opFmt' = fmtOpArgs (g, d, noCtxt, (oe (Exact S')), I.id) in
            OpArgs (FX.Nonfix, [F.Hbox [sym "("; opFmt'; sym ")"]], S'') in
      oe (dropImp ((impCon C), S, (argNumber fixity)))
    let rec opargs (g, d, R) =
      if !implicit
      then
        (if !printInfix
         then opargsImplicitInfix (g, d, R)
         else opargsImplicit (g, d, R))
      else opargsExplicit (g, d, R)
    let rec fmtOpArgs =
      function
      | (g, d, ctx, (OpArgs (_, opFmts, S') as oa), s) ->
          if isNil S'
          then aa (ctx, (List.hd opFmts))
          else fmtLevel (g, d, ctx, (oa, s))
      | (g, d, ctx, EtaLong (U'), s) -> fmtExpW (g, d, ctx, (U', s))
    let rec fmtSub (g, d, s) = (::) (Str "[") fmtSub' (g, d, 0, s)
    let rec fmtSub' (g, d, l, s) =
      if elide l then [ldots] else fmtSub'' (g, d, l, s)
    let rec fmtSub'' =
      function
      | (g, d, l, Shift k) -> [Str ((^) "^" Int.toString k); Str "]"]
      | (g, d, l, Dot (Idx k, s)) ->
          (::) (((::) (Str (Names.bvarName (g, k))) Str ".") :: F.Break)
            fmtSub' (g, d, (l + 1), s)
      | (g, d, l, Dot (Exp (U), s)) ->
          (::) (((::) (fmtExp (g, (d + 1), noCtxt, (U, I.id))) Str ".") ::
                  F.Break)
            fmtSub' (g, d, (l + 1), s)
    let rec fmtExp (g, d, ctx, (U, s)) =
      if exceeded (d, (!printDepth))
      then sym "%%"
      else fmtExpW (g, d, ctx, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (g, d, l, (I.Nil, _)) -> []
      | (g, d, l, (SClo (S, s'), s)) ->
          fmtSpine (g, d, l, (S, (I.comp (s', s))))
      | (g, d, l, (App (U, S), s)) ->
          if elide l
          then []
          else
            if addots l
            then [ldots]
            else
              (::) (fmtExp (g, (d + 1), appCtxt, (U, s))) fmtSpine'
                (g, d, l, (S, s))
    let rec fmtSpine' =
      function
      | (g, d, l, (I.Nil, _)) -> []
      | (g, d, l, (SClo (S, s'), s)) ->
          fmtSpine' (g, d, l, (S, (I.comp (s', s))))
      | (g, d, l, (S, s)) -> (::) F.Break fmtSpine (g, d, (l + 1), (S, s))
    let rec fmtLevel =
      function
      | (g, d, Ctxt (fixity', accum, l),
         (OpArgs ((FX.Nonfix as fixity), fmts, S), s)) ->
          let atm = fmtSpine (g, d, 0, (S, s)) in
          addAccum
            ((parens
                ((fixity', fixity), (F.HVbox ((fmts @ [F.Break]) @ atm)))),
              fixity', accum)
      | (g, d, Ctxt (fixity', accum, l),
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
                     (g, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                       (snd (S, s)))] in
          if accMore
          then
            fmtExp
              (g, d, (Ctxt (fixity, (rhs @ accum), (l + 1))), (fst (S, s)))
          else
            (let both = fmtExp (g, d, (Ctxt (fixity, rhs, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (g, d, Ctxt (fixity', accum, l),
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
                   (g, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                     (fst (S, s)))]
                  @ fmts in
          if accMore
          then
            fmtExp
              (g, d, (Ctxt (fixity, (accum @ lhs), (l + 1))), (snd (S, s)))
          else
            (let both = fmtExp (g, d, (Ctxt (fixity, lhs, 0)), (snd (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (_, FX.None) as fixity), fmts, S), s)) ->
          let lhs =
            fmtExp (g, (d + 1), (Ctxt (fixity, nil, 0)), (fst (S, s))) in
          let rhs =
            fmtExp (g, (d + 1), (Ctxt (fixity, nil, 0)), (snd (S, s))) in
          addAccum
            ((parens ((fixity', fixity), (F.HVbox (([lhs] @ fmts) @ [rhs])))),
              fixity', accum)
      | (g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Prefix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [ldots; F.Break] else fmts in
          if accMore
          then
            fmtExp
              (g, d, (Ctxt (fixity, (accum @ pfx), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (g, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
      | (g, d, Ctxt (fixity', accum, l),
         (OpArgs ((Postfix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [F.Break; ldots] else fmts in
          if accMore
          then
            fmtExp
              (g, d, (Ctxt (fixity, (pfx @ accum), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (g, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
    let rec braces (g, d, ((D, V), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "{"; fmtDec (g, d, (D, s)); sym "}"; F.Break],
          (IntSyn.App (V, IntSyn.Nil)))
    let rec brackets (g, d, ((D, U), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "["; fmtDec (g, d, (D, s)); sym "]"; F.Break],
          (IntSyn.App (U, IntSyn.Nil)))
    let rec fmtDec =
      function
      | (g, d, (Dec (x, V), s)) ->
          F.HVbox
            [Str0 (Symbol.bvar (nameOf x));
            sym ":";
            fmtExp (g, (d + 1), noCtxt, (V, s))]
      | (g, d, (BDec (x, (cid, t)), s)) ->
          let (Gsome, Gblock) = I.constBlock cid in
          F.HVbox
            ((@) [Str0 (Symbol.const (nameOf x)); sym ":"] fmtDecList'
               (g, (Gblock, (I.comp (t, s)))))
      | (g, d, (ADec (x, _), s)) ->
          F.HVbox [Str0 (Symbol.bvar (nameOf x)); sym ":_"]
      | (g, d, (NDec (SOME name), s)) -> F.HVbox [sym name]
    let rec fmtDecList' =
      function
      | (G0, (nil, s)) -> nil
      | (G0, ((D)::nil, s)) ->
          ((::) ((::) (sym "{") fmtDec (G0, 0, (D, s))) sym "}") :: nil
      | (G0, ((D)::L, s)) ->
          (::) (((::) ((::) (sym "{") fmtDec (G0, 0, (D, s))) sym "}") ::
                  F.Break)
            fmtDecList' ((I.Decl (G0, D)), (L, (I.dot1 s)))
    let rec skipI =
      function
      | (0, g, V) -> (g, V)
      | (i, g, Pi ((D, _), V)) ->
          skipI ((i - 1), (I.Decl (g, (Names.decEName (g, D)))), V)
    let rec skipI2 =
      function
      | (0, g, V, U) -> (g, V, U)
      | (i, g, Pi ((D, _), V), Lam (D', U)) ->
          skipI2 ((i - 1), (I.Decl (g, (Names.decEName (g, D')))), V, U)
    let rec ctxToDecList =
      function
      | (I.Null, L) -> L
      | (Decl (g, D), L) -> ctxToDecList (g, (D :: L))
    let rec fmtDecList =
      function
      | (G0, nil) -> nil
      | (G0, (D)::nil) ->
          ((::) ((::) (sym "{") fmtDec (G0, 0, (D, I.id))) sym "}") :: nil
      | (G0, (D)::L) ->
          (::) (((::) ((::) (sym "{") fmtDec (G0, 0, (D, I.id))) sym "}") ::
                  F.Break)
            fmtDecList ((I.Decl (G0, D)), L)
    let rec fmtCtx (G0, g) = fmtDecList (G0, (ctxToDecList (g, nil)))
    let rec fmtBlock =
      function
      | (I.Null, Lblock) ->
          [sym "block"; F.Break] @ (fmtDecList (I.Null, Lblock))
      | (Gsome, Lblock) ->
          [F.HVbox ([sym "some"; F.Space] @ (fmtCtx (I.Null, Gsome)));
          F.Break;
          F.HVbox ([sym "block"; F.Space] @ (fmtDecList (Gsome, Lblock)))]
    let rec fmtConDec =
      function
      | (hide, (ConDec (_, _, imp, _, V, L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (g, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in
          let Vfmt = fmtExp (g, 0, noCtxt, (V, I.id)) in
          F.HVbox
            [fmtConstPath (Symbol.const, qid);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | (hide, (SkoDec (_, _, imp, V, L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (g, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in
          let Vfmt = fmtExp (g, 0, noCtxt, (V, I.id)) in
          F.HVbox
            [sym "%skolem";
            F.Break;
            fmtConstPath (Symbol.skonst, qid);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | (hide, (BlockDec (_, _, Gsome, Lblock) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.HVbox
            (([sym "%block";
              F.Break;
              fmtConstPath (Symbol.label, qid);
              F.Space;
              sym ":";
              F.Break] @ (fmtBlock (Gsome, Lblock))) @ [sym "."])
      | (hide, (BlockDef (_, _, W) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.HVbox
            ([sym "%block";
             F.Break;
             fmtConstPath (Symbol.label, qid);
             F.Space;
             sym "=";
             F.Break] @ ((formatWorlds (T.Worlds W)) :: [sym "."]))
      | (hide, (ConDef (_, _, imp, U, V, L, _) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (g, V, U) =
            if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in
          let Vfmt = fmtExp (g, 0, noCtxt, (V, I.id)) in
          let Ufmt = fmtExp (g, 0, noCtxt, (U, I.id)) in
          F.HVbox
            [fmtConstPath (Symbol.def, qid);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            F.Break;
            sym "=";
            F.Space;
            Ufmt;
            sym "."]
      | (hide, (AbbrevDef (_, _, imp, U, V, L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (g, V, U) =
            if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in
          let Vfmt = fmtExp (g, 0, noCtxt, (V, I.id)) in
          let Ufmt = fmtExp (g, 0, noCtxt, (U, I.id)) in
          F.HVbox
            [fmtConstPath (Symbol.def, qid);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            F.Break;
            sym "=";
            F.Space;
            Ufmt;
            sym "."]
    let rec fmtCnstr =
      function
      | I.Solved -> [Str "Solved Constraint"]
      | Eqn (g, u1, u2) ->
          let g' = Names.ctxLUName g in
          [F.HVbox
             [fmtExp (g', 0, noCtxt, (u1, I.id));
             F.Break;
             sym "=";
             F.Space;
             fmtExp (g', 0, noCtxt, (u2, I.id))]]
      | FgnCnstr ((cs, _) as csfc) ->
          let fmtExpL =
            function
            | nil -> [Str "Empty Constraint"]
            | (g, U)::nil ->
                [fmtExp ((Names.ctxLUName g), 0, noCtxt, (U, I.id))]
            | (g, U)::expL ->
                (@) [fmtExp ((Names.ctxLUName g), 0, noCtxt, (U, I.id));
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
      | (I.Null, U) -> U
      | (Decl (g, D), U) -> abstractLam (g, (I.Lam (D, U)))
    let rec fmtNamedEVar =
      function
      | ((EVar (_, g, _, _) as U), name) ->
          let U' = abstractLam (g, U) in
          F.HVbox
            [Str0 (Symbol.evar name);
            F.Space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (U', I.id))]
      | (U, name) ->
          F.HVbox
            [Str0 (Symbol.evar name);
            F.Space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (U, I.id))]
    let rec fmtEVarInst =
      function
      | nil -> [Str "Empty Substitution"]
      | (U, name)::nil -> [fmtNamedEVar (U, name)]
      | (U, name)::Xs ->
          (::) (((::) (fmtNamedEVar (U, name)) Str ";") :: F.Break)
            fmtEVarInst Xs
    let rec collectEVars =
      function
      | (nil, Xs) -> Xs
      | ((U, _)::Xnames, Xs) ->
          collectEVars
            (Xnames, (Abstract.collectEVars (I.Null, (U, I.id), Xs)))
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
      | (EVar (ref (NONE), _, _, cnstrs))::Xs ->
          mergeConstraints
            ((Constraints.simplify (!cnstrs)), (collectConstraints Xs))
      | _::Xs -> collectConstraints Xs
    let rec formatDec
      (((g)(* if true, don't print shadowed constants as "%const%" *)
       (* Shorthands *)(* Disambiguation of block logic variable names *)
       (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
       (* fmtEVar (g, X) = "X", the name of the EVar X *)
       (* Effect: Names.evarName will assign a name if X does not yet have one *)
       (* should probably be a new Symbol constructor for AVars -kw *)
       (* isNil S = true iff S == Nil *)(* subToSpine (depth, s) = S
     Invariants:
     If  g |- s : g', Gd  with  |Gd| = depth
     then g |- S : {{Gd}} C > C  for any C

     This is used to print
      g |- Xl[s] : A[s]  for  g', Gd |- Xl : A
     as
      g |- Xr @ S : A[s]  for  g' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)
       (* k >= depth *)(* Eta violation, but probably inconsequential -kw *)
       (* ArgStatus classifies the number of arguments to an operator *)
       (* dropImp (i, S, n) for n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = s0 @ S'' and |s0| = n
  *)
       (* n >= 1 *)(* exceeded (n:int, b:bound) = true if n exceeds bound b *)
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

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)
       (* empty left context *)(* braces and brackets as a prefix operator *)
       (* colon is of FX.minPrec-2, but doesn't occur in printing *)
       (* arrow as infix operator *)(* juxtaposition as infix operator *)
       (* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)
       (* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)
       (* fixityCon (c) = fixity of c *)(* BVar, FVar *)
       (* impCon (c) = number of implicit arguments to c *)
       (* BVar, FVar *)(* argNumber (fixity) = number of required arguments to head with fixity *)
       (* FIX: this is certainly not correct -kw *)(* names should have been assigned by invar
         iant, NONE imppossible *)
       (* note: this obscures LVar identity! *)(* no longer Tue Mar  1 13:32:21 2011 -cs *)
       (* to be fixed --cs *)(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
       (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
       (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
       (* the user has re-defined this name *)(* evarArgs (g, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
       (* fst (S, s) = u1, the first argument in S[s] *)
       (* snd (S, s) = u2, the second argument in S[s] *)
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
       (* Infix(_,None) should never be asked *)(* Nonfix should never be asked *)
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
       (* fmtUni (L) = "L" *)(* impossible, included for robustness *)
       (* fmtExpW (g, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       g is a "printing context" (names in it are unique, but
            types may be incorrect) approximating g'
       g'' |- U : V   g' |- s : g''  (so  g' |- U[s] : V[s])
       (U,s) in whnf
  *)
       (* if Pi is dependent but anonymous, invent name here *)(* could sometimes be EName *)
       (* I.decSub (D', s) *)(* I.decSub (D', s) *)
       (* I.decSub (D, s) *)(* -bp *)
       (*      val D' = Names.decLUName (g, D) *)(* s = id *)
       (* I.Redex not possible *)(* I.decSub (D', s) *)
       (* assume dereferenced during whnf *)(* assume dereferenced during whnf *)
       (* I.EClo not possible for Whnf *)(* for internal printing *)
       (* opargsImplicit (g, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
       (* for flit printing -jcreed 6/2005 *)(* opargsImplicit (g, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix declarations are obeyed. It is an
     error to call this function if an infix declaration has been made for
     a term which has more than two arguments. (This could have happened if the term
     had two explicit arguments and further implicit arguments)

     In other words, it is an error if an infix declaration had any
     implicit arguments.
  *)
       (* Can't have implicit arguments by invariant *)
       (* for external printing *)(* opargsExplicit (g, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     g |- C @ S (no substitution involved)
  *)
       (* extra arguments to infix operator *)(* S' - all non-implicit arguments *)
       (* S'' - extra arguments *)(* parens because juxtaposition has highest precedence *)
       (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
       (* opargs (g, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
       (* fmtOpArgs (g, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     g is a printing context approximating g', and g' |- oa[s] is valid.
  *)
       (* opFmts = [fmtCon(g,C)] *)(* fmtSub (g, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
       (* fmtExp (g, d, ctx, (U, s)) = fmt
     format or elide U[s] at printing depth d and add to the left context ctx.

     g is a printing context approximation g' and g' |- U[s] is valid.
  *)
       (* fmtSpine (g, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context g which approximates g', where g' |- S[s] is valid
  *)
       (* necessary? *)(* fmtSpine' (g, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading "Break" and increment printing length
  *)
       (* fmtLevel (g, d, ctx, (oa, s)) = fmt

     format operator/arguments form oa[s] at printing depth d and add the result
     to the left context ctx.

     This is the main function flattening out infix/prefix/postfix operator
     sequences.  It compares the fixity of the operator of the current left
     context with the operator at the head of the current operator/arguments
     form and decides how to extend the accumulator and whether to insert
     parentheses.
  *)
       (* atm must not be empty, otherwise bug below *)
       (* F.HVbox doesn't work if last item of HVbox is F.Break *)
       (* possible improvement along the following lines: *)
       (*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *)
       (* braces (g, d, ((D, V), s)) = oa
     convert declaration D[s] as a prefix pi-abstraction into operator/arguments
     form with prefix "{D}" and argument V at printing depth d in printing
     context g approximating g'.

     Invariants:
      g' |- D[s] decl
      g' |- V : L  [NOTE: s does not apply to V!]
  *)
       (* brackets (g, d, ((D, U), s)) = oa
     convert declaration D[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix "[D]" and argument U at printing depth d in printing
     context g approximating g'.

     Invariants:
      g' |- D[s] decl
      g' |- U : V  [NOTE: s does not apply to U!]
  *)
       (* fmtDec (g, d, (D, s)) = fmt
     format declaration D[s] at printing depth d in printing context g approximating g'.

     Invariants:
      g' |- D[s] decl
  *)
       (* alternative with more whitespace *)(* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (g, d+1, noCtxt, (V,s))]
      *)
       (* alternative with more whitespace *)(* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (g, d+1, noCtxt, (V,s))]
      *)
       (* Assume unique names are already assigned in G0 and g! *)
       (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
       (* reset variable names in between to align names of type V and definition U *)
       (* val _ = Names.varReset () *)(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*)
       (* reset variable names in between to align names of type V and definition U *)
       (* val _ = Names.varReset () *)(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
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
       (* In the functions below, g must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)),
       D)
      = fmtDec (g, 0, (D, I.id))
    let rec formatDecList (g, D) = F.HVbox (fmtDecList (g, D))
    let rec formatDecList' (g, (D, s)) = F.HVbox (fmtDecList' (g, (D, s)))
    let rec formatExp (g, U) = fmtExp (g, 0, noCtxt, (U, I.id))
    let rec formatSpine (g, S) = fmtSpine (g, 0, 0, (S, I.id))
    let rec formatConDec condec = fmtConDec (false__, condec)
    let rec formatConDecI condec = fmtConDec (true__, condec)
    let rec formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
    let rec formatCnstrs cnstrL = F.Vbox0 0 1 (fmtCnstrL cnstrL)
    let rec formatCtx (G0, g) = F.HVbox (fmtCtx (G0, g))
    let rec decToString
      (((g)(* assumes G0 and g are named *)), D) =
      F.makestring_fmt (formatDec (g, D))
    let rec expToString (g, U) = F.makestring_fmt (formatExp (g, U))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
    let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
    let rec ctxToString (G0, g) = F.makestring_fmt (formatCtx (G0, g))
    let rec evarInstToString (Xnames) =
      F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
    let rec evarCnstrsToStringOpt (Xnames) =
      let Ys = collectEVars (Xnames, nil) in
      let ((cnstrL)(* collect EVars in instantiations *)) =
        collectConstraints Ys in
      match cnstrL with | nil -> NONE | _ -> SOME (cnstrsToString cnstrL)
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
module Print =
  (Make_Print)(struct
                 module Whnf =
                   ((Whnf)(*
structure WorldPrint = WorldPrint 
  (structure Global = Global
   ! structure IntSyn = IntSyn !*)
                   (*! structure Tomega' = Tomega !*)
                   (*! structure IntSyn' = IntSyn !*))
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolAscii
               end)
module ClausePrint =
  (Make_ClausePrint)(struct
                       module Whnf =
                         ((Whnf)(*! structure IntSyn' = IntSyn !*))
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = Print
                       module Symbol = SymbolAscii
                     end)
module PrintTeX =
  (Make_Print)(struct
                 module Whnf =
                   ((Whnf)(*! structure IntSyn' = IntSyn !*))
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolTeX
               end)
module ClausePrintTeX =
  (Make_ClausePrint)(struct
                       module Whnf =
                         ((Whnf)(*! structure IntSyn' = IntSyn !*))
                       module Constraints = Constraints
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = PrintTeX
                       module Symbol = SymbolTeX
                     end)
module PrintTwega =
  (Make_PrintTwega)(struct
                      module Whnf =
                        ((Whnf)(*! structure IntSyn' = IntSyn !*))
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end)
module PrintXML =
  (Make_PrintXML)(struct
                    module Whnf =
                      ((Whnf)(*! structure IntSyn' = IntSyn !*))
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Names = Names
                    module Formatter' = Formatter
                  end)
module PrintOMDoc =
  (Make_PrintOMDoc)(struct
                      module Whnf =
                        ((Whnf)(*! structure IntSyn' = IntSyn !*))
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end);;
