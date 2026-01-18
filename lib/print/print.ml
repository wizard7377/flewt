
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
    let printDepth = ref (NONE : int option)
    (* limit on term depth to print *)
    let printLength = ref (NONE : int option)
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
      let rec find (r::L) n = if r = l then n else find L (n + 1) in
      Int.toString (find (!lvars) 0)
    let Str = F.String
    let rec Str0 (s, n) = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec nameOf = function | SOME id -> id | NONE -> "_"
    let rec fmtEVar (G, X) = Str0 (Symbol.evar (Names.evarName (G, X)))
    let rec fmtAVar (G, X) =
      Str0 (Symbol.evar ((Names.evarName (G, X)) ^ "_"))
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
          let rec checkArgNumber =
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
      | (G, Proj (Bidx k, i)) ->
          let BDec (SOME bname, (cid, t)) = I.ctxLookup (G, k) in
          (^) (bname ^ "_") parmName (cid, i)
      | (G, Proj (LVar (r, _, (cid, t)), i)) -> (^) "_" parmName (cid, i)
      | (G, Proj (Inst iota, i)) -> "*"
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
      | (G, BVar n) -> Str0 (Symbol.bvar (Names.bvarName (G, n)))
      | (G, Const cid) -> fmtConstPath (Symbol.const, (constQid cid))
      | (G, Skonst cid) -> fmtConstPath (Symbol.skonst, (constQid cid))
      | (G, Def cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (G, NSDef cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (G, FVar (name, _, _)) -> Str0 (Symbol.fvar name)
      | (G, (Proj (Bidx k, i) as H)) -> Str0 (Symbol.const (projName (G, H)))
      | (G, (Proj (LVar ((ref (NONE) as r), sk, (cid, t)), i) as H)) ->
          let n = lookuplvar r in
          fmtConstPath
            ((function
              | l0 ->
                  Symbol.const
                    ((^) ((("#[" ^ l0) ^ n) ^ "]") projName (G, H))),
              (constQid cid))
      | (G, FgnConst (cs, conDec)) ->
          let name = I.conDecName conDec in
          (match ((Names.constLookup (Names.Qid (nil, name))), (!noShadow))
           with
           | (SOME _, false__) -> Str0 (Symbol.const (("%" ^ name) ^ "%"))
           | _ -> Str0 (Symbol.const name))
    let rec evarArgs (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtEVar (G, X)], (subToSpine ((I.ctxLength G), s)))
    let rec evarArgs' (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtAVar (G, X)], (subToSpine ((I.ctxLength G), s)))
    let rec fst =
      function
      | (App (U1, _), s) -> (U1, s)
      | (SClo (S, s'), s) -> fst (S, (I.comp (s', s)))
    let rec snd =
      function
      | (App (U1, S), s) -> fst (S, s)
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
      | (G, d, ctx, (Uni (L), s)) -> aa (ctx, (fmtUni L))
      | (G, d, ctx, (Pi (((Dec (_, V1) as D), P), V2), s)) ->
          (match P with
           | I.Maybe ->
               let D' = Names.decLUName (G, D) in
               fmtLevel
                 ((I.Decl (G, D')), d, ctx,
                   ((braces (G, d, ((D', V2), s))), (I.dot1 s)))
           | I.Meta ->
               let D' = Names.decLUName (G, D) in
               fmtLevel
                 ((I.Decl (G, D')), d, ctx,
                   ((braces (G, d, ((D', V2), s))), (I.dot1 s)))
           | I.No ->
               fmtLevel
                 ((I.Decl (G, D)), d, ctx,
                   ((arrow ((I.EClo (V1, I.shift)), V2)), (I.dot1 s))))
      | (G, d, ctx, (Pi (((BDec _ as D), P), V2), s)) ->
          let D' = Names.decLUName (G, D) in
          fmtLevel
            ((I.Decl (G, D')), d, ctx,
              ((braces (G, d, ((D', V2), s))), (I.dot1 s)))
      | (G, d, ctx, (Pi (((ADec _ as D), P), V2), s)) ->
          let braces =
            OpArgs
              ((FX.Prefix binderPrec), [sym "["; sym "_"; sym "]"; F.Break],
                (IntSyn.App (V2, IntSyn.Nil))) in
          fmtLevel ((I.Decl (G, D)), d, ctx, (braces, (I.dot1 s)))
      | (G, d, ctx, ((Root (R) as U), s)) ->
          fmtOpArgs (G, d, ctx, (opargs (G, d, R)), s)
      | (G, d, ctx, (Lam (D, U), s)) ->
          let D' = Names.decLUName (G, D) in
          fmtLevel
            ((I.Decl (G, D')), d, ctx,
              ((brackets (G, d, ((D', U), s))), (I.dot1 s)))
      | (G, d, ctx, ((EVar _ as X), s)) ->
          if !implicit
          then aa (ctx, (F.HVbox ((::) (fmtEVar (G, X)) fmtSub (G, d, s))))
          else fmtOpArgs (G, d, ctx, (evarArgs (G, d, X, s)), I.id)
      | (G, d, ctx, ((AVar _ as X), s)) ->
          if !implicit
          then aa (ctx, (F.HVbox ((::) (fmtAVar (G, X)) fmtSub (G, d, s))))
          else fmtOpArgs (G, d, ctx, (evarArgs' (G, d, X, s)), I.id)
      | (G, d, ctx, ((FgnExp csfe as U), s)) ->
          fmtExp (G, d, ctx, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
    let rec opargsImplicit (G, d, (C, S)) =
      OpArgs (FX.Nonfix, [fmtCon (G, C)], S)
    let rec opargsImplicitInfix (G, d, ((C, S) as R)) =
      let fixity = fixityCon C in
      match fixity with
      | Infix _ -> opargsExplicit (G, d, R)
      | _ -> OpArgs (FX.Nonfix, [fmtCon (G, C)], S)
    let rec opargsExplicit (G, d, ((C, S) as R)) =
      let opFmt = fmtCon (G, C) in
      let fixity = fixityCon C in
      let rec oe =
        function
        | Exact (S') ->
            (match fixity with
             | FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], S')
             | Prefix _ -> OpArgs (fixity, [opFmt; F.Break], S')
             | Postfix _ -> OpArgs (fixity, [F.Break; opFmt], S')
             | Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.Space], S'))
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root R))
        | TooMany (S', S'') ->
            let opFmt' = fmtOpArgs (G, d, noCtxt, (oe (Exact S')), I.id) in
            OpArgs (FX.Nonfix, [F.Hbox [sym "("; opFmt'; sym ")"]], S'') in
      oe (dropImp ((impCon C), S, (argNumber fixity)))
    let rec opargs (G, d, R) =
      if !implicit
      then
        (if !printInfix
         then opargsImplicitInfix (G, d, R)
         else opargsImplicit (G, d, R))
      else opargsExplicit (G, d, R)
    let rec fmtOpArgs =
      function
      | (G, d, ctx, (OpArgs (_, opFmts, S') as oa), s) ->
          if isNil S'
          then aa (ctx, (List.hd opFmts))
          else fmtLevel (G, d, ctx, (oa, s))
      | (G, d, ctx, EtaLong (U'), s) -> fmtExpW (G, d, ctx, (U', s))
    let rec fmtSub (G, d, s) = (::) (Str "[") fmtSub' (G, d, 0, s)
    let rec fmtSub' (G, d, l, s) =
      if elide l then [ldots] else fmtSub'' (G, d, l, s)
    let rec fmtSub'' =
      function
      | (G, d, l, Shift k) -> [Str ((^) "^" Int.toString k); Str "]"]
      | (G, d, l, Dot (Idx k, s)) ->
          (::) (((::) (Str (Names.bvarName (G, k))) Str ".") :: F.Break)
            fmtSub' (G, d, (l + 1), s)
      | (G, d, l, Dot (Exp (U), s)) ->
          (::) (((::) (fmtExp (G, (d + 1), noCtxt, (U, I.id))) Str ".") ::
                  F.Break)
            fmtSub' (G, d, (l + 1), s)
    let rec fmtExp (G, d, ctx, (U, s)) =
      if exceeded (d, (!printDepth))
      then sym "%%"
      else fmtExpW (G, d, ctx, (Whnf.whnf (U, s)))
    let rec fmtSpine =
      function
      | (G, d, l, (I.Nil, _)) -> []
      | (G, d, l, (SClo (S, s'), s)) ->
          fmtSpine (G, d, l, (S, (I.comp (s', s))))
      | (G, d, l, (App (U, S), s)) ->
          if elide l
          then []
          else
            if addots l
            then [ldots]
            else
              (::) (fmtExp (G, (d + 1), appCtxt, (U, s))) fmtSpine'
                (G, d, l, (S, s))
    let rec fmtSpine' =
      function
      | (G, d, l, (I.Nil, _)) -> []
      | (G, d, l, (SClo (S, s'), s)) ->
          fmtSpine' (G, d, l, (S, (I.comp (s', s))))
      | (G, d, l, (S, s)) -> (::) F.Break fmtSpine (G, d, (l + 1), (S, s))
    let rec fmtLevel =
      function
      | (G, d, Ctxt (fixity', accum, l),
         (OpArgs ((FX.Nonfix as fixity), fmts, S), s)) ->
          let atm = fmtSpine (G, d, 0, (S, s)) in
          addAccum
            ((parens
                ((fixity', fixity), (F.HVbox ((fmts @ [F.Break]) @ atm)))),
              fixity', accum)
      | (G, d, Ctxt (fixity', accum, l),
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
                     (G, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                       (snd (S, s)))] in
          if accMore
          then
            fmtExp
              (G, d, (Ctxt (fixity, (rhs @ accum), (l + 1))), (fst (S, s)))
          else
            (let both = fmtExp (G, d, (Ctxt (fixity, rhs, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (G, d, Ctxt (fixity', accum, l),
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
                   (G, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                     (fst (S, s)))]
                  @ fmts in
          if accMore
          then
            fmtExp
              (G, d, (Ctxt (fixity, (accum @ lhs), (l + 1))), (snd (S, s)))
          else
            (let both = fmtExp (G, d, (Ctxt (fixity, lhs, 0)), (snd (S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (_, FX.None) as fixity), fmts, S), s)) ->
          let lhs =
            fmtExp (G, (d + 1), (Ctxt (fixity, nil, 0)), (fst (S, s))) in
          let rhs =
            fmtExp (G, (d + 1), (Ctxt (fixity, nil, 0)), (snd (S, s))) in
          addAccum
            ((parens ((fixity', fixity), (F.HVbox (([lhs] @ fmts) @ [rhs])))),
              fixity', accum)
      | (G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Prefix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [ldots; F.Break] else fmts in
          if accMore
          then
            fmtExp
              (G, d, (Ctxt (fixity, (accum @ pfx), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (G, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
      | (G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Postfix _ as fixity), fmts, S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [F.Break; ldots] else fmts in
          if accMore
          then
            fmtExp
              (G, d, (Ctxt (fixity, (pfx @ accum), (l + 1))), (fst (S, s)))
          else
            (let whole = fmtExp (G, d, (Ctxt (fixity, pfx, 0)), (fst (S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
    let rec braces (G, d, ((D, V), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "{"; fmtDec (G, d, (D, s)); sym "}"; F.Break],
          (IntSyn.App (V, IntSyn.Nil)))
    let rec brackets (G, d, ((D, U), s)) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "["; fmtDec (G, d, (D, s)); sym "]"; F.Break],
          (IntSyn.App (U, IntSyn.Nil)))
    let rec fmtDec =
      function
      | (G, d, (Dec (x, V), s)) ->
          F.HVbox
            [Str0 (Symbol.bvar (nameOf x));
            sym ":";
            fmtExp (G, (d + 1), noCtxt, (V, s))]
      | (G, d, (BDec (x, (cid, t)), s)) ->
          let (Gsome, Gblock) = I.constBlock cid in
          F.HVbox
            ((@) [Str0 (Symbol.const (nameOf x)); sym ":"] fmtDecList'
               (G, (Gblock, (I.comp (t, s)))))
      | (G, d, (ADec (x, _), s)) ->
          F.HVbox [Str0 (Symbol.bvar (nameOf x)); sym ":_"]
      | (G, d, (NDec (SOME name), s)) -> F.HVbox [sym name]
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
      | (0, G, V) -> (G, V)
      | (i, G, Pi ((D, _), V)) ->
          skipI ((i - 1), (I.Decl (G, (Names.decEName (G, D)))), V)
    let rec skipI2 =
      function
      | (0, G, V, U) -> (G, V, U)
      | (i, G, Pi ((D, _), V), Lam (D', U)) ->
          skipI2 ((i - 1), (I.Decl (G, (Names.decEName (G, D')))), V, U)
    let rec ctxToDecList =
      function
      | (I.Null, L) -> L
      | (Decl (G, D), L) -> ctxToDecList (G, (D :: L))
    let rec fmtDecList =
      function
      | (G0, nil) -> nil
      | (G0, (D)::nil) ->
          ((::) ((::) (sym "{") fmtDec (G0, 0, (D, I.id))) sym "}") :: nil
      | (G0, (D)::L) ->
          (::) (((::) ((::) (sym "{") fmtDec (G0, 0, (D, I.id))) sym "}") ::
                  F.Break)
            fmtDecList ((I.Decl (G0, D)), L)
    let rec fmtCtx (G0, G) = fmtDecList (G0, (ctxToDecList (G, nil)))
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
          let (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in
          let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in
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
          let (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in
          let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in
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
          let (G, V, U) =
            if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in
          let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in
          let Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) in
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
          let (G, V, U) =
            if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in
          let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in
          let Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) in
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
      | Eqn (G, U1, U2) ->
          let G' = Names.ctxLUName G in
          [F.HVbox
             [fmtExp (G', 0, noCtxt, (U1, I.id));
             F.Break;
             sym "=";
             F.Space;
             fmtExp (G', 0, noCtxt, (U2, I.id))]]
      | FgnCnstr ((cs, _) as csfc) ->
          let rec fmtExpL =
            function
            | nil -> [Str "Empty Constraint"]
            | (G, U)::nil ->
                [fmtExp ((Names.ctxLUName G), 0, noCtxt, (U, I.id))]
            | (G, U)::expL ->
                (@) [fmtExp ((Names.ctxLUName G), 0, noCtxt, (U, I.id));
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
      | (Decl (G, D), U) -> abstractLam (G, (I.Lam (D, U)))
    let rec fmtNamedEVar =
      function
      | ((EVar (_, G, _, _) as U), name) ->
          let U' = abstractLam (G, U) in
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
    (* Disambiguation of block logic variable names *)
    (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
    (* fmtEVar (G, X) = "X", the name of the EVar X *)
    (* Effect: Names.evarName will assign a name if X does not yet have one *)
    (* should probably be a new Symbol constructor for AVars -kw *)
    (* isNil S = true iff S == Nil *)
    (* subToSpine (depth, s) = S
     Invariants:
     If  G |- s : G', Gd  with  |Gd| = depth
     then G |- S : {{Gd}} C > C  for any C

     This is used to print
      G |- Xl[s] : A[s]  for  G', Gd |- Xl : A
     as
      G |- Xr @ S : A[s]  for  G' |- Xr : {{Gd}} A
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

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
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
         iant, NONE imppossible *)
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
    (* evarArgs (G, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
    (* fst (S, s) = U1, the first argument in S[s] *)
    (* snd (S, s) = U2, the second argument in S[s] *)
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
    (* fmtUni (L) = "L" *)
    (* impossible, included for robustness *)
    (* fmtExpW (G, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
    (* if Pi is dependent but anonymous, invent name here *)
    (* could sometimes be EName *)
    (* I.decSub (D', s) *)
    (* I.decSub (D', s) *)
    (* I.decSub (D, s) *)
    (* -bp *)
    (*      val D' = Names.decLUName (G, D) *)
    (* s = id *)
    (* I.Redex not possible *)
    (* I.decSub (D', s) *)
    (* assume dereferenced during whnf *)
    (* assume dereferenced during whnf *)
    (* I.EClo not possible for Whnf *)
    (* for internal printing *)
    (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
    (* for flit printing -jcreed 6/2005 *)
    (* opargsImplicit (G, (C, S)) = oa
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
    (* opargsExplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     G |- C @ S (no substitution involved)
  *)
    (* extra arguments to infix operator *)
    (* S' - all non-implicit arguments *)
    (* S'' - extra arguments *)
    (* parens because juxtaposition has highest precedence *)
    (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
    (* opargs (G, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
    (* fmtOpArgs (G, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     G is a printing context approximating G', and G' |- oa[s] is valid.
  *)
    (* opFmts = [fmtCon(G,C)] *)
    (* fmtSub (G, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
    (* fmtExp (G, d, ctx, (U, s)) = fmt
     format or elide U[s] at printing depth d and add to the left context ctx.

     G is a printing context approximation G' and G' |- U[s] is valid.
  *)
    (* fmtSpine (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
    (* necessary? *)
    (* fmtSpine' (G, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading "Break" and increment printing length
  *)
    (* fmtLevel (G, d, ctx, (oa, s)) = fmt

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
    (* braces (G, d, ((D, V), s)) = oa
     convert declaration D[s] as a prefix pi-abstraction into operator/arguments
     form with prefix "{D}" and argument V at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- V : L  [NOTE: s does not apply to V!]
  *)
    (* brackets (G, d, ((D, U), s)) = oa
     convert declaration D[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix "[D]" and argument U at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- U : V  [NOTE: s does not apply to U!]
  *)
    (* fmtDec (G, d, (D, s)) = fmt
     format declaration D[s] at printing depth d in printing context G approximating G'.

     Invariants:
      G' |- D[s] decl
  *)
    (* alternative with more whitespace *)
    (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
    (* alternative with more whitespace *)
    (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
    (* Assume unique names are already assigned in G0 and G! *)
    (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
    (* reset variable names in between to align names of type V and definition U *)
    (* val _ = Names.varReset () *)
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*)
    (* reset variable names in between to align names of type V and definition U *)
    (* val _ = Names.varReset () *)
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
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
    (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
    let rec formatDec (G, D) = fmtDec (G, 0, (D, I.id))
    let rec formatDecList (G, D) = F.HVbox (fmtDecList (G, D))
    let rec formatDecList' (G, (D, s)) = F.HVbox (fmtDecList' (G, (D, s)))
    let rec formatExp (G, U) = fmtExp (G, 0, noCtxt, (U, I.id))
    let rec formatSpine (G, S) = fmtSpine (G, 0, 0, (S, I.id))
    let rec formatConDec condec = fmtConDec (false__, condec)
    let rec formatConDecI condec = fmtConDec (true__, condec)
    let rec formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
    let rec formatCnstrs cnstrL = F.Vbox0 0 1 (fmtCnstrL cnstrL)
    let rec formatCtx (G0, G) = F.HVbox (fmtCtx (G0, G))
    (* assumes G0 and G are named *)
    let rec decToString (G, D) = F.makestring_fmt (formatDec (G, D))
    let rec expToString (G, U) = F.makestring_fmt (formatExp (G, U))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
    let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
    let rec ctxToString (G0, G) = F.makestring_fmt (formatCtx (G0, G))
    let rec evarInstToString (Xnames) =
      F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
    let rec evarCnstrsToStringOpt (Xnames) =
      let Ys = collectEVars (Xnames, nil) in
      let cnstrL = collectConstraints Ys in
      ((match cnstrL with | nil -> NONE | _ -> SOME (cnstrsToString cnstrL))
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
