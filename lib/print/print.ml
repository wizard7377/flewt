
module type PRINT  =
  sig
    module Formatter : FORMATTER
    val implicit : bool ref
    val printInfix : bool ref
    val printDepth : int option ref
    val printLength : int option ref
    val noShadow : bool ref
    val formatDec : IntSyn.dctx -> IntSyn.__Dec -> Formatter.format
    val formatDecList : IntSyn.dctx -> IntSyn.__Dec list -> Formatter.format
    val formatDecList' :
      IntSyn.dctx -> (IntSyn.__Dec list * IntSyn.__Sub) -> Formatter.format
    val formatExp : IntSyn.dctx -> IntSyn.__Exp -> Formatter.format
    val formatSpine : IntSyn.dctx -> IntSyn.__Spine -> Formatter.format list
    val formatConDec : IntSyn.__ConDec -> Formatter.format
    val formatConDecI : IntSyn.__ConDec -> Formatter.format
    val formatCnstr : IntSyn.__Cnstr -> Formatter.format
    val formatCtx : IntSyn.dctx -> IntSyn.dctx -> Formatter.format
    val decToString : IntSyn.dctx -> IntSyn.__Dec -> string
    val expToString : IntSyn.dctx -> IntSyn.__Exp -> string
    val conDecToString : IntSyn.__ConDec -> string
    val cnstrToString : IntSyn.__Cnstr -> string
    val cnstrsToString : IntSyn.cnstr list -> string
    val ctxToString : IntSyn.dctx -> IntSyn.dctx -> string
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
                     module Symbol : SYMBOL
                   end) : PRINT =
  struct
    module Formatter = Formatter'
    module Tomega = Tomega
    let implicit = ref false__
    let printInfix = ref false__
    let printDepth = ref (NONE : int option)
    let printLength = ref (NONE : int option)
    let noShadow = ref false__
    module I = IntSyn
    module FX = Names.Fixity
    module F = Formatter
    module T = Tomega
    let (lvars : I.__Block option ref list ref) = ref nil
    let rec lookuplvar l =
      let _ =
        if List.exists (fun r -> r = l) (!lvars)
        then ()
        else ((!) ((:=) lvars) lvars) @ [l] in
      let rec find (r::__L) n = if r = l then n else find __L (n + 1) in
      ((Int.toString (find (!lvars) 0))
        (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *))
    let Str = F.String
    let rec Str0 s n = F.String0 n s
    let rec sym s = Str0 (Symbol.sym s)
    let rec nameOf = function | Some id -> id | NONE -> "_"
    let rec fmtEVar (__G) (__X) =
      Str0 (Symbol.evar (Names.evarName (__G, __X)))
    let rec fmtAVar (__G) (__X) =
      Str0 (Symbol.evar ((Names.evarName (__G, __X)) ^ "_"))
    let rec isNil =
      function
      | I.Nil -> true__
      | App _ -> false__
      | SClo (__S, _) -> isNil __S
    let rec subToSpine depth s =
      let rec sTS __0__ __1__ =
        match (__0__, __1__) with
        | (Shift k, __S) ->
            ((if k < depth
              then sTS ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __S)
              else __S)
            (* k >= depth *))
        | (Dot (Idx k, s), __S) ->
            sTS (s, (I.App ((I.Root ((I.BVar k), I.Nil)), __S)))
        | (Dot (Exp (__U), s), __S) -> sTS (s, (I.App (__U, __S)))(* Eta violation, but probably inconsequential -kw *) in
      sTS (s, I.Nil)
    type __ArgStatus =
      | TooFew 
      | Exact of I.__Spine 
      | TooMany of (I.__Spine * I.__Spine) 
    let rec sclo' __2__ __3__ =
      match (__2__, __3__) with
      | (TooFew, s) -> TooFew
      | (Exact (__S), s) -> Exact (I.SClo (__S, s))
      | (TooMany (__S, __S'), s) ->
          TooMany ((I.SClo (__S, s)), (I.SClo (__S', s)))
    let rec sclo'' __4__ __5__ =
      match (__4__, __5__) with
      | (TooFew, s) -> TooFew
      | (Exact (__S), s) -> Exact __S
      | (TooMany (__S, __S'), s) -> TooMany (__S, (I.SClo (__S', s)))
    let rec dropImp __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (0, __S, 0) -> Exact __S
      | (0, __S, n) ->
          let rec checkArgNumber __6__ __7__ =
            match (__6__, __7__) with
            | (I.Nil, 0) -> Exact __S
            | (I.Nil, k) -> TooFew
            | ((App _ as S'), 0) -> TooMany (__S, __S')
            | (App (__U, __S'), k) -> checkArgNumber (__S', (k - 1))
            | (SClo (__S', s), k) -> sclo'' ((checkArgNumber (__S', k)), s) in
          checkArgNumber (__S, n)
      | (i, App (__U, __S), n) -> dropImp ((i - 1), __S, n)
      | (i, SClo (__S, s), n) -> sclo' ((dropImp (i, __S, n)), s)
      | (i, I.Nil, n) -> TooFew(* n >= 1 *)
    let rec exceeded __11__ __12__ =
      match (__11__, __12__) with
      | (_, NONE) -> false__
      | ((n : int), Some (m : int)) -> n >= m
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
    let rec arrow (__V1) (__V2) =
      OpArgs
        ((FX.Infix (arrowPrec, FX.Right)), [F.Break; sym "->"; F.Space],
          (I.App (__V1, (I.App (__V2, I.Nil)))))
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
    let rec fmtConstPath f (Qid (ids, id)) =
      F.HVbox
        (foldr
           (fun id -> fun fmt -> ((::) (Str0 (Symbol.str id)) sym ".") :: fmt)
           [Str0 (f id)] ids)
    let rec parmDec __13__ __14__ =
      match (__13__, __14__) with
      | ((__D)::__L, 1) -> __D
      | ((__D)::__L, j) -> parmDec (__L, (j - 1))
    let rec parmName cid i =
      let (Gsome, Gblock) = I.constBlock cid in
      match parmDec (Gblock, i) with
      | Dec (Some pname, _) -> pname
      | Dec (NONE, _) -> Int.toString i
    let rec projName __15__ __16__ =
      match (__15__, __16__) with
      | (__G, Proj (Bidx k, i)) ->
          let BDec (Some bname, (cid, t)) = I.ctxLookup (__G, k) in
          (((^) (bname ^ "_") parmName (cid, i))
            (* names should have been assigned by invar
         iant, NONE imppossible *))
      | (__G, Proj (LVar (r, _, (cid, t)), i)) -> (^) "_" parmName (cid, i)
      | (__G, Proj (Inst iota, i)) -> "*"(* no longer Tue Mar  1 13:32:21 2011 -cs *)
      (* note: this obscures LVar identity! *)
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
    let rec worldsToString (__W) = F.makestring_fmt (formatWorlds __W)
    let rec fmtCon __17__ __18__ =
      match (__17__, __18__) with
      | (__G, BVar n) -> Str0 (Symbol.bvar (Names.bvarName (__G, n)))
      | (__G, Const cid) -> fmtConstPath (Symbol.const, (constQid cid))
      | (__G, Skonst cid) -> fmtConstPath (Symbol.skonst, (constQid cid))
      | (__G, Def cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (__G, NSDef cid) -> fmtConstPath (Symbol.def, (constQid cid))
      | (__G, FVar (name, _, _)) -> Str0 (Symbol.fvar name)
      | (__G, (Proj (Bidx k, i) as H)) ->
          Str0 (Symbol.const (projName (__G, __H)))
      | (__G,
         (Proj (LVar (({ contents = NONE } as r), sk, (cid, t)), i) as H)) ->
          let n = lookuplvar r in
          ((fmtConstPath
              ((fun l0 ->
                  Symbol.const
                    ((^) ((("#[" ^ l0) ^ n) ^ "]") projName (__G, __H))),
                (constQid cid)))
            (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *))
      | (__G, FgnConst (cs, conDec)) ->
          let name = I.conDecName conDec in
          (((match ((Names.constLookup (Names.Qid (nil, name))), (!noShadow))
             with
             | (Some _, false__) -> Str0 (Symbol.const (("%" ^ name) ^ "%"))
             | _ -> Str0 (Symbol.const name)))
            (* the user has re-defined this name *)(* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *))
    let rec evarArgs (__G) d (__X) s =
      OpArgs
        (FX.Nonfix, [fmtEVar (__G, __X)],
          (subToSpine ((I.ctxLength __G), s)))
    let rec evarArgs' (__G) d (__X) s =
      OpArgs
        (FX.Nonfix, [fmtAVar (__G, __X)],
          (subToSpine ((I.ctxLength __G), s)))
    let rec fst __19__ __20__ =
      match (__19__, __20__) with
      | (App (__U1, _), s) -> (__U1, s)
      | (SClo (__S, s'), s) -> fst (__S, (I.comp (s', s)))
    let rec snd __21__ __22__ =
      match (__21__, __22__) with
      | (App (__U1, __S), s) -> fst (__S, s)
      | (SClo (__S, s'), s) -> snd (__S, (I.comp (s', s)))
    let rec elide l =
      match !printLength with | NONE -> false__ | Some l' -> l > l'
    let ldots = sym "..."
    let rec addots l =
      match !printLength with | NONE -> false__ | Some l' -> l = l'
    let rec parens (fixity', fixity) fmt =
      if FX.leq ((FX.prec fixity), (FX.prec fixity'))
      then F.Hbox [sym "("; fmt; sym ")"]
      else fmt
    let rec eqFix __23__ __24__ =
      match (__23__, __24__) with
      | (Infix (p, FX.Left), Infix (p', FX.Left)) -> p = p'
      | (Infix (p, FX.Right), Infix (p', FX.Right)) -> p = p'
      | (Prefix p, Prefix p') -> p = p'
      | (Postfix p, Postfix p') -> p = p'
      | _ -> false__(* Nonfix should never be asked *)
      (* Infix(_,None) should never be asked *)
    let rec addAccum __25__ __26__ __27__ =
      match (__25__, __26__, __27__) with
      | (fmt, _, nil) -> fmt
      | (fmt, Infix (_, FX.Left), accum) -> F.HVbox ([fmt] @ accum)
      | (fmt, Infix (_, FX.Right), accum) -> F.HVbox (accum @ [fmt])
      | (fmt, Prefix _, accum) -> F.HVbox (accum @ [fmt])
      | (fmt, Postfix _, accum) -> F.HVbox ([fmt] @ accum)
    let rec aa (Ctxt (fixity, accum, l)) fmt = addAccum (fmt, fixity, accum)
    let rec fmtUni = function | I.Type -> sym "type" | I.Kind -> sym "kind"
    let rec fmtExpW __28__ __29__ __30__ __31__ =
      match (__28__, __29__, __30__, __31__) with
      | (__G, d, ctx, (Uni (__L), s)) -> aa (ctx, (fmtUni __L))
      | (__G, d, ctx, (Pi (((Dec (_, __V1) as D), __P), __V2), s)) ->
          (((match __P with
             | I.Maybe ->
                 let __D' = Names.decLUName (__G, __D) in
                 ((fmtLevel
                     ((((I.Decl (__G, __D')), d, ctx,
                         ((braces (__G, d, ((__D', __V2), s))), (I.dot1 s))))
                     (* I.decSub (D', s) *)))
                   (* could sometimes be EName *))
             | I.Meta ->
                 let __D' = Names.decLUName (__G, __D) in
                 fmtLevel
                   ((((I.Decl (__G, __D')), d, ctx,
                       ((braces (__G, d, ((__D', __V2), s))), (I.dot1 s))))
                   (* I.decSub (D', s) *))
             | I.No ->
                 fmtLevel
                   ((((I.Decl (__G, __D)), d, ctx,
                       ((arrow ((I.EClo (__V1, I.shift)), __V2)), (I.dot1 s))))
                   (* I.decSub (D, s) *))))
          (* if Pi is dependent but anonymous, invent name here *))
      | (__G, d, ctx, (Pi (((BDec _ as D), __P), __V2), s)) ->
          let __D' = Names.decLUName (__G, __D) in
          fmtLevel
            ((I.Decl (__G, __D')), d, ctx,
              ((braces (__G, d, ((__D', __V2), s))), (I.dot1 s)))
      | (__G, d, ctx, (Pi (((ADec _ as D), __P), __V2), s)) ->
          let braces =
            OpArgs
              ((FX.Prefix binderPrec), [sym "["; sym "_"; sym "]"; F.Break],
                (IntSyn.App (__V2, IntSyn.Nil))) in
          ((fmtLevel ((I.Decl (__G, __D)), d, ctx, (braces, (I.dot1 s))))
            (*      val D' = Names.decLUName (G, D) *))
      | (__G, d, ctx, ((Root (__R) as U), s)) ->
          fmtOpArgs (__G, d, ctx, (opargs (__G, d, __R)), s)
      | (__G, d, ctx, (Lam (__D, __U), s)) ->
          let __D' = Names.decLUName (__G, __D) in
          fmtLevel
            ((((I.Decl (__G, __D')), d, ctx,
                ((brackets (__G, d, ((__D', __U), s))), (I.dot1 s))))
            (* I.decSub (D', s) *))
      | (__G, d, ctx, ((EVar _ as X), s)) ->
          if !implicit
          then
            aa
              (ctx, (F.HVbox ((::) (fmtEVar (__G, __X)) fmtSub (__G, d, s))))
          else fmtOpArgs (__G, d, ctx, (evarArgs (__G, d, __X, s)), I.id)
      | (__G, d, ctx, ((AVar _ as X), s)) ->
          if !implicit
          then
            aa
              (ctx, (F.HVbox ((::) (fmtAVar (__G, __X)) fmtSub (__G, d, s))))
          else fmtOpArgs (__G, d, ctx, (evarArgs' (__G, d, __X, s)), I.id)
      | (__G, d, ctx, ((FgnExp csfe as U), s)) ->
          fmtExp (__G, d, ctx, ((I.FgnExpStd.ToInternal.apply csfe ()), s))
      (* assume dereferenced during whnf *)(* assume dereferenced during whnf *)
      (* I.Redex not possible *)(* s = id *)(* -bp *)
    let rec opargsImplicit (__G) d (__C, __S) =
      OpArgs (FX.Nonfix, [fmtCon (__G, __C)], __S)
    let rec opargsImplicitInfix (__G) d ((__C, __S) as R) =
      let fixity = fixityCon __C in
      ((match fixity with
        | Infix _ -> opargsExplicit (__G, d, __R)
        | _ -> OpArgs (FX.Nonfix, [fmtCon (__G, __C)], __S))
        (* Can't have implicit arguments by invariant *))
    let rec opargsExplicit (__G) d ((__C, __S) as R) =
      let opFmt = fmtCon (__G, __C) in
      let fixity = fixityCon __C in
      let rec oe =
        function
        | Exact (__S') ->
            (match fixity with
             | FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], __S')
             | Prefix _ -> OpArgs (fixity, [opFmt; F.Break], __S')
             | Postfix _ -> OpArgs (fixity, [F.Break; opFmt], __S')
             | Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.Space], __S'))
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root __R))
        | TooMany (__S', S'') ->
            let opFmt' = fmtOpArgs (__G, d, noCtxt, (oe (Exact __S')), I.id) in
            ((OpArgs (FX.Nonfix, [F.Hbox [sym "("; opFmt'; sym ")"]], S''))
              (* parens because juxtaposition has highest precedence *)
              (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *))
        (* S'' - extra arguments *)(* S' - all non-implicit arguments *)
        (* extra arguments to infix operator *) in
      oe (dropImp ((impCon __C), __S, (argNumber fixity)))
    let rec opargs (__G) d (__R) =
      if !implicit
      then
        (if !printInfix
         then opargsImplicitInfix (__G, d, __R)
         else opargsImplicit (__G, d, __R))
      else opargsExplicit (__G, d, __R)
    let rec fmtOpArgs __32__ __33__ __34__ __35__ __36__ =
      match (__32__, __33__, __34__, __35__, __36__) with
      | (__G, d, ctx, (OpArgs (_, opFmts, __S') as oa), s) ->
          ((if isNil __S'
            then aa (ctx, (List.hd opFmts))
            else fmtLevel (__G, d, ctx, (oa, s)))
          (* opFmts = [fmtCon(G,C)] *))
      | (__G, d, ctx, EtaLong (__U'), s) -> fmtExpW (__G, d, ctx, (__U', s))
    let rec fmtSub (__G) d s = (::) (Str "[") fmtSub' (__G, d, 0, s)
    let rec fmtSub' (__G) d l s =
      if elide l then [ldots] else fmtSub'' (__G, d, l, s)
    let rec fmtSub'' __37__ __38__ __39__ __40__ =
      match (__37__, __38__, __39__, __40__) with
      | (__G, d, l, Shift k) -> [Str ((^) "^" Int.toString k); Str "]"]
      | (__G, d, l, Dot (Idx k, s)) ->
          (::) (((::) (Str (Names.bvarName (__G, k))) Str ".") :: F.Break)
            fmtSub' (__G, d, (l + 1), s)
      | (__G, d, l, Dot (Exp (__U), s)) ->
          (::) (((::) (fmtExp (__G, (d + 1), noCtxt, (__U, I.id))) Str ".")
                  :: F.Break)
            fmtSub' (__G, d, (l + 1), s)
    let rec fmtExp (__G) d ctx (__U, s) =
      if exceeded (d, (!printDepth))
      then sym "%%"
      else fmtExpW (__G, d, ctx, (Whnf.whnf (__U, s)))
    let rec fmtSpine __41__ __42__ __43__ __44__ =
      match (__41__, __42__, __43__, __44__) with
      | (__G, d, l, (I.Nil, _)) -> []
      | (__G, d, l, (SClo (__S, s'), s)) ->
          fmtSpine (__G, d, l, (__S, (I.comp (s', s))))
      | (__G, d, l, (App (__U, __S), s)) ->
          ((if elide l
            then []
            else
              if addots l
              then [ldots]
              else
                (::) (fmtExp (__G, (d + 1), appCtxt, (__U, s))) fmtSpine'
                  (__G, d, l, (__S, s)))
          (* necessary? *))
    let rec fmtSpine' __45__ __46__ __47__ __48__ =
      match (__45__, __46__, __47__, __48__) with
      | (__G, d, l, (I.Nil, _)) -> []
      | (__G, d, l, (SClo (__S, s'), s)) ->
          fmtSpine' (__G, d, l, (__S, (I.comp (s', s))))
      | (__G, d, l, (__S, s)) ->
          (::) F.Break fmtSpine (__G, d, (l + 1), (__S, s))
    let rec fmtLevel __49__ __50__ __51__ __52__ =
      match (__49__, __50__, __51__, __52__) with
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((FX.Nonfix as fixity), fmts, __S), s)) ->
          let atm = fmtSpine (__G, d, 0, (__S, s)) in
          ((addAccum
              ((parens
                  ((fixity', fixity), (F.HVbox ((fmts @ [F.Break]) @ atm)))),
                fixity', accum))
            (* atm must not be empty, otherwise bug below *)
            (* F.HVbox doesn't work if last item of HVbox is F.Break *)
            (* possible improvement along the following lines: *)
            (*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *))
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (p, FX.Left) as fixity), fmts, __S), s)) ->
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
                     (__G, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                       (snd (__S, s)))] in
          if accMore
          then
            fmtExp
              (__G, d, (Ctxt (fixity, (rhs @ accum), (l + 1))),
                (fst (__S, s)))
          else
            (let both =
               fmtExp (__G, d, (Ctxt (fixity, rhs, 0)), (fst (__S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (p, FX.Right) as fixity), fmts, __S), s)) ->
          let accMore = eqFix (fixity, fixity') in
          let lhs =
            if accMore && (elide l)
            then []
            else
              if accMore && (addots l)
              then [ldots] @ fmts
              else
                [fmtExp
                   (__G, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), nil, 0)),
                     (fst (__S, s)))]
                  @ fmts in
          if accMore
          then
            fmtExp
              (__G, d, (Ctxt (fixity, (accum @ lhs), (l + 1))),
                (snd (__S, s)))
          else
            (let both =
               fmtExp (__G, d, (Ctxt (fixity, lhs, 0)), (snd (__S, s))) in
             addAccum ((parens ((fixity', fixity), both)), fixity', accum))
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Infix (_, FX.None) as fixity), fmts, __S), s)) ->
          let lhs =
            fmtExp (__G, (d + 1), (Ctxt (fixity, nil, 0)), (fst (__S, s))) in
          let rhs =
            fmtExp (__G, (d + 1), (Ctxt (fixity, nil, 0)), (snd (__S, s))) in
          addAccum
            ((parens ((fixity', fixity), (F.HVbox (([lhs] @ fmts) @ [rhs])))),
              fixity', accum)
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Prefix _ as fixity), fmts, __S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [ldots; F.Break] else fmts in
          if accMore
          then
            fmtExp
              (__G, d, (Ctxt (fixity, (accum @ pfx), (l + 1))),
                (fst (__S, s)))
          else
            (let whole =
               fmtExp (__G, d, (Ctxt (fixity, pfx, 0)), (fst (__S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
      | (__G, d, Ctxt (fixity', accum, l),
         (OpArgs ((Postfix _ as fixity), fmts, __S), s)) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            if accMore && (elide l)
            then []
            else if accMore && (addots l) then [F.Break; ldots] else fmts in
          if accMore
          then
            fmtExp
              (__G, d, (Ctxt (fixity, (pfx @ accum), (l + 1))),
                (fst (__S, s)))
          else
            (let whole =
               fmtExp (__G, d, (Ctxt (fixity, pfx, 0)), (fst (__S, s))) in
             addAccum ((parens ((fixity', fixity), whole)), fixity', accum))
    let rec braces (__G) d ((__D, __V), s) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "{"; fmtDec (__G, d, (__D, s)); sym "}"; F.Break],
          (IntSyn.App (__V, IntSyn.Nil)))
    let rec brackets (__G) d ((__D, __U), s) =
      OpArgs
        ((FX.Prefix binderPrec),
          [sym "["; fmtDec (__G, d, (__D, s)); sym "]"; F.Break],
          (IntSyn.App (__U, IntSyn.Nil)))
    let rec fmtDec __53__ __54__ __55__ =
      match (__53__, __54__, __55__) with
      | (__G, d, (Dec (x, __V), s)) ->
          F.HVbox
            [Str0 (Symbol.bvar (nameOf x));
            sym ":";
            fmtExp (__G, (d + 1), noCtxt, (__V, s))]
      | (__G, d, (BDec (x, (cid, t)), s)) ->
          let (Gsome, Gblock) = I.constBlock cid in
          F.HVbox
            ((@) [Str0 (Symbol.const (nameOf x)); sym ":"] fmtDecList'
               (__G, (Gblock, (I.comp (t, s)))))
      | (__G, d, (ADec (x, _), s)) ->
          F.HVbox [Str0 (Symbol.bvar (nameOf x)); sym ":_"]
      | (__G, d, (NDec (Some name), s)) -> F.HVbox [sym name](* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
      (* alternative with more whitespace *)
    let rec fmtDecList' __56__ __57__ =
      match (__56__, __57__) with
      | (__G0, (nil, s)) -> nil
      | (__G0, ((__D)::nil, s)) ->
          ((::) ((::) (sym "{") fmtDec (__G0, 0, (__D, s))) sym "}") :: nil
      | (__G0, ((__D)::__L, s)) ->
          (::) (((::) ((::) (sym "{") fmtDec (__G0, 0, (__D, s))) sym "}") ::
                  F.Break)
            fmtDecList' ((I.Decl (__G0, __D)), (__L, (I.dot1 s)))
    let rec skipI __58__ __59__ __60__ =
      match (__58__, __59__, __60__) with
      | (0, __G, __V) -> (__G, __V)
      | (i, __G, Pi ((__D, _), __V)) ->
          skipI ((i - 1), (I.Decl (__G, (Names.decEName (__G, __D)))), __V)
    let rec skipI2 __61__ __62__ __63__ __64__ =
      match (__61__, __62__, __63__, __64__) with
      | (0, __G, __V, __U) -> (__G, __V, __U)
      | (i, __G, Pi ((__D, _), __V), Lam (__D', __U)) ->
          skipI2
            ((i - 1), (I.Decl (__G, (Names.decEName (__G, __D')))), __V, __U)
    let rec ctxToDecList __65__ __66__ =
      match (__65__, __66__) with
      | (I.Null, __L) -> __L
      | (Decl (__G, __D), __L) -> ctxToDecList (__G, (__D :: __L))
    let rec fmtDecList __67__ __68__ =
      match (__67__, __68__) with
      | (__G0, nil) -> nil
      | (__G0, (__D)::nil) ->
          ((::) ((::) (sym "{") fmtDec (__G0, 0, (__D, I.id))) sym "}") ::
            nil
      | (__G0, (__D)::__L) ->
          (::) (((::) ((::) (sym "{") fmtDec (__G0, 0, (__D, I.id))) sym "}")
                  :: F.Break)
            fmtDecList ((I.Decl (__G0, __D)), __L)
    let rec fmtCtx (__G0) (__G) =
      fmtDecList (__G0, (ctxToDecList (__G, nil)))
    let rec fmtBlock __69__ __70__ =
      match (__69__, __70__) with
      | (I.Null, Lblock) ->
          [sym "block"; F.Break] @ (fmtDecList (I.Null, Lblock))
      | (Gsome, Lblock) ->
          [F.HVbox ([sym "some"; F.Space] @ (fmtCtx (I.Null, Gsome)));
          F.Break;
          F.HVbox ([sym "block"; F.Space] @ (fmtDecList (Gsome, Lblock)))]
    let rec fmtConDec __71__ __72__ =
      match (__71__, __72__) with
      | (hide, (ConDec (_, _, imp, _, __V, __L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__G, __V) =
            if hide then skipI (imp, I.Null, __V) else (I.Null, __V) in
          let Vfmt = fmtExp (__G, 0, noCtxt, (__V, I.id)) in
          F.HVbox
            [fmtConstPath (Symbol.const, qid);
            F.Space;
            sym ":";
            F.Break;
            Vfmt;
            sym "."]
      | (hide, (SkoDec (_, _, imp, __V, __L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__G, __V) =
            if hide then skipI (imp, I.Null, __V) else (I.Null, __V) in
          let Vfmt = fmtExp (__G, 0, noCtxt, (__V, I.id)) in
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
      | (hide, (BlockDef (_, _, __W) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.HVbox
            ([sym "%block";
             F.Break;
             fmtConstPath (Symbol.label, qid);
             F.Space;
             sym "=";
             F.Break] @ ((formatWorlds (T.Worlds __W)) :: [sym "."]))
      | (hide, (ConDef (_, _, imp, __U, __V, __L, _) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__G, __V, __U) =
            if hide
            then skipI2 (imp, I.Null, __V, __U)
            else (I.Null, __V, __U) in
          let Vfmt = fmtExp (__G, 0, noCtxt, (__V, I.id)) in
          let Ufmt = fmtExp (__G, 0, noCtxt, (__U, I.id)) in
          ((F.HVbox
              [fmtConstPath (Symbol.def, qid);
              F.Space;
              sym ":";
              F.Break;
              Vfmt;
              F.Break;
              sym "=";
              F.Space;
              Ufmt;
              sym "."])
            (* val _ = Names.varReset () *)(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*))
      | (hide, (AbbrevDef (_, _, imp, __U, __V, __L) as condec)) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let (__G, __V, __U) =
            if hide
            then skipI2 (imp, I.Null, __V, __U)
            else (I.Null, __V, __U) in
          let Vfmt = fmtExp (__G, 0, noCtxt, (__V, I.id)) in
          let Ufmt = fmtExp (__G, 0, noCtxt, (__U, I.id)) in
          ((F.HVbox
              [fmtConstPath (Symbol.def, qid);
              F.Space;
              sym ":";
              F.Break;
              Vfmt;
              F.Break;
              sym "=";
              F.Space;
              Ufmt;
              sym "."])
            (* val _ = Names.varReset () *)(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
*))
      (* reset variable names in between to align names of type V and definition U *)
      (* reset variable names in between to align names of type V and definition U *)
    let rec fmtCnstr =
      function
      | I.Solved -> [Str "Solved Constraint"]
      | Eqn (__G, __U1, __U2) ->
          let __G' = Names.ctxLUName __G in
          [F.HVbox
             [fmtExp (__G', 0, noCtxt, (__U1, I.id));
             F.Break;
             sym "=";
             F.Space;
             fmtExp (__G', 0, noCtxt, (__U2, I.id))]]
      | FgnCnstr ((cs, _) as csfc) ->
          let rec fmtExpL =
            function
            | nil -> [Str "Empty Constraint"]
            | (__G, __U)::nil ->
                [fmtExp ((Names.ctxLUName __G), 0, noCtxt, (__U, I.id))]
            | (__G, __U)::expL ->
                (@) [fmtExp ((Names.ctxLUName __G), 0, noCtxt, (__U, I.id));
                    Str ";";
                    F.Break]
                  fmtExpL expL in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ())
    let rec fmtCnstrL =
      function
      | nil -> [Str "Empty Constraint"]
      | { contents = Cnstr }::nil -> (fmtCnstr Cnstr) @ [Str "."]
      | { contents = Cnstr }::cnstrL ->
          ((fmtCnstr Cnstr) @ [Str ";"; F.Break]) @ (fmtCnstrL cnstrL)
    let rec abstractLam __73__ __74__ =
      match (__73__, __74__) with
      | (I.Null, __U) -> __U
      | (Decl (__G, __D), __U) -> abstractLam (__G, (I.Lam (__D, __U)))
    let rec fmtNamedEVar __75__ __76__ =
      match (__75__, __76__) with
      | ((EVar (_, __G, _, _) as U), name) ->
          let __U' = abstractLam (__G, __U) in
          F.HVbox
            [Str0 (Symbol.evar name);
            F.Space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (__U', I.id))]
      | (__U, name) ->
          F.HVbox
            [Str0 (Symbol.evar name);
            F.Space;
            sym "=";
            F.Break;
            fmtExp (I.Null, 0, noCtxt, (__U, I.id))](* used for proof term variables in queries *)
    let rec fmtEVarInst =
      function
      | nil -> [Str "Empty Substitution"]
      | (__U, name)::nil -> [fmtNamedEVar (__U, name)]
      | (__U, name)::__Xs ->
          (::) (((::) (fmtNamedEVar (__U, name)) Str ";") :: F.Break)
            fmtEVarInst __Xs
    let rec collectEVars __77__ __78__ =
      match (__77__, __78__) with
      | (nil, __Xs) -> __Xs
      | ((__U, _)::Xnames, __Xs) ->
          collectEVars
            (Xnames, (Abstract.collectEVars (I.Null, (__U, I.id), __Xs)))
    let rec eqCnstr r1 r2 = r1 = r2
    let rec mergeConstraints __79__ __80__ =
      match (__79__, __80__) with
      | (nil, cnstrs2) -> cnstrs2
      | (cnstr::cnstrs1, cnstrs2) ->
          if List.exists (eqCnstr cnstr) cnstrs2
          then mergeConstraints (cnstrs1, cnstrs2)
          else cnstr :: (mergeConstraints (cnstrs1, cnstrs2))
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar ({ contents = NONE }, _, _, cnstrs))::__Xs ->
          mergeConstraints
            ((Constraints.simplify (!cnstrs)), (collectConstraints __Xs))
      | _::__Xs -> collectConstraints __Xs
    let rec formatDec (__G) (__D) = fmtDec (__G, 0, (__D, I.id))
    let rec formatDecList (__G) (__D) = F.HVbox (fmtDecList (__G, __D))
    let rec formatDecList' (__G) (__D, s) =
      F.HVbox (fmtDecList' (__G, (__D, s)))
    let rec formatExp (__G) (__U) = fmtExp (__G, 0, noCtxt, (__U, I.id))
    let rec formatSpine (__G) (__S) = fmtSpine (__G, 0, 0, (__S, I.id))
    let rec formatConDec condec = fmtConDec (false__, condec)
    let rec formatConDecI condec = fmtConDec (true__, condec)
    let rec formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
    let rec formatCnstrs cnstrL = F.Vbox0 0 1 (fmtCnstrL cnstrL)
    let rec formatCtx (__G0) (__G) = F.HVbox (fmtCtx (__G0, __G))
    let rec decToString (__G) (__D) = F.makestring_fmt (formatDec (__G, __D))
    let rec expToString (__G) (__U) = F.makestring_fmt (formatExp (__G, __U))
    let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
    let rec cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
    let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
    let rec ctxToString (__G0) (__G) =
      F.makestring_fmt (formatCtx (__G0, __G))
    let rec evarInstToString (Xnames) =
      F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
    let rec evarCnstrsToStringOpt (Xnames) =
      let __Ys = collectEVars (Xnames, nil) in
      let cnstrL = collectConstraints __Ys in
      ((match cnstrL with | nil -> NONE | _ -> Some (cnstrsToString cnstrL))
        (* collect EVars in instantiations *))
    let rec printSgn () =
      IntSyn.sgnApp
        (fun cid ->
           print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
           print "\n")
    let formatWorlds = formatWorlds
    let worldsToString = worldsToString
  end ;;




module SymbolAscii = (Make_SymbolAscii)(struct  end)
module SymbolTeX = (Make_SymbolTeX)(struct  end)
module Print =
  (Make_Print)(struct
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolAscii
               end)
module ClausePrint =
  (Make_ClausePrint)(struct
                       module Whnf = Whnf
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = Print
                       module Symbol = SymbolAscii
                     end)
module PrintTeX =
  (Make_Print)(struct
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolTeX
               end)
module ClausePrintTeX =
  (Make_ClausePrint)(struct
                       module Whnf = Whnf
                       module Constraints = Constraints
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = PrintTeX
                       module Symbol = SymbolTeX
                     end)
module PrintTwega =
  (Make_PrintTwega)(struct
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end)
module PrintXML =
  (Make_PrintXML)(struct
                    module Whnf = Whnf
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Names = Names
                    module Formatter' = Formatter
                  end)
module PrintOMDoc =
  (Make_PrintOMDoc)(struct
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end);;
