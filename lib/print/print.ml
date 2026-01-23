module type PRINT  =
  sig
    module Formatter : FORMATTER
    val implicit : bool ref
    val printInfix : bool ref
    val printDepth : int option ref
    val printLength : int option ref
    val noShadow : bool ref
    val formatDec : (IntSyn.dctx * IntSyn.dec_) -> Formatter.format
    val formatDecList : (IntSyn.dctx * IntSyn.dec_ list) -> Formatter.format
    val formatDecList' :
      (IntSyn.dctx * (IntSyn.dec_ list * IntSyn.sub_)) -> Formatter.format
    val formatExp : (IntSyn.dctx * IntSyn.exp_) -> Formatter.format
    val formatSpine : (IntSyn.dctx * IntSyn.spine_) -> Formatter.format list
    val formatConDec : IntSyn.conDec_ -> Formatter.format
    val formatConDecI : IntSyn.conDec_ -> Formatter.format
    val formatCnstr : IntSyn.cnstr_ -> Formatter.format
    val formatCtx : (IntSyn.dctx * IntSyn.dctx) -> Formatter.format
    val decToString : (IntSyn.dctx * IntSyn.dec_) -> string
    val expToString : (IntSyn.dctx * IntSyn.exp_) -> string
    val conDecToString : IntSyn.conDec_ -> string
    val cnstrToString : IntSyn.cnstr_ -> string
    val cnstrsToString : IntSyn.cnstr list -> string
    val ctxToString : (IntSyn.dctx * IntSyn.dctx) -> string
    val evarInstToString : (IntSyn.exp_ * string) list -> string
    val evarCnstrsToStringOpt : (IntSyn.exp_ * string) list -> string option
    val formatWorlds : Tomega.worlds_ -> Formatter.format
    val worldsToString : Tomega.worlds_ -> string
    val printSgn : unit -> unit
  end


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
    let implicit = ref false
    let printInfix = ref false
    let printDepth = ref (None : int option)
    let printLength = ref (None : int option)
    let noShadow = ref false
    module I = IntSyn
    module FX = Names.Fixity
    module F = Formatter
    module T = Tomega
    let (lvars : I.block_ option ref list ref) = ref []
    let rec lookuplvar l =
      let _ = if List.exists (begin function | r -> r = l end) !lvars
        then begin () end else begin ((!) ((:=) lvars) lvars) @ [l] end in
  let rec find (r::l_) n = if r = l then begin n end
    else begin find l_ (n + 1) end in
  ((Int.toString (find !lvars 0))
    (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *))
let Str = F.String
let rec Str0 (s, n) = F.String0 n s
let rec sym s = Str0 (Symbol.sym s)
let rec nameOf = begin function | Some id -> id | None -> "_" end
let rec fmtEVar (g_, x_) = Str0 (Symbol.evar (Names.evarName (g_, x_)))
let rec fmtAVar (g_, x_) =
  Str0 (Symbol.evar ((Names.evarName (g_, x_)) ^ "_"))
let rec isNil =
  begin function | I.Nil -> true | App _ -> false | SClo (s_, _) -> isNil s_ end
let rec subToSpine (depth, s) =
  let rec sTS =
    begin function
    | (Shift k, s_) ->
        ((if k < depth
          then begin sTS ((I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), s_) end
        else begin s_ end)
    (* k >= depth *))
    | (Dot (Idx k, s), s_) ->
        sTS (s, (I.App ((I.Root ((I.BVar k), I.Nil)), s_)))
    | (Dot (Exp (u_), s), s_) -> sTS (s, (I.App (u_, s_))) end(* Eta violation, but probably inconsequential -kw *) in
sTS (s, I.Nil)
type argStatus_ =
  | TooFew 
  | Exact of I.spine_ 
  | TooMany of (I.spine_ * I.spine_) 
let rec sclo' =
  begin function
  | (TooFew, s) -> TooFew
  | (Exact (s_), s) -> Exact (I.SClo (s_, s))
  | (TooMany (s_, s'_), s) -> TooMany ((I.SClo (s_, s)), (I.SClo (s'_, s))) end
let rec sclo'' =
  begin function
  | (TooFew, s) -> TooFew
  | (Exact (s_), s) -> Exact s_
  | (TooMany (s_, s'_), s) -> TooMany (s_, (I.SClo (s'_, s))) end
let rec dropImp =
  begin function
  | (0, s_, 0) -> Exact s_
  | (0, s_, n) ->
      let rec checkArgNumber =
        begin function
        | (I.Nil, 0) -> Exact s_
        | (I.Nil, k) -> TooFew
        | ((App _ as s'_), 0) -> TooMany (s_, s'_)
        | (App (u_, s'_), k) -> checkArgNumber (s'_, (k - 1))
        | (SClo (s'_, s), k) -> sclo'' ((checkArgNumber (s'_, k)), s) end in
    checkArgNumber (s_, n)
  | (i, App (u_, s_), n) -> dropImp ((i - 1), s_, n)
  | (i, SClo (s_, s), n) -> sclo' ((dropImp (i, s_, n)), s)
  | (i, I.Nil, n) -> TooFew end(* n >= 1 *)
let rec exceeded =
  begin function | (_, None) -> false | ((n : int), Some (m : int)) -> n >= m end
type ctxt =
  | Ctxt of (FX.fixity * F.format list * int) 
type opargs =
  | OpArgs of (FX.fixity * F.format list * I.spine_) 
  | EtaLong of I.exp_ 
let noCtxt =
  Ctxt ((FX.Prefix (FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec))))), [], 0)
let binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
let arrowPrec = FX.dec FX.minPrec
let juxPrec = FX.inc FX.maxPrec
let rec arrow (v1_, v2_) =
  OpArgs
    ((FX.Infix (arrowPrec, FX.Right)), [F.Break; sym "->"; F.Space],
      (I.App (v1_, (I.App (v2_, I.Nil)))))
let appCtxt = Ctxt (FX.Nonfix, [], 0)
let rec fixityCon =
  begin function
  | Const cid -> Names.getFixity cid
  | Skonst cid -> FX.Nonfix
  | Def cid -> Names.getFixity cid
  | NSDef cid -> Names.getFixity cid
  | _ -> FX.Nonfix end
let rec impCon =
  begin function
  | Const cid -> I.constImp cid
  | Skonst cid -> I.constImp cid
  | Def cid -> I.constImp cid
  | NSDef cid -> I.constImp cid
  | _ -> 0 end
let rec argNumber =
  begin function
  | FX.Nonfix -> 0
  | Infix _ -> 2
  | Prefix _ -> 1
  | Postfix _ -> 1 end
let rec fmtConstPath (f, Qid (ids, id)) =
  F.HVbox
    (foldr
       (begin function
        | (id, fmt) -> ((::) (Str0 (Symbol.str id)) sym ".") :: fmt end)
    [Str0 (f id)] ids)
let rec parmDec =
  begin function
  | ((d_)::l_, 1) -> d_
  | ((d_)::l_, j) -> parmDec (l_, (j - 1)) end
let rec parmName (cid, i) =
  let (Gsome, Gblock) = I.constBlock cid in
  begin match parmDec (Gblock, i) with
  | Dec (Some pname, _) -> pname
  | Dec (None, _) -> Int.toString i end
let rec projName =
  begin function
  | (g_, Proj (Bidx k, i)) ->
      let BDec (Some bname, (cid, t)) = I.ctxLookup (g_, k) in
      (((^) (bname ^ "_") parmName (cid, i))
        (* names should have been assigned by invar
         iant, NONE imppossible *))
  | (g_, Proj (LVar (r, _, (cid, t)), i)) -> (^) "_" parmName (cid, i)
  | (g_, Proj (Inst iota, i)) -> "*" end(* no longer Tue Mar  1 13:32:21 2011 -cs *)
(* note: this obscures LVar identity! *)
let rec constQid cid =
  if !noShadow then begin Names.conDecQid (I.sgnLookup cid) end
  else begin Names.constQid cid end
let rec cidToFmt cid = F.String (Names.qidToString (Names.constQid cid))
let rec formatCids =
  begin function
  | [] -> []
  | cid::[] -> [cidToFmt cid]
  | cid::cids ->
      (::) (((::) ((cidToFmt cid) :: F.Break) F.String "|") :: F.Space)
        formatCids cids end
let rec formatWorlds (Worlds cids) =
  F.Hbox [F.String "("; F.HVbox (formatCids cids); F.String ")"]
let rec worldsToString (w_) = F.makestring_fmt (formatWorlds w_)
let rec fmtCon =
  begin function
  | (g_, BVar n) -> Str0 (Symbol.bvar (Names.bvarName (g_, n)))
  | (g_, Const cid) -> fmtConstPath (Symbol.const, (constQid cid))
  | (g_, Skonst cid) -> fmtConstPath (Symbol.skonst, (constQid cid))
  | (g_, Def cid) -> fmtConstPath (Symbol.def, (constQid cid))
  | (g_, NSDef cid) -> fmtConstPath (Symbol.def, (constQid cid))
  | (g_, FVar (name, _, _)) -> Str0 (Symbol.fvar name)
  | (g_, (Proj (Bidx k, i) as h_)) -> Str0 (Symbol.const (projName (g_, h_)))
  | (g_, (Proj (LVar (({ contents = None } as r), sk, (cid, t)), i) as h_))
      ->
      let n = lookuplvar r in
      ((fmtConstPath
          ((begin function
            | l0 ->
                Symbol.const
                  ((^) ((("#[" ^ l0) ^ n) ^ "]") projName (g_, h_)) end),
          (constQid cid)))
      (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *))
  | (g_, FgnConst (cs, conDec)) ->
      let name = I.conDecName conDec in
      (((begin match ((Names.constLookup (Names.Qid ([], name))), !noShadow)
               with
         | (Some _, false) -> Str0 (Symbol.const (("%" ^ name) ^ "%"))
         | _ -> Str0 (Symbol.const name) end))
      (* the user has re-defined this name *)(* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)) end
let rec evarArgs (g_, d, x_, s) =
  OpArgs (FX.Nonfix, [fmtEVar (g_, x_)], (subToSpine ((I.ctxLength g_), s)))
let rec evarArgs' (g_, d, x_, s) =
  OpArgs (FX.Nonfix, [fmtAVar (g_, x_)], (subToSpine ((I.ctxLength g_), s)))
let rec fst =
  begin function
  | (App (u1_, _), s) -> (u1_, s)
  | (SClo (s_, s'), s) -> fst (s_, (I.comp (s', s))) end
let rec snd =
  begin function
  | (App (u1_, s_), s) -> fst (s_, s)
  | (SClo (s_, s'), s) -> snd (s_, (I.comp (s', s))) end
let rec elide l =
  begin match !printLength with | None -> false | Some l' -> l > l' end
let ldots = sym "..."
let rec addots l =
  begin match !printLength with | None -> false | Some l' -> l = l' end
let rec parens ((fixity', fixity), fmt) =
  if FX.leq ((FX.prec fixity), (FX.prec fixity'))
  then begin F.Hbox [sym "("; fmt; sym ")"] end else begin fmt end
let rec eqFix =
  begin function
  | (Infix (p, FX.Left), Infix (p', FX.Left)) -> p = p'
  | (Infix (p, FX.Right), Infix (p', FX.Right)) -> p = p'
  | (Prefix p, Prefix p') -> p = p'
  | (Postfix p, Postfix p') -> p = p'
  | _ -> false end(* Nonfix should never be asked *)
(* Infix(_,None) should never be asked *)
let rec addAccum =
  begin function
  | (fmt, _, []) -> fmt
  | (fmt, Infix (_, FX.Left), accum) -> F.HVbox ([fmt] @ accum)
  | (fmt, Infix (_, FX.Right), accum) -> F.HVbox (accum @ [fmt])
  | (fmt, Prefix _, accum) -> F.HVbox (accum @ [fmt])
  | (fmt, Postfix _, accum) -> F.HVbox ([fmt] @ accum) end
let rec aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)
let rec fmtUni =
  begin function | I.Type -> sym "type" | I.Kind -> sym "kind" end
let rec fmtExpW =
  begin function
  | (g_, d, ctx, (Uni (l_), s)) -> aa (ctx, (fmtUni l_))
  | (g_, d, ctx, (Pi (((Dec (_, v1_) as d_), p_), v2_), s)) ->
      (((begin match p_ with
         | I.Maybe ->
             let d'_ = Names.decLUName (g_, d_) in
             ((fmtLevel
                 ((((I.Decl (g_, d'_)), d, ctx,
                     ((braces (g_, d, ((d'_, v2_), s))), (I.dot1 s))))
                 (* I.decSub (D', s) *)))
               (* could sometimes be EName *))
         | I.Meta ->
             let d'_ = Names.decLUName (g_, d_) in
             fmtLevel
               ((((I.Decl (g_, d'_)), d, ctx,
                   ((braces (g_, d, ((d'_, v2_), s))), (I.dot1 s))))
               (* I.decSub (D', s) *))
         | I.No ->
             fmtLevel
               ((((I.Decl (g_, d_)), d, ctx,
                   ((arrow ((I.EClo (v1_, I.shift)), v2_)), (I.dot1 s))))
               (* I.decSub (D, s) *)) end))
  (* if Pi is dependent but anonymous, invent name here *))
  | (g_, d, ctx, (Pi (((BDec _ as d_), p_), v2_), s)) ->
      let d'_ = Names.decLUName (g_, d_) in
      fmtLevel
        ((I.Decl (g_, d'_)), d, ctx,
          ((braces (g_, d, ((d'_, v2_), s))), (I.dot1 s)))
  | (g_, d, ctx, (Pi (((ADec _ as d_), p_), v2_), s)) ->
      let braces =
        OpArgs
          ((FX.Prefix binderPrec), [sym "["; sym "_"; sym "]"; F.Break],
            (IntSyn.App (v2_, IntSyn.Nil))) in
      ((fmtLevel ((I.Decl (g_, d_)), d, ctx, (braces, (I.dot1 s))))
        (*      val D' = Names.decLUName (G, D) *))
  | (g_, d, ctx, ((Root (r_) as u_), s)) ->
      fmtOpArgs (g_, d, ctx, (opargs (g_, d, r_)), s)
  | (g_, d, ctx, (Lam (d_, u_), s)) ->
      let d'_ = Names.decLUName (g_, d_) in
      fmtLevel
        ((((I.Decl (g_, d'_)), d, ctx,
            ((brackets (g_, d, ((d'_, u_), s))), (I.dot1 s))))
        (* I.decSub (D', s) *))
  | (g_, d, ctx, ((EVar _ as x_), s)) ->
      if !implicit
      then
        begin aa (ctx, (F.HVbox ((::) (fmtEVar (g_, x_)) fmtSub (g_, d, s)))) end
      else begin fmtOpArgs (g_, d, ctx, (evarArgs (g_, d, x_, s)), I.id) end
| (g_, d, ctx, ((AVar _ as x_), s)) ->
    if !implicit
    then
      begin aa (ctx, (F.HVbox ((::) (fmtAVar (g_, x_)) fmtSub (g_, d, s)))) end
    else begin fmtOpArgs (g_, d, ctx, (evarArgs' (g_, d, x_, s)), I.id) end
| (g_, d, ctx, ((FgnExp csfe as u_), s)) ->
    fmtExp (g_, d, ctx, ((I.FgnExpStd.ToInternal.apply csfe ()), s)) end
(* assume dereferenced during whnf *)(* assume dereferenced during whnf *)
(* I.Redex not possible *)(* s = id *)
(* -bp *)
let rec opargsImplicit (g_, d, (c_, s_)) =
  OpArgs (FX.Nonfix, [fmtCon (g_, c_)], s_)
let rec opargsImplicitInfix (g_, d, ((c_, s_) as r_)) =
  let fixity = fixityCon c_ in
  ((begin match fixity with
    | Infix _ -> opargsExplicit (g_, d, r_)
    | _ -> OpArgs (FX.Nonfix, [fmtCon (g_, c_)], s_) end)
  (* Can't have implicit arguments by invariant *))
let rec opargsExplicit (g_, d, ((c_, s_) as r_)) =
  let opFmt = fmtCon (g_, c_) in
  let fixity = fixityCon c_ in
  let rec oe =
    begin function
    | Exact (s'_) ->
        (begin match fixity with
         | FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], s'_)
         | Prefix _ -> OpArgs (fixity, [opFmt; F.Break], s'_)
         | Postfix _ -> OpArgs (fixity, [F.Break; opFmt], s'_)
         | Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.Space], s'_) end)
    | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root r_))
    | TooMany (s'_, S'') ->
        let opFmt' = fmtOpArgs (g_, d, noCtxt, (oe (Exact s'_)), I.id) in
        ((OpArgs (FX.Nonfix, [F.Hbox [sym "("; opFmt'; sym ")"]], S''))
          (* parens because juxtaposition has highest precedence *)
          (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)) end
    (* S'' - extra arguments *)(* S' - all non-implicit arguments *)
    (* extra arguments to infix operator *) in
  oe (dropImp ((impCon c_), s_, (argNumber fixity)))
let rec opargs (g_, d, r_) =
  if !implicit
  then begin (if !printInfix then begin opargsImplicitInfix (g_, d, r_) end
    else begin opargsImplicit (g_, d, r_) end) end
else begin opargsExplicit (g_, d, r_) end
let rec fmtOpArgs =
  begin function
  | (g_, d, ctx, (OpArgs (_, opFmts, s'_) as oa), s) ->
      ((if isNil s'_ then begin aa (ctx, (List.hd opFmts)) end
      else begin fmtLevel (g_, d, ctx, (oa, s)) end)
  (* opFmts = [fmtCon(G,C)] *))
  | (g_, d, ctx, EtaLong (u'_), s) -> fmtExpW (g_, d, ctx, (u'_, s)) end
let rec fmtSub (g_, d, s) = (::) (Str "[") fmtSub' (g_, d, 0, s)
let rec fmtSub' (g_, d, l, s) = if elide l then begin [ldots] end
  else begin fmtSub'' (g_, d, l, s) end
let rec fmtSub'' =
  begin function
  | (g_, d, l, Shift k) -> [Str ((^) "^" Int.toString k); Str "]"]
  | (g_, d, l, Dot (Idx k, s)) ->
      (::) (((::) (Str (Names.bvarName (g_, k))) Str ".") :: F.Break) fmtSub'
        (g_, d, (l + 1), s)
  | (g_, d, l, Dot (Exp (u_), s)) ->
      (::) (((::) (fmtExp (g_, (d + 1), noCtxt, (u_, I.id))) Str ".") ::
              F.Break)
        fmtSub' (g_, d, (l + 1), s) end
let rec fmtExp (g_, d, ctx, (u_, s)) =
  if exceeded (d, !printDepth) then begin sym "%%" end
  else begin fmtExpW (g_, d, ctx, (Whnf.whnf (u_, s))) end
let rec fmtSpine =
  begin function
  | (g_, d, l, (I.Nil, _)) -> []
  | (g_, d, l, (SClo (s_, s'), s)) ->
      fmtSpine (g_, d, l, (s_, (I.comp (s', s))))
  | (g_, d, l, (App (u_, s_), s)) -> ((if elide l then begin [] end
      else begin if addots l then begin [ldots] end
        else begin
          (::) (fmtExp (g_, (d + 1), appCtxt, (u_, s))) fmtSpine'
            (g_, d, l, (s_, s)) end end)
(* necessary? *)) end
let rec fmtSpine' =
  begin function
  | (g_, d, l, (I.Nil, _)) -> []
  | (g_, d, l, (SClo (s_, s'), s)) ->
      fmtSpine' (g_, d, l, (s_, (I.comp (s', s))))
  | (g_, d, l, (s_, s)) -> (::) F.Break fmtSpine (g_, d, (l + 1), (s_, s)) end
let rec fmtLevel =
  begin function
  | (g_, d, Ctxt (fixity', accum, l),
     (OpArgs ((FX.Nonfix as fixity), fmts, s_), s)) ->
      let atm = fmtSpine (g_, d, 0, (s_, s)) in
      ((addAccum
          ((parens ((fixity', fixity), (F.HVbox ((fmts @ [F.Break]) @ atm)))),
            fixity', accum))
        (* atm must not be empty, otherwise bug below *)
        (* F.HVbox doesn't work if last item of HVbox is F.Break *)
        (* possible improvement along the following lines: *)(*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *))
  | (g_, d, Ctxt (fixity', accum, l),
     (OpArgs ((Infix (p, FX.Left) as fixity), fmts, s_), s)) ->
      let accMore = eqFix (fixity, fixity') in
      let rhs = if accMore && (elide l) then begin [] end
        else begin if accMore && (addots l) then begin fmts @ [ldots] end
          else begin
            fmts @
              [fmtExp
                 (g_, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), [], 0)),
                   (snd (s_, s)))] end end in
if accMore
then
  begin fmtExp
          (g_, d, (Ctxt (fixity, (rhs @ accum), (l + 1))), (fst (s_, s))) end
  else begin
    (let both = fmtExp (g_, d, (Ctxt (fixity, rhs, 0)), (fst (s_, s))) in
     addAccum ((parens ((fixity', fixity), both)), fixity', accum)) end
| (g_, d, Ctxt (fixity', accum, l),
   (OpArgs ((Infix (p, FX.Right) as fixity), fmts, s_), s)) ->
    let accMore = eqFix (fixity, fixity') in
    let lhs = if accMore && (elide l) then begin [] end
      else begin if accMore && (addots l) then begin [ldots] @ fmts end
        else begin
          [fmtExp
             (g_, (d + 1), (Ctxt ((FX.Infix (p, FX.None)), [], 0)),
               (fst (s_, s)))]
            @ fmts end end in
if accMore
then
begin fmtExp (g_, d, (Ctxt (fixity, (accum @ lhs), (l + 1))), (snd (s_, s))) end
else begin
  (let both = fmtExp (g_, d, (Ctxt (fixity, lhs, 0)), (snd (s_, s))) in
   addAccum ((parens ((fixity', fixity), both)), fixity', accum)) end
| (g_, d, Ctxt (fixity', accum, l),
   (OpArgs ((Infix (_, FX.None) as fixity), fmts, s_), s)) ->
    let lhs = fmtExp (g_, (d + 1), (Ctxt (fixity, [], 0)), (fst (s_, s))) in
    let rhs = fmtExp (g_, (d + 1), (Ctxt (fixity, [], 0)), (snd (s_, s))) in
    addAccum
      ((parens ((fixity', fixity), (F.HVbox (([lhs] @ fmts) @ [rhs])))),
        fixity', accum)
| (g_, d, Ctxt (fixity', accum, l),
   (OpArgs ((Prefix _ as fixity), fmts, s_), s)) ->
    let accMore = eqFix (fixity', fixity) in
    let pfx = if accMore && (elide l) then begin [] end
      else begin if accMore && (addots l) then begin [ldots; F.Break] end
        else begin fmts end end in
if accMore
then
begin fmtExp (g_, d, (Ctxt (fixity, (accum @ pfx), (l + 1))), (fst (s_, s))) end
else begin
  (let whole = fmtExp (g_, d, (Ctxt (fixity, pfx, 0)), (fst (s_, s))) in
   addAccum ((parens ((fixity', fixity), whole)), fixity', accum)) end
| (g_, d, Ctxt (fixity', accum, l),
   (OpArgs ((Postfix _ as fixity), fmts, s_), s)) ->
    let accMore = eqFix (fixity', fixity) in
    let pfx = if accMore && (elide l) then begin [] end
      else begin if accMore && (addots l) then begin [F.Break; ldots] end
        else begin fmts end end in
if accMore
then
begin fmtExp (g_, d, (Ctxt (fixity, (pfx @ accum), (l + 1))), (fst (s_, s))) end
else begin
  (let whole = fmtExp (g_, d, (Ctxt (fixity, pfx, 0)), (fst (s_, s))) in
   addAccum ((parens ((fixity', fixity), whole)), fixity', accum)) end end
let rec braces (g_, d, ((d_, v_), s)) =
  OpArgs
    ((FX.Prefix binderPrec),
      [sym "{"; fmtDec (g_, d, (d_, s)); sym "}"; F.Break],
      (IntSyn.App (v_, IntSyn.Nil)))
let rec brackets (g_, d, ((d_, u_), s)) =
  OpArgs
    ((FX.Prefix binderPrec),
      [sym "["; fmtDec (g_, d, (d_, s)); sym "]"; F.Break],
      (IntSyn.App (u_, IntSyn.Nil)))
let rec fmtDec =
  begin function
  | (g_, d, (Dec (x, v_), s)) ->
      F.HVbox
        [Str0 (Symbol.bvar (nameOf x));
        sym ":";
        fmtExp (g_, (d + 1), noCtxt, (v_, s))]
  | (g_, d, (BDec (x, (cid, t)), s)) ->
      let (Gsome, Gblock) = I.constBlock cid in
      F.HVbox
        ((@) [Str0 (Symbol.const (nameOf x)); sym ":"] fmtDecList'
           (g_, (Gblock, (I.comp (t, s)))))
  | (g_, d, (ADec (x, _), s)) ->
      F.HVbox [Str0 (Symbol.bvar (nameOf x)); sym ":_"]
  | (g_, d, (NDec (Some name), s)) -> F.HVbox [sym name] end(* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
(* alternative with more whitespace *)
let rec fmtDecList' =
  begin function
  | (g0_, ([], s)) -> []
  | (g0_, ((d_)::[], s)) ->
      ((::) ((::) (sym "{") fmtDec (g0_, 0, (d_, s))) sym "}") :: []
  | (g0_, ((d_)::l_, s)) ->
      (::) (((::) ((::) (sym "{") fmtDec (g0_, 0, (d_, s))) sym "}") ::
              F.Break)
        fmtDecList' ((I.Decl (g0_, d_)), (l_, (I.dot1 s))) end
let rec skipI =
  begin function
  | (0, g_, v_) -> (g_, v_)
  | (i, g_, Pi ((d_, _), v_)) ->
      skipI ((i - 1), (I.Decl (g_, (Names.decEName (g_, d_)))), v_) end
let rec skipI2 =
  begin function
  | (0, g_, v_, u_) -> (g_, v_, u_)
  | (i, g_, Pi ((d_, _), v_), Lam (d'_, u_)) ->
      skipI2 ((i - 1), (I.Decl (g_, (Names.decEName (g_, d'_)))), v_, u_) end
let rec ctxToDecList =
  begin function
  | (I.Null, l_) -> l_
  | (Decl (g_, d_), l_) -> ctxToDecList (g_, (d_ :: l_)) end
let rec fmtDecList =
  begin function
  | (g0_, []) -> []
  | (g0_, (d_)::[]) ->
      ((::) ((::) (sym "{") fmtDec (g0_, 0, (d_, I.id))) sym "}") :: []
  | (g0_, (d_)::l_) ->
      (::) (((::) ((::) (sym "{") fmtDec (g0_, 0, (d_, I.id))) sym "}") ::
              F.Break)
        fmtDecList ((I.Decl (g0_, d_)), l_) end
let rec fmtCtx (g0_, g_) = fmtDecList (g0_, (ctxToDecList (g_, [])))
let rec fmtBlock =
  begin function
  | (I.Null, Lblock) ->
      [sym "block"; F.Break] @ (fmtDecList (I.Null, Lblock))
  | (Gsome, Lblock) ->
      [F.HVbox ([sym "some"; F.Space] @ (fmtCtx (I.Null, Gsome)));
      F.Break;
      F.HVbox ([sym "block"; F.Space] @ (fmtDecList (Gsome, Lblock)))] end
let rec fmtConDec =
  begin function
  | (hide, (ConDec (_, _, imp, _, v_, l_) as condec)) ->
      let qid = Names.conDecQid condec in
      let _ = Names.varReset IntSyn.Null in
      let (g_, v_) = if hide then begin skipI (imp, I.Null, v_) end
        else begin (I.Null, v_) end in
      let Vfmt = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
      F.HVbox
        [fmtConstPath (Symbol.const, qid);
        F.Space;
        sym ":";
        F.Break;
        Vfmt;
        sym "."]
  | (hide, (SkoDec (_, _, imp, v_, l_) as condec)) ->
      let qid = Names.conDecQid condec in
      let _ = Names.varReset IntSyn.Null in
      let (g_, v_) = if hide then begin skipI (imp, I.Null, v_) end
        else begin (I.Null, v_) end in
      let Vfmt = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
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
| (hide, (BlockDef (_, _, w_) as condec)) ->
    let qid = Names.conDecQid condec in
    let _ = Names.varReset IntSyn.Null in
    F.HVbox
      ([sym "%block";
       F.Break;
       fmtConstPath (Symbol.label, qid);
       F.Space;
       sym "=";
       F.Break] @ ((formatWorlds (T.Worlds w_)) :: [sym "."]))
| (hide, (ConDef (_, _, imp, u_, v_, l_, _) as condec)) ->
    let qid = Names.conDecQid condec in
    let _ = Names.varReset IntSyn.Null in
    let (g_, v_, u_) = if hide then begin skipI2 (imp, I.Null, v_, u_) end
      else begin (I.Null, v_, u_) end in
    let Vfmt = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
    let Ufmt = fmtExp (g_, 0, noCtxt, (u_, I.id)) in
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
| (hide, (AbbrevDef (_, _, imp, u_, v_, l_) as condec)) ->
    let qid = Names.conDecQid condec in
    let _ = Names.varReset IntSyn.Null in
    let (g_, v_, u_) = if hide then begin skipI2 (imp, I.Null, v_, u_) end
      else begin (I.Null, v_, u_) end in
    let Vfmt = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
    let Ufmt = fmtExp (g_, 0, noCtxt, (u_, I.id)) in
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
*)) end
(* reset variable names in between to align names of type V and definition U *)
(* reset variable names in between to align names of type V and definition U *)
let rec fmtCnstr =
  begin function
  | I.Solved -> [Str "Solved Constraint"]
  | Eqn (g_, u1_, u2_) ->
      let g'_ = Names.ctxLUName g_ in
      [F.HVbox
         [fmtExp (g'_, 0, noCtxt, (u1_, I.id));
         F.Break;
         sym "=";
         F.Space;
         fmtExp (g'_, 0, noCtxt, (u2_, I.id))]]
  | FgnCnstr ((cs, _) as csfc) ->
      let rec fmtExpL =
        begin function
        | [] -> [Str "Empty Constraint"]
        | (g_, u_)::[] ->
            [fmtExp ((Names.ctxLUName g_), 0, noCtxt, (u_, I.id))]
        | (g_, u_)::expL ->
            (@) [fmtExp ((Names.ctxLUName g_), 0, noCtxt, (u_, I.id));
                Str ";";
                F.Break]
              fmtExpL expL end in
    fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ()) end
let rec fmtCnstrL =
  begin function
  | [] -> [Str "Empty Constraint"]
  | { contents = Cnstr }::[] -> (fmtCnstr Cnstr) @ [Str "."]
  | { contents = Cnstr }::cnstrL ->
      ((fmtCnstr Cnstr) @ [Str ";"; F.Break]) @ (fmtCnstrL cnstrL) end
let rec abstractLam =
  begin function
  | (I.Null, u_) -> u_
  | (Decl (g_, d_), u_) -> abstractLam (g_, (I.Lam (d_, u_))) end
let rec fmtNamedEVar =
  begin function
  | ((EVar (_, g_, _, _) as u_), name) ->
      let u'_ = abstractLam (g_, u_) in
      F.HVbox
        [Str0 (Symbol.evar name);
        F.Space;
        sym "=";
        F.Break;
        fmtExp (I.Null, 0, noCtxt, (u'_, I.id))]
  | (u_, name) ->
      F.HVbox
        [Str0 (Symbol.evar name);
        F.Space;
        sym "=";
        F.Break;
        fmtExp (I.Null, 0, noCtxt, (u_, I.id))] end(* used for proof term variables in queries *)
let rec fmtEVarInst =
  begin function
  | [] -> [Str "Empty Substitution"]
  | (u_, name)::[] -> [fmtNamedEVar (u_, name)]
  | (u_, name)::xs_ ->
      (::) (((::) (fmtNamedEVar (u_, name)) Str ";") :: F.Break) fmtEVarInst
        xs_ end
let rec collectEVars =
  begin function
  | ([], xs_) -> xs_
  | ((u_, _)::Xnames, xs_) ->
      collectEVars
        (Xnames, (Abstract.collectEVars (I.Null, (u_, I.id), xs_))) end
let rec eqCnstr r1 r2 = r1 = r2
let rec mergeConstraints =
  begin function
  | ([], cnstrs2) -> cnstrs2
  | (cnstr::cnstrs1, cnstrs2) ->
      if List.exists (eqCnstr cnstr) cnstrs2
      then begin mergeConstraints (cnstrs1, cnstrs2) end
      else begin cnstr :: (mergeConstraints (cnstrs1, cnstrs2)) end end
let rec collectConstraints =
  begin function
  | [] -> []
  | (EVar ({ contents = None }, _, _, cnstrs))::xs_ ->
      mergeConstraints
        ((Constraints.simplify !cnstrs), (collectConstraints xs_))
  | _::xs_ -> collectConstraints xs_ end
let rec formatDec (g_, d_) = fmtDec (g_, 0, (d_, I.id))
let rec formatDecList (g_, d_) = F.HVbox (fmtDecList (g_, d_))
let rec formatDecList' (g_, (d_, s)) = F.HVbox (fmtDecList' (g_, (d_, s)))
let rec formatExp (g_, u_) = fmtExp (g_, 0, noCtxt, (u_, I.id))
let rec formatSpine (g_, s_) = fmtSpine (g_, 0, 0, (s_, I.id))
let rec formatConDec condec = fmtConDec (false, condec)
let rec formatConDecI condec = fmtConDec (true, condec)
let rec formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
let rec formatCnstrs cnstrL = F.Vbox0 0 1 (fmtCnstrL cnstrL)
let rec formatCtx (g0_, g_) = F.HVbox (fmtCtx (g0_, g_))
let rec decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_))
let rec expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_))
let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
let rec cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
let rec ctxToString (g0_, g_) = F.makestring_fmt (formatCtx (g0_, g_))
let rec evarInstToString (Xnames) =
  F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
let rec evarCnstrsToStringOpt (Xnames) =
  let ys_ = collectEVars (Xnames, []) in
  let cnstrL = collectConstraints ys_ in
  ((begin match cnstrL with | [] -> None | _ -> Some (cnstrsToString cnstrL) end)
    (* collect EVars in instantiations *))
let rec printSgn () =
  IntSyn.sgnApp
    (begin function
     | cid ->
         (begin print
                  (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
          print "\n" end) end)
let formatWorlds = formatWorlds
let worldsToString = worldsToString end



module SymbolAscii = (SymbolAscii)(struct  end)
module SymbolTeX = (SymbolTeX)(struct  end)
module Print =
  (Print)(struct
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolAscii
               end)
module ClausePrint =
  (ClausePrint)(struct
                       module Whnf = Whnf
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = Print
                       module Symbol = SymbolAscii
                     end)
module PrintTeX =
  (Print)(struct
                 module Whnf = Whnf
                 module Abstract = Abstract
                 module Constraints = Constraints
                 module Names = Names
                 module Formatter' = Formatter
                 module Symbol = SymbolTeX
               end)
module ClausePrintTeX =
  (ClausePrint)(struct
                       module Whnf = Whnf
                       module Constraints = Constraints
                       module Names = Names
                       module Formatter' = Formatter
                       module Print = PrintTeX
                       module Symbol = SymbolTeX
                     end)
module PrintTwega =
  (PrintTwega)(struct
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end)
module PrintXML =
  (PrintXML)(struct
                    module Whnf = Whnf
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Names = Names
                    module Formatter' = Formatter
                  end)
module PrintOMDoc =
  (PrintOMDoc)(struct
                      module Whnf = Whnf
                      module Abstract = Abstract
                      module Constraints = Constraints
                      module Names = Names
                      module Formatter' = Formatter
                    end)