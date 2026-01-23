module type EXTSYN  =
  sig
    type nonrec term
    type nonrec dec
    val lcid : (string list * string * Paths.region) -> term
    val ucid : (string list * string * Paths.region) -> term
    val quid : (string list * string * Paths.region) -> term
    val scon : (string * Paths.region) -> term
    val evar : (string * Paths.region) -> term
    val fvar : (string * Paths.region) -> term
    val typ : Paths.region -> term
    val arrow : (term * term) -> term
    val backarrow : (term * term) -> term
    val pi : (dec * term) -> term
    val lam : (dec * term) -> term
    val app : (term * term) -> term
    val hastype : (term * term) -> term
    val omitted : Paths.region -> term
    val dec : (string option * term * Paths.region) -> dec
    val dec0 : (string option * Paths.region) -> dec
  end
module type RECON_TERM  =
  sig
    include EXTSYN
    exception Error of string 
    val resetErrors : string -> unit
    val checkErrors : Paths.region -> unit
    type traceMode_ =
      | Progressive 
      | Omniscient 
    val trace : bool ref
    val traceMode : traceMode_ ref
    type nonrec job
    val jnothing : job
    val jand : (job * job) -> job
    val jwithctx : (dec IntSyn.ctx_ * job) -> job
    val jterm : term -> job
    val jclass : term -> job
    val jof : (term * term) -> job
    val jof' : (term * IntSyn.exp_) -> job
    type job_ =
      | JNothing 
      | JAnd of (job_ * job_) 
      | JWithCtx of (IntSyn.dec_ IntSyn.ctx_ * job_) 
      | JTerm of ((IntSyn.exp_ * Paths.occExp) * IntSyn.exp_ * IntSyn.uni_) 
      | JClass of ((IntSyn.exp_ * Paths.occExp) * IntSyn.uni_) 
      | JOf of ((IntSyn.exp_ * Paths.occExp) * (IntSyn.exp_ * Paths.occExp) *
      IntSyn.uni_) 
    val recon : job -> job_
    val reconQuery : job -> job_
    val reconWithCtx : (IntSyn.dctx * job) -> job_
    val reconQueryWithCtx : (IntSyn.dctx * job) -> job_
    val termRegion : term -> Paths.region
    val decRegion : dec -> Paths.region
    val ctxRegion : dec IntSyn.ctx_ -> Paths.region option
    val internalInst : 'a -> 'b
    val externalInst : 'a -> 'b
  end


module ReconTerm(ReconTerm:sig
                             module Names : NAMES
                             module Approx : APPROX
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Abstract : ABSTRACT
                             module Print : PRINT
                             module StringTree : TABLE
                             module Msg : MSG
                           end) : RECON_TERM =
  struct
    module F = Print.Formatter
    module Apx = Approx
    let (delayedList : (unit -> unit) list ref) = ref []
    let rec clearDelayed () = delayedList := []
    let rec addDelayed f = (delayedList := f) :: !delayedList
    let rec runDelayed () =
      let rec run' =
        begin function | [] -> () | h::t -> (begin run' t; h () end) end in
    run' !delayedList
  exception Error of string 
  let errorCount = ref 0
  let errorFileName = ref "no file"
  let errorThreshold = ref (Some 20)
  let rec exceeds =
    begin function | (i, None) -> false | (i, Some j) -> i > j end
let rec resetErrors fileName =
  begin errorCount := 0; errorFileName := fileName end
let rec die r =
  raise
    (Error
       (Paths.wrap
          (r,
            (((((^) " " Int.toString !errorCount) ^ " error") ^
                (if !errorCount > 1 then begin "s" end else begin "" end)) ^
          " found"))))
let rec checkErrors r = if !errorCount > 0 then begin die r end
  else begin () end
let rec chatterOneNewline () =
  if (!Global.chatter = 1) && (!errorCount = 1)
  then begin Msg.message "\n" end else begin () end
let rec fatalError (r, msg) =
  begin ((!) ((:=) errorCount) errorCount) + 1;
  chatterOneNewline ();
  Msg.message (((^) (!errorFileName ^ ":") Paths.wrap (r, msg)) ^ "\n");
  die r end
let rec error (r, msg) =
  begin ((!) ((:=) errorCount) errorCount) + 1;
  chatterOneNewline ();
  Msg.message (((^) (!errorFileName ^ ":") Paths.wrap (r, msg)) ^ "\n");
  if exceeds (!errorCount, !errorThreshold) then begin die r end
  else begin () end end
let rec formatExp (g_, u_) =
  begin try Print.formatExp (g_, u_)
  with | Names.Unprintable -> F.String "%_unprintable_%" end
let queryMode = ref false
open IntSyn
let rec headConDec =
  begin function
  | Const c -> sgnLookup c
  | Skonst c -> sgnLookup c
  | Def d -> sgnLookup d
  | NSDef d -> sgnLookup d
  | FgnConst (_, cd) -> cd end
let rec lowerTypeW =
  begin function
  | (g_, (Pi ((d_, _), v_), s)) ->
      let d'_ = decSub (d_, s) in
      lowerType ((Decl (g_, d'_)), (v_, (dot1 s)))
  | (g_, vs_) -> (g_, (EClo vs_)) end
let rec lowerType (g_, vs_) = lowerTypeW (g_, (Whnf.whnfExpandDef vs_))
let rec raiseType =
  begin function
  | (Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (Pi ((d_, Maybe), v_))) end
let (evarApxTable : Apx.exp_ StringTree.table_) = StringTree.new_ 0
let (fvarApxTable : Apx.exp_ StringTree.table_) = StringTree.new_ 0
let (fvarTable : IntSyn.exp_ StringTree.table_) = StringTree.new_ 0
let rec varReset () =
  begin StringTree.clear evarApxTable;
  StringTree.clear fvarApxTable;
  StringTree.clear fvarTable end
let rec getEVarTypeApx name =
  begin match StringTree.lookup evarApxTable name with
  | Some (v_) -> v_
  | None ->
      (begin match Names.getEVarOpt name with
       | Some (EVar (_, _, v_, _)) ->
           let (((v'_, _))(* Type *)) = Apx.classToApx v_ in
           (begin StringTree.insert evarApxTable (name, v'_); v'_ end)
      | None ->
          let v_ = Apx.newCVar () in
          (begin StringTree.insert evarApxTable (name, v_); v_ end) end) end
let rec getFVarTypeApx name =
  begin match StringTree.lookup fvarApxTable name with
  | Some (v_) -> v_
  | None ->
      let v_ = Apx.newCVar () in
      (begin StringTree.insert fvarApxTable (name, v_); v_ end) end
let rec getEVar (name, allowed) =
  begin match Names.getEVarOpt name with
  | Some (EVar (_, g_, v_, _) as x_) -> (x_, (raiseType (g_, v_)))
  | None ->
      let v_ = Option.valOf (StringTree.lookup evarApxTable name) in
      let v'_ = Apx.apxToClass (IntSyn.Null, v_, Apx.Type, allowed) in
      let (G'', V'') = lowerType (IntSyn.Null, (v'_, IntSyn.id)) in
      let x_ = IntSyn.newEVar (G'', V'') in
      (begin Names.addEVar (x_, name); (x_, v'_) end) end
let rec getFVarType (name, allowed) =
  begin match StringTree.lookup fvarTable name with
  | Some (v_) -> v_
  | None ->
      let v_ = Option.valOf (StringTree.lookup fvarApxTable name) in
      let v'_ = Apx.apxToClass (IntSyn.Null, v_, Apx.Type, allowed) in
      (begin StringTree.insert fvarTable (name, v'_); v'_ end) end
type term =
  | internal of (IntSyn.exp_ * IntSyn.exp_ * Paths.region)
  [@sml.renamed "internal"][@sml.renamed "internal"]
  | constant of (IntSyn.head_ * Paths.region)
  [@sml.renamed "constant"][@sml.renamed "constant"]
  | bvar of (int * Paths.region) [@sml.renamed "bvar"][@sml.renamed "bvar"]
  | evar of (string * Paths.region)
  [@sml.renamed "evar"][@sml.renamed "evar"]
  | fvar of (string * Paths.region)
  [@sml.renamed "fvar"][@sml.renamed "fvar"]
  | typ of Paths.region [@sml.renamed "typ"][@sml.renamed "typ"]
  | arrow of (term * term) [@sml.renamed "arrow"][@sml.renamed "arrow"]
  | pi of (dec * term) [@sml.renamed "pi"][@sml.renamed "pi"]
  | lam of (dec * term) [@sml.renamed "lam"][@sml.renamed "lam"]
  | app of (term * term) [@sml.renamed "app"][@sml.renamed "app"]
  | hastype of (term * term)
  [@sml.renamed "hastype"][@sml.renamed "hastype"]
  | mismatch of (term * term * string * string)
  [@sml.renamed "mismatch"][@sml.renamed "mismatch"]
  | omitted of Paths.region [@sml.renamed "omitted"][@sml.renamed "omitted"]
  | lcid of (string list * string * Paths.region)
  [@sml.renamed "lcid"][@sml.renamed "lcid"]
  | ucid of (string list * string * Paths.region)
  [@sml.renamed "ucid"][@sml.renamed "ucid"]
  | quid of (string list * string * Paths.region)
  [@sml.renamed "quid"][@sml.renamed "quid"]
  | scon of (string * Paths.region)
  [@sml.renamed "scon"][@sml.renamed "scon"]
  | omitapx of (Apx.exp_ * Apx.exp_ * Apx.uni_ * Paths.region)
  [@sml.renamed "omitapx"][@sml.renamed "omitapx"]
  | omitexact of (IntSyn.exp_ * IntSyn.exp_ * Paths.region)
  [@sml.renamed "omitexact"][@sml.renamed "omitexact"]
and dec =
  | dec of (string option * term * Paths.region)
  [@sml.renamed "dec"][@sml.renamed "dec"]
let rec backarrow (tm1, tm2) = arrow (tm2, tm1)
let rec dec0 (nameOpt, r) = dec (nameOpt, (omitted r), r)
type job =
  | jnothing [@sml.renamed "jnothing"][@sml.renamed "jnothing"]
  | jand of (job * job) [@sml.renamed "jand"][@sml.renamed "jand"]
  | jwithctx of (dec IntSyn.ctx_ * job)
  [@sml.renamed "jwithctx"][@sml.renamed "jwithctx"]
  | jterm of term [@sml.renamed "jterm"][@sml.renamed "jterm"]
  | jclass of term [@sml.renamed "jclass"][@sml.renamed "jclass"]
  | jof of (term * term) [@sml.renamed "jof"][@sml.renamed "jof"]
  | jof' of (term * IntSyn.exp_) [@sml.renamed "jof'"][@sml.renamed "jof'"]
let rec termRegion =
  begin function
  | internal (u_, v_, r) -> r
  | constant (h_, r) -> r
  | bvar (k, r) -> r
  | evar (name, r) -> r
  | fvar (name, r) -> r
  | typ r -> r
  | arrow (tm1, tm2) -> Paths.join ((termRegion tm1), (termRegion tm2))
  | pi (tm1, tm2) -> Paths.join ((decRegion tm1), (termRegion tm2))
  | lam (tm1, tm2) -> Paths.join ((decRegion tm1), (termRegion tm2))
  | app (tm1, tm2) -> Paths.join ((termRegion tm1), (termRegion tm2))
  | hastype (tm1, tm2) -> Paths.join ((termRegion tm1), (termRegion tm2))
  | mismatch (tm1, tm2, _, _) -> termRegion tm2
  | omitted r -> r
  | lcid (_, _, r) -> r
  | ucid (_, _, r) -> r
  | quid (_, _, r) -> r
  | scon (_, r) -> r
  | omitapx (u_, v_, l_, r) -> r
  | omitexact (u_, v_, r) -> r end
let rec decRegion (dec (name, tm, r)) = r
let rec ctxRegion =
  begin function
  | IntSyn.Null -> None
  | Decl (g, tm) -> ctxRegion' (g, (decRegion tm)) end
let rec ctxRegion' =
  begin function
  | (IntSyn.Null, r) -> Some r
  | (Decl (g, tm), r) -> ctxRegion' (g, (Paths.join (r, (decRegion tm)))) end
open Apx
type ctx_ = IntSyn.ctx_
type dec_ =
  | Dec of (string option * exp_) 
  | NDec of string option 
let rec filterLevel (tm, l_, max, msg) =
  let notGround = makeGroundUni l_ in
  let Level i = whnfUni l_ in
  if i > max
  then begin fatalError ((termRegion tm), ("Level too high\n" ^ msg)) end
    else begin
      if notGround
      then
        begin error
                ((termRegion tm),
                  (((("Ambiguous level\n" ^
                        "The level of this term could not be inferred\n")
                       ^ "Defaulting to ")
                      ^
                      (begin match i with
                       | 1 -> "object"
                       | 2 -> "type family"
                       | 3 -> "kind" end)) ^ " level")) end
    else begin () end end
let rec findOmitted (g_, qid, r) =
  begin error
          (r,
            ((^) "Undeclared identifier " Names.qidToString
               (valOf (Names.constUndef qid))));
  omitted r end
let rec findBVar' =
  begin function
  | (Null, name, k) -> None
  | (Decl (g_, Dec (None, _)), name, k) -> findBVar' (g_, name, (k + 1))
  | (Decl (g_, NDec _), name, k) -> findBVar' (g_, name, (k + 1))
  | (Decl (g_, Dec (Some name', _)), name, k) ->
      if name = name' then begin Some k end
      else begin findBVar' (g_, name, (k + 1)) end end
let rec findBVar fc (g_, qid, r) =
  begin match Names.unqualified qid with
  | None -> fc (g_, qid, r)
  | Some name ->
      (begin match findBVar' (g_, name, 1) with
       | None -> fc (g_, qid, r)
       | Some k -> bvar (k, r) end) end
let rec findConst fc (g_, qid, r) =
  begin match Names.constLookup qid with
  | None -> fc (g_, qid, r)
  | Some cid ->
      (begin match IntSyn.sgnLookup cid with
       | ConDec _ -> constant ((IntSyn.Const cid), r)
       | ConDef _ -> constant ((IntSyn.Def cid), r)
       | AbbrevDef _ -> constant ((IntSyn.NSDef cid), r)
       | _ ->
           (begin error
                    (r,
                      (((^) ("Invalid identifier\n" ^ "Identifier `")
                          Names.qidToString qid)
                         ^ "' is not a constant, definition or abbreviation"));
            omitted r end) end) end
let rec findCSConst fc (g_, qid, r) =
  begin match Names.unqualified qid with
  | None -> fc (g_, qid, r)
  | Some name ->
      (begin match CSManager.parse name with
       | None -> fc (g_, qid, r)
       | Some (cs, conDec) -> constant ((IntSyn.FgnConst (cs, conDec)), r) end) end
let rec findEFVar fc (g_, qid, r) =
  begin match Names.unqualified qid with
  | None -> fc (g_, qid, r)
  | Some name -> (if !queryMode then begin evar end else begin fvar end)
  (name, r) end
let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x
let rec findUCID x =
  findBVar (findConst (findCSConst (findEFVar findOmitted))) x
let rec findQUID x = findConst (findCSConst findOmitted) x
let rec inferApx =
  begin function
  | (g_, (internal (u_, v_, r) as tm)) ->
      let (u'_, v'_, l'_) = exactToApx (u_, v_) in (tm, u'_, v'_, l'_)
  | (g_, (lcid (ids, name, r) as tm)) ->
      let qid = Names.Qid (ids, name) in
      inferApx (g_, (findLCID (g_, qid, r)))
  | (g_, (ucid (ids, name, r) as tm)) ->
      let qid = Names.Qid (ids, name) in
      inferApx (g_, (findUCID (g_, qid, r)))
  | (g_, (quid (ids, name, r) as tm)) ->
      let qid = Names.Qid (ids, name) in
      inferApx (g_, (findQUID (g_, qid, r)))
  | (g_, (scon (name, r) as tm)) ->
      (begin match CSManager.parse name with
       | None ->
           (begin error (r, "Strings unsupported in current signature");
            inferApx (g_, (omitted r)) end)
      | Some (cs, conDec) ->
          inferApx (g_, (constant ((IntSyn.FgnConst (cs, conDec)), r))) end)
  | (g_, (constant (h_, r) as tm)) ->
      let cd = headConDec h_ in
      let (u'_, v'_, l'_) =
        exactToApx ((IntSyn.Root (h_, IntSyn.Nil)), (IntSyn.conDecType cd)) in
      let rec dropImplicit =
        begin function
        | (v_, 0) -> v_
        | (Arrow (_, v_), i) -> dropImplicit (v_, (i - 1)) end in
      let V'' = dropImplicit (v'_, (IntSyn.conDecImp cd)) in
      (tm, u'_, V'', l'_)
| (g_, (bvar (k, r) as tm)) ->
    let Dec (_, v_) = IntSyn.ctxLookup (g_, k) in (tm, Undefined, v_, Type)
| (g_, (evar (name, r) as tm)) ->
    (tm, Undefined, (getEVarTypeApx name), Type)
| (g_, (fvar (name, r) as tm)) ->
    (tm, Undefined, (getFVarTypeApx name), Type)
| (g_, (typ r as tm)) -> (tm, (Uni Type), (Uni Kind), Hyperkind)
| (g_, arrow (tm1, tm2)) ->
    let l_ = newLVar () in
    let (tm1', v1_) =
      checkApx
        (g_, tm1, (Uni Type), Kind, "Left-hand side of arrow must be a type") in
    let (tm2', v2_) =
      checkApx
        (g_, tm2, (Uni l_), (Next l_),
          "Right-hand side of arrow must be a type or a kind") in
    ((arrow (tm1', tm2')), (Arrow (v1_, v2_)), (Uni l_), (Next l_))
| (g_, pi (tm1, tm2)) ->
    let (tm1', (Dec (_, v1_) as d_)) = inferApxDec (g_, tm1) in
    let l_ = newLVar () in
    let (tm2', v2_) =
      checkApx
        ((Decl (g_, d_)), tm2, (Uni l_), (Next l_),
          "Body of pi must be a type or a kind") in
    ((pi (tm1', tm2')), (Arrow (v1_, v2_)), (Uni l_), (Next l_))
| (g_, (lam (tm1, tm2) as tm)) ->
    let (tm1', (Dec (_, v1_) as d_)) = inferApxDec (g_, tm1) in
    let (tm2', u2_, v2_, l2_) = inferApx ((Decl (g_, d_)), tm2) in
    ((lam (tm1', tm2')), u2_, (Arrow (v1_, v2_)), l2_)
| (g_, (app (tm1, tm2) as tm)) ->
    let l_ = newLVar () in
    let Va = newCVar () in
    let Vr = newCVar () in
    let (tm1', u1_) =
      checkApx
        (g_, tm1, (Arrow (Va, Vr)), l_,
          "Non-function was applied to an argument") in
    let (tm2', _) =
      checkApx
        (g_, tm2, Va, Type,
          "Argument type did not match function domain type") in
    ((((app (tm1', tm2')), u1_, Vr, l_))
      (* probably a confusing message if the problem is the level: *))
| (g_, (hastype (tm1, tm2) as tm)) ->
    let l_ = newLVar () in
    let (tm2', v2_) =
      checkApx
        (g_, tm2, (Uni l_), (Next l_),
          "Right-hand side of ascription must be a type or a kind") in
    let (tm1', u1_) = checkApx (g_, tm1, v2_, l_, "Ascription did not hold") in
    let _ =
      addDelayed
        (begin function
         | () ->
             filterLevel
               (tm, l_, 2,
                 "Ascription can only be applied to objects and type families") end) in
    ((hastype (tm1', tm2')), u1_, v2_, l_)
| (g_, omitted r) ->
    let l_ = newLVar () in
    let v_ = newCVar () in
    let u_ = newCVar () in ((((omitapx (u_, v_, l_, r)), u_, v_, l_))
      (* guaranteed not to be used if L is type *)) end
let rec checkApx (g_, tm, v_, l_, location_msg) =
  let (tm', u'_, v'_, l'_) = inferApx (g_, tm) in
  begin try begin matchUni (l_, l'_); match_ (v_, v'_); (tm', u'_) end
    with
    | Unify problem_msg ->
        let r = termRegion tm in
        let (tm'', U'') = checkApx (g_, (omitted r), v_, l_, location_msg) in
        let _ =
          addDelayed
            (begin function | () -> (begin makeGroundUni l'_; () end) end) in
        ((((mismatch (tm', tm'', location_msg, problem_msg)), U''))
          (* just in case *)) end
let rec inferApxDec (g_, dec (name, tm, r)) =
  let (tm', v1_) =
    checkApx
      (g_, tm, (Uni Type), Kind, "Classifier in declaration must be a type") in
  let d_ = Dec (name, v1_) in ((dec (name, tm', r)), d_)
let rec inferApxJob =
  begin function
  | (g_, jnothing) -> jnothing
  | (g_, jand (j1, j2)) ->
      jand ((inferApxJob (g_, j1)), (inferApxJob (g_, j2)))
  | (g_, jwithctx (g, j)) ->
      let rec ia =
        begin function
        | Null -> (g_, Null)
        | Decl (g, tm) ->
            let (g'_, g') = ia g in
            let _ = clearDelayed () in
            let (tm', d_) = inferApxDec (g'_, tm) in
            let _ = runDelayed () in ((Decl (g'_, d_)), (Decl (g', tm'))) end in
    let (g'_, g') = ia g in jwithctx (g', (inferApxJob (g'_, j)))
  | (g_, jterm tm) ->
      let _ = clearDelayed () in
      let (tm', u_, v_, l_) = inferApx (g_, tm) in
      let _ =
        filterLevel
          (tm', l_, 2,
            "The term in this position must be an object or a type family") in
      let _ = runDelayed () in jterm tm'
  | (g_, jclass tm) ->
      let _ = clearDelayed () in
      let l_ = newLVar () in
      let (tm', v_) =
        checkApx
          (g_, tm, (Uni l_), (Next l_),
            "The term in this position must be a type or a kind") in
      let _ =
        filterLevel
          (tm', (Next l_), 3,
            "The term in this position must be a type or a kind") in
      let _ = runDelayed () in jclass tm'
  | (g_, jof (tm1, tm2)) ->
      let _ = clearDelayed () in
      let l_ = newLVar () in
      let (tm2', v2_) =
        checkApx
          (g_, tm2, (Uni l_), (Next l_),
            "The term in this position must be a type or a kind") in
      let (tm1', u1_) =
        checkApx (g_, tm1, v2_, l_, "Ascription in declaration did not hold") in
      let _ =
        filterLevel
          (tm1', l_, 2,
            "The term in this position must be an object or a type family") in
      let _ = runDelayed () in jof (tm1', tm2')
  | (g_, jof' (tm1, v_)) ->
      let _ = clearDelayed () in
      let l_ = newLVar () in
      let (v2_, _) = Apx.classToApx v_ in
      let (tm1', u1_) =
        checkApx (g_, tm1, v2_, l_, "Ascription in declaration did not hold") in
      let _ =
        filterLevel
          (tm1', l_, 2,
            "The term in this position must be an object or a type family") in
      let _ = runDelayed () in jof' (tm1', v_) end
let rec ctxToApx =
  begin function
  | IntSyn.Null -> IntSyn.Null
  | Decl (g_, NDec x) -> IntSyn.Decl ((ctxToApx g_), (NDec x))
  | Decl (g_, Dec (name, v_)) ->
      let (v'_, _) = Apx.classToApx v_ in
      IntSyn.Decl ((ctxToApx g_), (Dec (name, v'_))) end
let rec inferApxJob' (g_, t) = inferApxJob ((ctxToApx g_), t)
open IntSyn
type job_ =
  | JNothing 
  | JAnd of (job_ * job_) 
  | JWithCtx of (IntSyn.dec_ IntSyn.ctx_ * job_) 
  | JTerm of ((IntSyn.exp_ * Paths.occExp) * IntSyn.exp_ * IntSyn.uni_) 
  | JClass of ((IntSyn.exp_ * Paths.occExp) * IntSyn.uni_) 
  | JOf of ((IntSyn.exp_ * Paths.occExp) * (IntSyn.exp_ * Paths.occExp) *
  IntSyn.uni_) 
type bidi_ =
  | Elim of ((IntSyn.sub_ * IntSyn.spine_) -> IntSyn.exp_) 
  | Intro of IntSyn.exp_ 
let rec elimSub (e_, s) =
  begin function | (s', s_) -> e_ ((comp (s, s')), s_) end
let rec elimApp (e_, u_) =
  begin function | (s, s_) -> e_ (s, (App ((EClo (u_, s)), s_))) end
let rec bvarElim n =
  begin function
  | (s, s_) ->
      (begin match bvarSub (n, s) with
       | Idx n' -> Root ((BVar n'), s_)
       | Exp (u_) -> Redex (u_, s_) end) end
let rec fvarElim (name, v_, s) =
  begin function | (s', s_) -> Root ((FVar (name, v_, (comp (s, s')))), s_) end
let rec redexElim (u_) =
  begin function | (s, s_) -> Redex ((EClo (u_, s)), s_) end
let rec headElim =
  begin function
  | BVar n -> bvarElim n
  | FVar fv -> fvarElim fv
  | NSDef d -> redexElim (constDef d)
  | h_ ->
      (begin match conDecStatus (headConDec h_) with
       | Foreign (csid, f) -> (begin function | (s, s_) -> f s_ end)
      | _ -> (begin function | (s, s_) -> Root (h_, s_) end) end) end
let rec evarElim (EVar _ as x_) =
  begin function | (s, s_) -> EClo (x_, (Whnf.spineToSub (s_, s))) end
let rec etaExpandW =
  begin function
  | (e_, (Pi (((Dec (_, Va) as d_), _), Vr), s)) ->
      let u1_ = etaExpand ((bvarElim 1), (Va, (comp (s, shift)))) in
      let d'_ = decSub (d_, s) in
      Lam
        (d'_,
          (etaExpand ((elimApp ((elimSub (e_, shift)), u1_)), (Vr, (dot1 s)))))
  | (e_, _) -> e_ (id, Nil) end
let rec etaExpand (e_, vs_) = etaExpandW (e_, (Whnf.whnfExpandDef vs_))
let rec toElim =
  begin function | Elim (e_) -> e_ | Intro (u_) -> redexElim u_ end
let rec toIntro =
  begin function
  | (Elim (e_), vs_) -> etaExpand (e_, vs_)
  | (Intro (u_), vs_) -> u_ end
let rec addImplicit1W
  (((g_, e_, (Pi ((Dec (_, Va), _), Vr), s), i))(* >= 1 *))
  =
  let x_ = Whnf.newLoweredEVar (g_, (Va, s)) in
  addImplicit
    (g_, (elimApp (e_, x_)), (Vr, (Whnf.dotEta ((Exp x_), s))), (i - 1))
let rec addImplicit =
  begin function
  | (g_, e_, vs_, 0) -> (e_, (EClo vs_))
  | (g_, e_, vs_, i) -> addImplicit1W (g_, e_, (Whnf.whnfExpandDef vs_), i) end
let rec reportConstraints (Xnames) =
  begin try
          begin match Print.evarCnstrsToStringOpt Xnames with
          | None -> ()
          | Some constr -> print (("Constraints:\n" ^ constr) ^ "\n") end
  with | Names.Unprintable -> print "%_constraints unprintable_%\n" end
let rec reportInst (Xnames) =
  begin try Msg.message ((Print.evarInstToString Xnames) ^ "\n")
  with | Names.Unprintable -> Msg.message "%_unifier unprintable_%\n" end
let rec delayMismatch (g_, v1_, v2_, r2, location_msg, problem_msg) =
  addDelayed
    (begin function
     | () ->
         let xs_ =
           Abstract.collectEVars
             (g_, (v2_, id), (Abstract.collectEVars (g_, (v1_, id), []))) in
         let Xnames =
           List.map
             (begin function | x_ -> (x_, (Names.evarName (IntSyn.Null, x_))) end)
           xs_ in
         let V1fmt = formatExp (g_, v1_) in
         let V2fmt = formatExp (g_, v2_) in
         let diff =
           F.Vbox0 0 1
             [F.String "Expected:";
             F.Space;
             V2fmt;
             F.Break;
             F.String "Inferred:";
             F.Space;
             V1fmt] in
         let diff =
           begin match Print.evarCnstrsToStringOpt Xnames with
           | None -> F.makestring_fmt diff
           | Some cnstrs ->
               ((F.makestring_fmt diff) ^ "\nConstraints:\n") ^ cnstrs end in
         error
           (r2,
             ((((("Type mismatch\n" ^ diff) ^ "\n") ^ problem_msg) ^ "\n") ^
                location_msg)) end)
let rec delayAmbiguous (g_, u_, r, msg) =
  addDelayed
    (begin function
     | () ->
         let Ufmt = formatExp (g_, u_) in
         let amb =
           F.HVbox [F.String "Inferred:"; F.Space; formatExp (g_, u_)] in
         error
           (r,
             ((((^) "Ambiguous reconstruction\n" F.makestring_fmt amb) ^ "\n")
                ^ msg)) end)
let rec unifyIdem x =
  let _ = Unify.reset () in
  let _ =
    begin try Unify.unify x
    with | Unify _ as e -> (begin Unify.unwind (); raise e end) end in
let _ = Unify.reset () in ((())
  (* this reset should be unnecessary -- for safety only *))
let rec unifiableIdem x =
  let _ = Unify.reset () in
  let ok = Unify.unifiable x in
  let _ = if ok then begin Unify.reset () end else begin Unify.unwind () end in
  ((ok)
    (* this reset should be unnecessary -- for safety only *))
type traceMode_ =
  | Progressive 
  | Omniscient 
let trace = ref false
let traceMode = ref Omniscient
let rec report f =
  begin match !traceMode with
  | Progressive -> f ()
  | Omniscient -> addDelayed f end
let rec reportMismatch (g_, vs1_, vs2_, problem_msg) =
  report
    (begin function
     | () ->
         let xs_ =
           Abstract.collectEVars
             (g_, vs2_, (Abstract.collectEVars (g_, vs1_, []))) in
         let Xnames =
           List.map
             (begin function | x_ -> (x_, (Names.evarName (IntSyn.Null, x_))) end)
           xs_ in
         let eqnsFmt =
           F.HVbox
             [F.String "|?";
             F.Space;
             formatExp (g_, (EClo vs1_));
             F.Break;
             F.String "=";
             F.Space;
             formatExp (g_, (EClo vs2_))] in
         let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
         let _ = reportConstraints Xnames in
         let _ =
           Msg.message
             ((("Failed: " ^ problem_msg) ^ "\n") ^
                "Continuing with subterm replaced by _\n") in
         () end)
let rec reportUnify' (g_, vs1_, vs2_) =
  let xs_ =
    Abstract.collectEVars (g_, vs2_, (Abstract.collectEVars (g_, vs1_, []))) in
  let Xnames =
    List.map
      (begin function | x_ -> (x_, (Names.evarName (IntSyn.Null, x_))) end)
    xs_ in
  let eqnsFmt =
    F.HVbox
      [F.String "|?";
      F.Space;
      formatExp (g_, (EClo vs1_));
      F.Break;
      F.String "=";
      F.Space;
      formatExp (g_, (EClo vs2_))] in
  let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
  let _ =
    begin try unifyIdem (g_, vs1_, vs2_)
    with
    | Unify msg as e ->
        (begin Msg.message
                 ((("Failed: " ^ msg) ^ "\n") ^
                    "Continuing with subterm replaced by _\n");
         raise e end) end in
  let _ = reportInst Xnames in let _ = reportConstraints Xnames in ()
let rec reportUnify (g_, vs1_, vs2_) =
  begin match !traceMode with
  | Progressive -> reportUnify' (g_, vs1_, vs2_)
  | Omniscient ->
      (begin try unifyIdem (g_, vs1_, vs2_)
       with
       | Unify msg as e ->
           (begin reportMismatch (g_, vs1_, vs2_, msg); raise e end) end) end
let rec reportInfer' =
  begin function
  | (g_, omitexact (_, _, r), u_, v_) ->
      let xs_ =
        Abstract.collectEVars
          (g_, (u_, id), (Abstract.collectEVars (g_, (v_, id), []))) in
      let Xnames =
        List.map
          (begin function | x_ -> (x_, (Names.evarName (IntSyn.Null, x_))) end)
        xs_ in
      let omit =
        F.HVbox
          [F.String "|-";
          F.Space;
          F.String "_";
          F.Space;
          F.String "==>";
          F.Space;
          formatExp (g_, u_);
          F.Break;
          F.String ":";
          F.Space;
          formatExp (g_, v_)] in
      let _ = Msg.message ((F.makestring_fmt omit) ^ "\n") in
      let _ = reportConstraints Xnames in ()
  | (g_, mismatch (tm1, tm2, _, _), u_, v_) -> reportInfer' (g_, tm2, u_, v_)
  | (g_, hastype _, u_, v_) -> ()
  | (g_, tm, u_, v_) ->
      let xs_ =
        Abstract.collectEVars
          (g_, (u_, id), (Abstract.collectEVars (g_, (v_, id), []))) in
      let Xnames =
        List.map
          (begin function | x_ -> (x_, (Names.evarName (IntSyn.Null, x_))) end)
        xs_ in
      let judg =
        F.HVbox
          [F.String "|-";
          F.Space;
          formatExp (g_, u_);
          F.Break;
          F.String ":";
          F.Space;
          formatExp (g_, v_)] in
      let _ = Msg.message ((F.makestring_fmt judg) ^ "\n") in
      let _ = reportConstraints Xnames in () end
let rec reportInfer x = report (begin function | () -> reportInfer' x end)
let rec inferExactN =
  begin function
  | (g_, (internal (u_, v_, r) as tm)) -> (tm, (Intro u_), v_)
  | (g_, (constant (h_, r) as tm)) ->
      let cd = headConDec h_ in
      let (e_, v_) =
        addImplicit
          (g_, (headElim h_), ((conDecType cd), id), (conDecImp cd)) in
      (tm, (Elim e_), v_)
  | (g_, (bvar (k, r) as tm)) ->
      let Dec (_, v_) = ctxDec (g_, k) in (tm, (Elim (bvarElim k)), v_)
  | (g_, (evar (name, r) as tm)) ->
      let (x_, v_) =
        begin try getEVar (name, false)
        with
        | Apx.Ambiguous ->
            let (x_, v_) = getEVar (name, true) in
            (begin delayAmbiguous
                     (g_, v_, r, "Free variable has ambiguous type");
             (x_, v_) end) end in
let s = Shift (ctxLength g_) in
(((tm, (Elim (elimSub ((evarElim x_), s))), (EClo (v_, s))))
  (* externally EVars are raised elim forms *)(* necessary? -kw *))
  | (g_, (fvar (name, r) as tm)) ->
      let v_ =
        begin try getFVarType (name, false)
        with
        | Apx.Ambiguous ->
            let v_ = getFVarType (name, true) in
            (begin delayAmbiguous
                     (g_, v_, r, "Free variable has ambiguous type");
             v_ end) end in
let s = Shift (ctxLength g_) in
(((tm, (Elim (fvarElim (name, v_, s))), (EClo (v_, s))))
  (* necessary? -kw *))
| (g_, (typ r as tm)) -> (tm, (Intro (Uni Type)), (Uni Kind))
| (g_, arrow (tm1, tm2)) ->
    let (((tm1', b1_, _))(* Uni Type *)) =
      inferExact (g_, tm1) in
    let d_ = Dec (None, (toIntro (b1_, ((Uni Type), id)))) in
    let (tm2', b2_, l_) = inferExact (g_, tm2) in
    let v2_ = toIntro (b2_, (l_, id)) in
    ((arrow (tm1', tm2')), (Intro (Pi ((d_, No), (EClo (v2_, shift))))), l_)
| (g_, pi (tm1, tm2)) ->
    let (tm1', d_) = inferExactDec (g_, tm1) in
    let (tm2', b2_, l_) = inferExact ((Decl (g_, d_)), tm2) in
    let v2_ = toIntro (b2_, (l_, id)) in
    ((pi (tm1', tm2')), (Intro (Pi ((d_, Maybe), v2_))), l_)
| (g_, lam (tm1, tm2)) ->
    let (tm1', d_) = inferExactDec (g_, tm1) in
    let (tm2', b2_, v2_) = inferExact ((Decl (g_, d_)), tm2) in
    let u2_ = toIntro (b2_, (v2_, id)) in
    ((lam (tm1', tm2')), (Intro (Lam (d_, u2_))), (Pi ((d_, Maybe), v2_)))
| (g_, app (tm1, tm2)) ->
    let (tm1', b1_, v1_) = inferExact (g_, tm1) in
    let e1_ = toElim b1_ in
    let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (v1_, id) in
    let (tm2', b2_) =
      checkExact
        (g_, tm2, (Va, s),
          "Argument type did not match function domain type\n(Index object(s) did not match)") in
    let u2_ = toIntro (b2_, (Va, s)) in
    ((app (tm1', tm2')), (Elim (elimApp (e1_, u2_))),
      (EClo (Vr, (Whnf.dotEta ((Exp u2_), s)))))
| (g_, hastype (tm1, tm2)) ->
    let (tm2', b2_, l_) = inferExact (g_, tm2) in
    let v_ = toIntro (b2_, (l_, id)) in
    let (tm1', b1_) =
      checkExact
        (g_, tm1, (v_, id),
          "Ascription did not hold\n(Index object(s) did not match)") in
    ((hastype (tm1', tm2')), b1_, v_)
| (g_, mismatch (tm1, tm2, location_msg, problem_msg)) ->
    let (tm1', _, v1_) = inferExact (g_, tm1) in
    let (tm2', b_, v_) = inferExactN (g_, tm2) in
    let _ =
      if !trace
      then begin reportMismatch (g_, (v1_, id), (v_, id), problem_msg) end
      else begin () end in
    let _ =
      delayMismatch
        (g_, v1_, v_, (termRegion tm2'), location_msg, problem_msg) in
    ((mismatch (tm1', tm2', location_msg, problem_msg)), b_, v_)
| (g_, omitapx (u_, v_, l_, r)) ->
    let v'_ =
      begin try Apx.apxToClass (g_, v_, l_, false)
      with
      | Apx.Ambiguous ->
          let v'_ = Apx.apxToClass (g_, v_, l_, true) in
          (begin delayAmbiguous
                   (g_, v'_, r,
                     ("Omitted term has ambiguous " ^
                        ((begin match Apx.whnfUni l_ with
                          | Level 1 -> "type"
                          | Level 2 -> "kind"
                          | Level 3 -> "hyperkind" end)
                     (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                     (* FIX: this violates an invariant in printing *))));
            v'_ end) end in
let u'_ =
begin try Apx.apxToExact (g_, u_, (v'_, id), false)
with
| Apx.Ambiguous ->
    let u'_ = Apx.apxToExact (g_, u_, (v'_, id), true) in
    (begin delayAmbiguous
             (g_, u'_, r,
               (("Omitted " ^
                   (begin match Apx.whnfUni l_ with
                    | Level 2 -> "type"
                    | Level 3 -> "kind" end)) ^ " is ambiguous"));
      u'_ end) end in
((omitexact (u'_, v'_, r)), (Intro u'_), v'_) end
let rec inferExact (g_, tm) =
  if not !trace then begin inferExactN (g_, tm) end
  else begin
    (let (tm', b'_, v'_) = inferExactN (g_, tm) in
     begin reportInfer (g_, tm', (toIntro (b'_, (v'_, id))), v'_);
     (tm', b'_, v'_) end) end
let rec inferExactDec (g_, dec (name, tm, r)) =
  let (((tm', b1_, _))(* Uni Type *)) = inferExact (g_, tm) in
  let v1_ = toIntro (b1_, ((Uni Type), id)) in
  let d_ = Dec (name, v1_) in ((dec (name, tm', r)), d_)
let rec checkExact1 =
  begin function
  | (g_, lam (dec (name, tm1, r), tm2), Vhs) ->
      let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
      let ((((tm1', b1_, _))(* Uni Type *)), ok1) =
        unifyExact (g_, tm1, (Va, s)) in
      let v1_ = toIntro (b1_, ((Uni Type), id)) in
      let d_ = Dec (name, v1_) in
      let ((tm2', b2_, v2_), ok2) =
        if ok1
        then begin checkExact1 ((Decl (g_, d_)), tm2, (Vr, (dot1 s))) end
        else begin ((inferExact ((Decl (g_, d_)), tm2)), false) end in
      let u2_ = toIntro (b2_, (v2_, id)) in
      (((lam ((dec (name, tm1', r)), tm2')), (Intro (Lam (d_, u2_))),
         (Pi ((d_, Maybe), v2_))), ok2)
  | (g_, hastype (tm1, tm2), Vhs) ->
      let ((tm2', b2_, l_), ok2) = unifyExact (g_, tm2, Vhs) in
      let v_ = toIntro (b2_, (l_, id)) in
      let (tm1', b1_) =
        checkExact
          (g_, tm1, (v_, id),
            "Ascription did not hold\n(Index object(s) did not match)") in
      (((hastype (tm1', tm2')), b1_, v_), ok2)
  | (g_, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
      let (tm1', _, v1_) = inferExact (g_, tm1) in
      let ((tm2', b_, v_), ok2) = checkExact1 (g_, tm2, Vhs) in
      let _ =
        delayMismatch
          (g_, v1_, v_, (termRegion tm2'), location_msg, problem_msg) in
      (((mismatch (tm1', tm2', location_msg, problem_msg)), b_, v_), ok2)
  | (g_, omitapx (((u_, v_, l_, r))(* = Vhs *)), Vhs) ->
      let v'_ = EClo Vhs in
      let u'_ =
        begin try Apx.apxToExact (g_, u_, Vhs, false)
        with
        | Apx.Ambiguous ->
            let u'_ = Apx.apxToExact (g_, u_, Vhs, true) in
            (begin delayAmbiguous
                     (g_, u'_, r,
                       (("Omitted " ^
                           (begin match Apx.whnfUni l_ with
                            | Level 2 -> "type"
                            | Level 3 -> "kind" end)) ^ " is ambiguous"));
              u'_ end) end in
(((omitexact (u'_, v'_, r)), (Intro u'_), v'_), true)
| (g_, tm, Vhs) ->
    let (tm', b'_, v'_) = inferExact (g_, tm) in
    ((tm', b'_, v'_), (unifiableIdem (g_, Vhs, (v'_, id)))) end
let rec checkExact (g_, tm, vs_, location_msg) =
  if not !trace
  then
    begin let ((tm', b'_, v'_), ok) = checkExact1 (g_, tm, vs_) in
          (if ok then begin (tm', b'_) end
            else begin
              (begin try
                       ((begin unifyIdem (g_, (v'_, id), vs_); raise Match end)
               (* can't happen *))
              with
              | Unify problem_msg ->
                  let r = termRegion tm in
                  let u'_ = toIntro (b'_, (v'_, id)) in
                  let (Uapx, Vapx, Lapx) = Apx.exactToApx (u'_, v'_) in
                  let ((((((tm'', B'', _))(* Vs *)), _))
                    (* true *)) =
                    checkExact1 (g_, (omitapx (Uapx, Vapx, Lapx, r)), vs_) in
                  let _ =
                    delayMismatch
                      (g_, v'_, (EClo vs_), r, location_msg, problem_msg) in
                  ((mismatch (tm', tm'', location_msg, problem_msg)), B'') end) end) end
else begin
  (let (tm', b'_, v'_) = inferExact (g_, tm) in
   begin try begin reportUnify (g_, (v'_, id), vs_); (tm', b'_) end
     with
     | Unify problem_msg ->
         let r = termRegion tm in
         let u'_ = toIntro (b'_, (v'_, id)) in
         let (Uapx, Vapx, Lapx) = Apx.exactToApx (u'_, v'_) in
         let (tm'', B'') =
           checkExact
             (g_, (omitapx (Uapx, Vapx, Lapx, r)), vs_, location_msg) in
         let _ =
           delayMismatch (g_, v'_, (EClo vs_), r, location_msg, problem_msg) in
         ((mismatch (tm', tm'', location_msg, problem_msg)), B'') end) end
let rec unifyExact =
  begin function
  | (g_, arrow (tm1, tm2), Vhs) ->
      let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
      let ((((tm1', b1_, _))(* Uni Type *)), ok1) =
        unifyExact (g_, tm1, (Va, s)) in
      let v1_ = toIntro (b1_, ((Uni Type), id)) in
      let d_ = Dec (None, v1_) in
      let (tm2', b2_, l_) = inferExact (g_, tm2) in
      let v2_ = toIntro (b2_, (l_, id)) in
      (((arrow (tm1', tm2')), (Intro (Pi ((d_, No), (EClo (v2_, shift))))),
         l_),
        (ok1 &&
           (unifiableIdem ((Decl (g_, d_)), (Vr, (dot1 s)), (v2_, shift)))))
  | (g_, pi (dec (name, tm1, r), tm2), Vhs) ->
      let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
      let ((((tm1', b1_, _))(* Uni Type *)), ok1) =
        unifyExact (g_, tm1, (Va, s)) in
      let v1_ = toIntro (b1_, ((Uni Type), id)) in
      let d_ = Dec (name, v1_) in
      let ((tm2', b2_, l_), ok2) =
        if ok1
        then begin unifyExact ((Decl (g_, d_)), tm2, (Vr, (dot1 s))) end
        else begin ((inferExact ((Decl (g_, d_)), tm2)), false) end in
      let v2_ = toIntro (b2_, (l_, id)) in
      (((pi ((dec (name, tm1', r)), tm2')), (Intro (Pi ((d_, Maybe), v2_))),
         l_), ok2)
  | (g_, hastype (tm1, tm2), Vhs) ->
      let (((tm2', _, _))(* Uni L *)(* Uni (Next L) *))
        = inferExact (g_, tm2) in
      let ((tm1', b_, l_), ok1) = unifyExact (g_, tm1, Vhs) in
      (((((hastype (tm1', tm2')), b_, l_), ok1))
        (* Vh : L by invariant *))
  | (g_, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
      let (tm1', _, l1_) = inferExact (g_, tm1) in
      let ((tm2', b_, l_), ok2) = unifyExact (g_, tm2, Vhs) in
      let _ =
        delayMismatch
          (g_, l1_, l_, (termRegion tm2'), location_msg, problem_msg) in
      (((mismatch (tm1', tm2', location_msg, problem_msg)), b_, l_), ok2)
  | (g_, omitapx
     (((v_, l_, nL, r))(* = Vhs *)(* Next L *)),
     Vhs) ->
      let l'_ = Apx.apxToClass (g_, l_, nL, false) in
      let v'_ = EClo Vhs in
      (((((omitexact (v'_, l'_, r)), (Intro v'_), l'_), true))
        (* cannot raise Ambiguous *))
  | (g_, tm, Vhs) ->
      let (tm', b'_, l'_) = inferExact (g_, tm) in
      let v'_ = toIntro (b'_, (l'_, id)) in
      ((tm', b'_, l'_), (unifiableIdem (g_, Vhs, (v'_, id)))) end(* lam impossible *)
let rec occElim =
  begin function
  | (constant (h_, r), os, rs, i) ->
      let r' = List.foldr Paths.join r rs in
      ((((Paths.root (r', (Paths.leaf r), (conDecImp (headConDec h_)), i, os)),
          r'))
        (* should probably treat a constant with Foreign
             attribute as a redex *))
  | (bvar (k, r), os, rs, i) ->
      let r' = List.foldr Paths.join r rs in
      ((Paths.root (r', (Paths.leaf r), 0, i, os)), r')
  | (fvar (name, r), os, rs, i) ->
      let r' = List.foldr Paths.join r rs in
      ((Paths.root (r', (Paths.leaf r), 0, i, os)), r')
  | (app (tm1, tm2), os, rs, i) ->
      let (oc2, r2) = occIntro tm2 in
      occElim (tm1, (Paths.app (oc2, os)), (r2 :: rs), (i + 1))
  | (hastype (tm1, tm2), os, rs, i) -> occElim (tm1, os, rs, i)
  | (tm, os, rs, i) ->
      let r' = List.foldr Paths.join (termRegion tm) rs in
      ((Paths.leaf r'), r') end(* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)
let rec occIntro =
  begin function
  | arrow (tm1, tm2) ->
      let (oc1, r1) = occIntro tm1 in
      let (oc2, r2) = occIntro tm2 in
      let r' = Paths.join (r1, r2) in
      ((Paths.bind (r', (Some oc1), oc2)), r')
  | pi (dec (name, tm1, r), tm2) ->
      let (oc1, r1) = occIntro tm1 in
      let (oc2, r2) = occIntro tm2 in
      let r' = Paths.join (r, r2) in
      ((((Paths.bind (r', (Some oc1), oc2)), r'))
        (* not quite consistent with older implementation for dec0 *))
  | lam (dec (name, tm1, r), tm2) ->
      let (oc1, r1) = occIntro tm1 in
      let (oc2, r2) = occIntro tm2 in
      let r' = Paths.join (r, r2) in
      ((((Paths.bind (r', (Some oc1), oc2)), r'))
        (* not quite consistent with older implementation for dec0 *))
  | hastype (tm1, tm2) -> occIntro tm1
  | tm ->
      let (oc, r) = occElim (tm, Paths.nils, [], 0) in (((oc, r))
        (* still doesn't work quite right for the location -> occurrence map? *)) end
let rec inferExactJob =
  begin function
  | (g_, jnothing) -> JNothing
  | (g_, jand (j1, j2)) ->
      JAnd ((inferExactJob (g_, j1)), (inferExactJob (g_, j2)))
  | (g_, jwithctx (g, j)) ->
      let rec ie =
        begin function
        | Null -> (g_, Null)
        | Decl (g, tm) ->
            let (g'_, Gresult) = ie g in
            let (_, d_) = inferExactDec (g'_, tm) in
            ((Decl (g'_, d_)), (Decl (Gresult, d_))) end in
    let (g'_, Gresult) = ie g in JWithCtx (Gresult, (inferExactJob (g'_, j)))
  | (g_, jterm tm) ->
      let (tm', b_, v_) = inferExact (g_, tm) in
      let u_ = toIntro (b_, (v_, id)) in
      let (oc, r) = occIntro tm' in
      let rec iu =
        begin function
        | Uni (Type) -> Kind
        | Pi (_, v_) -> iu v_
        | Root _ -> Type
        | Redex (v_, _) -> iu v_
        | Lam (_, v_) -> iu v_
        | EClo (v_, _) -> iu v_ end in
      ((JTerm ((u_, oc), v_, (iu v_)))
        (* others impossible *))
  | (g_, jclass tm) ->
      let (tm', b_, l_) = inferExact (g_, tm) in
      let v_ = toIntro (b_, (l_, id)) in
      let (oc, r) = occIntro tm' in
      let (Uni (l_), _) = Whnf.whnf (l_, id) in JClass ((v_, oc), l_)
  | (g_, jof (tm1, tm2)) ->
      let (tm2', b2_, l2_) = inferExact (g_, tm2) in
      let v2_ = toIntro (b2_, (l2_, id)) in
      let (tm1', b1_) =
        checkExact
          (g_, tm1, (v2_, id),
            ("Ascription in declaration did not hold\n" ^
               "(Index object(s) did not match)")) in
      let u1_ = toIntro (b1_, (v2_, id)) in
      let (oc2, r2) = occIntro tm2' in
      let (oc1, r1) = occIntro tm1' in
      let (Uni (l2_), _) = Whnf.whnf (l2_, id) in
      JOf ((u1_, oc1), (v2_, oc2), l2_)
  | (g_, jof' (tm1, v2_)) ->
      let (tm1', b1_) =
        checkExact
          (g_, tm1, (v2_, id),
            ("Ascription in declaration did not hold\n" ^
               "(Index object(s) did not match)")) in
      let u1_ = toIntro (b1_, (v2_, id)) in
      let (oc1, r1) = occIntro tm1' in ((JOf ((u1_, oc1), (v2_, oc1), Type))
        (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
        (*          val (oc2, r2) = occIntro tm2' *)
        (*          val (Uni L2, _) = Whnf.whnf (L2, id) *)) end
let rec recon' j =
  let _ = Apx.varReset () in
  let _ = varReset () in
  let j' = inferApxJob (Null, j) in
  let _ = clearDelayed () in
  let j'' = inferExactJob (Null, j') in
  let _ = runDelayed () in ((j'')
    (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
    (* context must already have called resetErrors *)
    (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *))
let rec recon j = begin queryMode := false; recon' j end
let rec reconQuery j = begin queryMode := true; recon' j end
let rec reconWithCtx' (g_, j) =
  let _ = Apx.varReset () in
  let _ = varReset () in
  let j' = inferApxJob' (g_, j) in
  let _ = clearDelayed () in
  let j'' = inferExactJob (g_, j') in
  let _ = runDelayed () in ((j'')
    (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
    (* context must already have called resetErrors *)
    (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *))
let rec reconWithCtx (g_, j) =
  begin queryMode := false; reconWithCtx' (g_, j) end
let rec reconQueryWithCtx (g_, j) =
  begin queryMode := true; reconWithCtx' (g_, j) end
let rec internalInst x = raise Match
let rec externalInst x = raise Match end
