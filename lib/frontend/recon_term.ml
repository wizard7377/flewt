
module type EXTSYN  =
  sig
    type nonrec term
    type nonrec dec
    val lcid : string list -> string -> Paths.region -> term
    val ucid : string list -> string -> Paths.region -> term
    val quid : string list -> string -> Paths.region -> term
    val scon : string -> Paths.region -> term
    val evar : string -> Paths.region -> term
    val fvar : string -> Paths.region -> term
    val typ : Paths.region -> term
    val arrow : term -> term -> term
    val backarrow : term -> term -> term
    val pi : dec -> term -> term
    val lam : dec -> term -> term
    val app : term -> term -> term
    val hastype : term -> term -> term
    val omitted : Paths.region -> term
    val dec : string option -> term -> Paths.region -> dec
    val dec0 : string option -> Paths.region -> dec
  end
module type RECON_TERM  =
  sig
    include EXTSYN
    exception Error of string 
    val resetErrors : string -> unit
    val checkErrors : Paths.region -> unit
    type __TraceMode =
      | Progressive 
      | Omniscient 
    val trace : bool ref
    val traceMode : __TraceMode ref
    type nonrec job
    val jnothing : job
    val jand : job -> job -> job
    val jwithctx : dec IntSyn.__Ctx -> job -> job
    val jterm : term -> job
    val jclass : term -> job
    val jof : term -> term -> job
    val jof' : term -> IntSyn.__Exp -> job
    type __Job =
      | JNothing 
      | JAnd of (__Job * __Job) 
      | JWithCtx of (IntSyn.__Dec IntSyn.__Ctx * __Job) 
      | JTerm of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Exp *
      IntSyn.__Uni) 
      | JClass of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Uni) 
      | JOf of ((IntSyn.__Exp * Paths.occExp) * (IntSyn.__Exp * Paths.occExp)
      * IntSyn.__Uni) 
    val recon : job -> __Job
    val reconQuery : job -> __Job
    val reconWithCtx : IntSyn.dctx -> job -> __Job
    val reconQueryWithCtx : IntSyn.dctx -> job -> __Job
    val termRegion : term -> Paths.region
    val decRegion : dec -> Paths.region
    val ctxRegion : dec IntSyn.__Ctx -> Paths.region option
    val internalInst : 'a -> 'b
    val externalInst : 'a -> 'b
  end;;




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
    let (delayedList : (unit -> unit) list ref) = ref nil
    let rec clearDelayed () = delayedList := nil
    let rec addDelayed f = (delayedList := f) :: (!delayedList)
    let rec runDelayed () =
      let rec run' = function | nil -> () | h::t -> (run' t; h ()) in
      run' (!delayedList)
    exception Error of string 
    let errorCount = ref 0
    let errorFileName = ref "no file"
    let errorThreshold = ref (Some 20)
    let rec exceeds __0__ __1__ =
      match (__0__, __1__) with | (i, NONE) -> false__ | (i, Some j) -> i > j
    let rec resetErrors fileName = errorCount := 0; errorFileName := fileName
    let rec die r =
      raise
        (Error
           (Paths.wrap
              (r,
                (((((^) " " Int.toString (!errorCount)) ^ " error") ^
                    (if (!errorCount) > 1 then "s" else ""))
                   ^ " found"))))
    let rec checkErrors r = if (!errorCount) > 0 then die r else ()
    let rec chatterOneNewline () =
      if ((!Global.chatter) = 1) && ((!errorCount) = 1)
      then Msg.message "\n"
      else ()
    let rec fatalError r msg =
      ((!) ((:=) errorCount) errorCount) + 1;
      chatterOneNewline ();
      Msg.message (((^) ((!errorFileName) ^ ":") Paths.wrap (r, msg)) ^ "\n");
      die r
    let rec error r msg =
      ((!) ((:=) errorCount) errorCount) + 1;
      chatterOneNewline ();
      Msg.message (((^) ((!errorFileName) ^ ":") Paths.wrap (r, msg)) ^ "\n");
      if exceeds ((!errorCount), (!errorThreshold)) then die r else ()
    let rec formatExp (__G) (__U) =
      try Print.formatExp (__G, __U)
      with | Names.Unprintable -> F.String "%_unprintable_%"
    let queryMode = ref false__
    open IntSyn
    let rec headConDec =
      function
      | Const c -> sgnLookup c
      | Skonst c -> sgnLookup c
      | Def d -> sgnLookup d
      | NSDef d -> sgnLookup d
      | FgnConst (_, cd) -> cd
    let rec lowerTypeW __2__ __3__ =
      match (__2__, __3__) with
      | (__G, (Pi ((__D, _), __V), s)) ->
          let __D' = decSub (__D, s) in
          lowerType ((Decl (__G, __D')), (__V, (dot1 s)))
      | (__G, __Vs) -> (__G, (EClo __Vs))
    let rec lowerType (__G) (__Vs) =
      lowerTypeW (__G, (Whnf.whnfExpandDef __Vs))
    let rec raiseType __4__ __5__ =
      match (__4__, __5__) with
      | (Null, __V) -> __V
      | (Decl (__G, __D), __V) -> raiseType (__G, (Pi ((__D, Maybe), __V)))
    let (evarApxTable : Apx.__Exp StringTree.__Table) = StringTree.new__ 0
    let (fvarApxTable : Apx.__Exp StringTree.__Table) = StringTree.new__ 0
    let (fvarTable : IntSyn.__Exp StringTree.__Table) = StringTree.new__ 0
    let rec varReset () =
      StringTree.clear evarApxTable;
      StringTree.clear fvarApxTable;
      StringTree.clear fvarTable
    let rec getEVarTypeApx name =
      match StringTree.lookup evarApxTable name with
      | Some (__V) -> __V
      | NONE ->
          (match Names.getEVarOpt name with
           | Some (EVar (_, _, __V, _)) ->
               let (((__V', _))(* Type *)) =
                 Apx.classToApx __V in
               (StringTree.insert evarApxTable (name, __V'); __V')
           | NONE ->
               let __V = Apx.newCVar () in
               (StringTree.insert evarApxTable (name, __V); __V))
    let rec getFVarTypeApx name =
      match StringTree.lookup fvarApxTable name with
      | Some (__V) -> __V
      | NONE ->
          let __V = Apx.newCVar () in
          (StringTree.insert fvarApxTable (name, __V); __V)
    let rec getEVar name allowed =
      match Names.getEVarOpt name with
      | Some (EVar (_, __G, __V, _) as X) -> (__X, (raiseType (__G, __V)))
      | NONE ->
          let __V = Option.valOf (StringTree.lookup evarApxTable name) in
          let __V' = Apx.apxToClass (IntSyn.Null, __V, Apx.Type, allowed) in
          let (G'', V'') = lowerType (IntSyn.Null, (__V', IntSyn.id)) in
          let __X = IntSyn.newEVar (G'', V'') in
          (Names.addEVar (__X, name); (__X, __V'))
    let rec getFVarType name allowed =
      match StringTree.lookup fvarTable name with
      | Some (__V) -> __V
      | NONE ->
          let __V = Option.valOf (StringTree.lookup fvarApxTable name) in
          let __V' = Apx.apxToClass (IntSyn.Null, __V, Apx.Type, allowed) in
          (StringTree.insert fvarTable (name, __V'); __V')
    type term =
      | internal of (IntSyn.__Exp * IntSyn.__Exp * Paths.region)
      [@sml.renamed "internal"][@sml.renamed "internal"]
      | constant of (IntSyn.__Head * Paths.region)
      [@sml.renamed "constant"][@sml.renamed "constant"]
      | bvar of (int * Paths.region)
      [@sml.renamed "bvar"][@sml.renamed "bvar"]
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
      | omitted of Paths.region
      [@sml.renamed "omitted"][@sml.renamed "omitted"]
      | lcid of (string list * string * Paths.region)
      [@sml.renamed "lcid"][@sml.renamed "lcid"]
      | ucid of (string list * string * Paths.region)
      [@sml.renamed "ucid"][@sml.renamed "ucid"]
      | quid of (string list * string * Paths.region)
      [@sml.renamed "quid"][@sml.renamed "quid"]
      | scon of (string * Paths.region)
      [@sml.renamed "scon"][@sml.renamed "scon"]
      | omitapx of (Apx.__Exp * Apx.__Exp * Apx.__Uni * Paths.region)
      [@sml.renamed "omitapx"][@sml.renamed "omitapx"]
      | omitexact of (IntSyn.__Exp * IntSyn.__Exp * Paths.region)
      [@sml.renamed "omitexact"][@sml.renamed "omitexact"]
    and dec =
      | dec of (string option * term * Paths.region)
      [@sml.renamed "dec"][@sml.renamed "dec"]
    let rec backarrow tm1 tm2 = arrow (tm2, tm1)
    let rec dec0 nameOpt r = dec (nameOpt, (omitted r), r)
    type job =
      | jnothing [@sml.renamed "jnothing"][@sml.renamed "jnothing"]
      | jand of (job * job) [@sml.renamed "jand"][@sml.renamed "jand"]
      | jwithctx of (dec IntSyn.__Ctx * job)
      [@sml.renamed "jwithctx"][@sml.renamed "jwithctx"]
      | jterm of term [@sml.renamed "jterm"][@sml.renamed "jterm"]
      | jclass of term [@sml.renamed "jclass"][@sml.renamed "jclass"]
      | jof of (term * term) [@sml.renamed "jof"][@sml.renamed "jof"]
      | jof' of (term * IntSyn.__Exp)
      [@sml.renamed "jof'"][@sml.renamed "jof'"]
    let rec termRegion =
      function
      | internal (__U, __V, r) -> r
      | constant (__H, r) -> r
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
      | omitapx (__U, __V, __L, r) -> r
      | omitexact (__U, __V, r) -> r
    let rec decRegion (dec (name, tm, r)) = r
    let rec ctxRegion =
      function
      | IntSyn.Null -> NONE
      | Decl (g, tm) -> ctxRegion' (g, (decRegion tm))
    let rec ctxRegion' __6__ __7__ =
      match (__6__, __7__) with
      | (IntSyn.Null, r) -> Some r
      | (Decl (g, tm), r) -> ctxRegion' (g, (Paths.join (r, (decRegion tm))))
    open Apx
    type __Ctx = IntSyn.__Ctx
    type __Dec =
      | Dec of (string option * __Exp) 
      | NDec of string option 
    let rec filterLevel tm (__L) max msg =
      let notGround = makeGroundUni __L in
      let Level i = whnfUni __L in
      if i > max
      then fatalError ((termRegion tm), ("Level too high\n" ^ msg))
      else
        if notGround
        then
          error
            ((termRegion tm),
              (((("Ambiguous level\n" ^
                    "The level of this term could not be inferred\n")
                   ^ "Defaulting to ")
                  ^
                  (match i with
                   | 1 -> "object"
                   | 2 -> "type family"
                   | 3 -> "kind"))
                 ^ " level"))
        else ()
    let rec findOmitted (__G) qid r =
      error
        (r,
          ((^) "Undeclared identifier " Names.qidToString
             (valOf (Names.constUndef qid))));
      omitted r
    let rec findBVar' __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (Null, name, k) -> NONE
      | (Decl (__G, Dec (NONE, _)), name, k) ->
          findBVar' (__G, name, (k + 1))
      | (Decl (__G, NDec _), name, k) -> findBVar' (__G, name, (k + 1))
      | (Decl (__G, Dec (Some name', _)), name, k) ->
          if name = name' then Some k else findBVar' (__G, name, (k + 1))
    let rec findBVar fc (__G) qid r =
      match Names.unqualified qid with
      | NONE -> fc (__G, qid, r)
      | Some name ->
          (match findBVar' (__G, name, 1) with
           | NONE -> fc (__G, qid, r)
           | Some k -> bvar (k, r))
    let rec findConst fc (__G) qid r =
      match Names.constLookup qid with
      | NONE -> fc (__G, qid, r)
      | Some cid ->
          (match IntSyn.sgnLookup cid with
           | ConDec _ -> constant ((IntSyn.Const cid), r)
           | ConDef _ -> constant ((IntSyn.Def cid), r)
           | AbbrevDef _ -> constant ((IntSyn.NSDef cid), r)
           | _ ->
               (error
                  (r,
                    (((^) ("Invalid identifier\n" ^ "Identifier `")
                        Names.qidToString qid)
                       ^ "' is not a constant, definition or abbreviation"));
                omitted r))
    let rec findCSConst fc (__G) qid r =
      match Names.unqualified qid with
      | NONE -> fc (__G, qid, r)
      | Some name ->
          (match CSManager.parse name with
           | NONE -> fc (__G, qid, r)
           | Some (cs, conDec) ->
               constant ((IntSyn.FgnConst (cs, conDec)), r))
    let rec findEFVar fc (__G) qid r =
      match Names.unqualified qid with
      | NONE -> fc (__G, qid, r)
      | Some name -> (if !queryMode then evar else fvar) (name, r)
    let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x
    let rec findUCID x =
      findBVar (findConst (findCSConst (findEFVar findOmitted))) x
    let rec findQUID x = findConst (findCSConst findOmitted) x
    let rec inferApx __13__ __14__ =
      match (__13__, __14__) with
      | (__G, (internal (__U, __V, r) as tm)) ->
          let (__U', __V', __L') = exactToApx (__U, __V) in
          (tm, __U', __V', __L')
      | (__G, (lcid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__G, (findLCID (__G, qid, r)))
      | (__G, (ucid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__G, (findUCID (__G, qid, r)))
      | (__G, (quid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__G, (findQUID (__G, qid, r)))
      | (__G, (scon (name, r) as tm)) ->
          (match CSManager.parse name with
           | NONE ->
               (error (r, "Strings unsupported in current signature");
                inferApx (__G, (omitted r)))
           | Some (cs, conDec) ->
               inferApx (__G, (constant ((IntSyn.FgnConst (cs, conDec)), r))))
      | (__G, (constant (__H, r) as tm)) ->
          let cd = headConDec __H in
          let (__U', __V', __L') =
            exactToApx
              ((IntSyn.Root (__H, IntSyn.Nil)), (IntSyn.conDecType cd)) in
          let rec dropImplicit __11__ __12__ =
            match (__11__, __12__) with
            | (__V, 0) -> __V
            | (Arrow (_, __V), i) -> dropImplicit (__V, (i - 1)) in
          let V'' = dropImplicit (__V', (IntSyn.conDecImp cd)) in
          (tm, __U', V'', __L')
      | (__G, (bvar (k, r) as tm)) ->
          let Dec (_, __V) = IntSyn.ctxLookup (__G, k) in
          (tm, Undefined, __V, Type)
      | (__G, (evar (name, r) as tm)) ->
          (tm, Undefined, (getEVarTypeApx name), Type)
      | (__G, (fvar (name, r) as tm)) ->
          (tm, Undefined, (getFVarTypeApx name), Type)
      | (__G, (typ r as tm)) -> (tm, (Uni Type), (Uni Kind), Hyperkind)
      | (__G, arrow (tm1, tm2)) ->
          let __L = newLVar () in
          let (tm1', __V1) =
            checkApx
              (__G, tm1, (Uni Type), Kind,
                "Left-hand side of arrow must be a type") in
          let (tm2', __V2) =
            checkApx
              (__G, tm2, (Uni __L), (Next __L),
                "Right-hand side of arrow must be a type or a kind") in
          ((arrow (tm1', tm2')), (Arrow (__V1, __V2)), (Uni __L), (Next __L))
      | (__G, pi (tm1, tm2)) ->
          let (tm1', (Dec (_, __V1) as D)) = inferApxDec (__G, tm1) in
          let __L = newLVar () in
          let (tm2', __V2) =
            checkApx
              ((Decl (__G, __D)), tm2, (Uni __L), (Next __L),
                "Body of pi must be a type or a kind") in
          ((pi (tm1', tm2')), (Arrow (__V1, __V2)), (Uni __L), (Next __L))
      | (__G, (lam (tm1, tm2) as tm)) ->
          let (tm1', (Dec (_, __V1) as D)) = inferApxDec (__G, tm1) in
          let (tm2', __U2, __V2, __L2) = inferApx ((Decl (__G, __D)), tm2) in
          ((lam (tm1', tm2')), __U2, (Arrow (__V1, __V2)), __L2)
      | (__G, (app (tm1, tm2) as tm)) ->
          let __L = newLVar () in
          let Va = newCVar () in
          let Vr = newCVar () in
          let (tm1', __U1) =
            checkApx
              (__G, tm1, (Arrow (Va, Vr)), __L,
                "Non-function was applied to an argument") in
          let (tm2', _) =
            checkApx
              (__G, tm2, Va, Type,
                "Argument type did not match function domain type") in
          ((((app (tm1', tm2')), __U1, Vr, __L))
            (* probably a confusing message if the problem is the level: *))
      | (__G, (hastype (tm1, tm2) as tm)) ->
          let __L = newLVar () in
          let (tm2', __V2) =
            checkApx
              (__G, tm2, (Uni __L), (Next __L),
                "Right-hand side of ascription must be a type or a kind") in
          let (tm1', __U1) =
            checkApx (__G, tm1, __V2, __L, "Ascription did not hold") in
          let _ =
            addDelayed
              (fun () ->
                 filterLevel
                   (tm, __L, 2,
                     "Ascription can only be applied to objects and type families")) in
          ((hastype (tm1', tm2')), __U1, __V2, __L)
      | (__G, omitted r) ->
          let __L = newLVar () in
          let __V = newCVar () in
          let __U = newCVar () in
          ((((omitapx (__U, __V, __L, r)), __U, __V, __L))
            (* guaranteed not to be used if L is type *))
    let rec checkApx (__G) tm (__V) (__L) location_msg =
      let (tm', __U', __V', __L') = inferApx (__G, tm) in
      try matchUni (__L, __L'); match__ (__V, __V'); (tm', __U')
      with
      | Unify problem_msg ->
          let r = termRegion tm in
          let (tm'', U'') =
            checkApx (__G, (omitted r), __V, __L, location_msg) in
          let _ = addDelayed (fun () -> makeGroundUni __L'; ()) in
          ((((mismatch (tm', tm'', location_msg, problem_msg)), U''))
            (* just in case *))
    let rec inferApxDec (__G) (dec (name, tm, r)) =
      let (tm', __V1) =
        checkApx
          (__G, tm, (Uni Type), Kind,
            "Classifier in declaration must be a type") in
      let __D = Dec (name, __V1) in ((dec (name, tm', r)), __D)
    let rec inferApxJob __15__ __16__ =
      match (__15__, __16__) with
      | (__G, jnothing) -> jnothing
      | (__G, jand (j1, j2)) ->
          jand ((inferApxJob (__G, j1)), (inferApxJob (__G, j2)))
      | (__G, jwithctx (g, j)) ->
          let rec ia =
            function
            | Null -> (__G, Null)
            | Decl (g, tm) ->
                let (__G', g') = ia g in
                let _ = clearDelayed () in
                let (tm', __D) = inferApxDec (__G', tm) in
                let _ = runDelayed () in
                ((Decl (__G', __D)), (Decl (g', tm'))) in
          let (__G', g') = ia g in jwithctx (g', (inferApxJob (__G', j)))
      | (__G, jterm tm) ->
          let _ = clearDelayed () in
          let (tm', __U, __V, __L) = inferApx (__G, tm) in
          let _ =
            filterLevel
              (tm', __L, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jterm tm'
      | (__G, jclass tm) ->
          let _ = clearDelayed () in
          let __L = newLVar () in
          let (tm', __V) =
            checkApx
              (__G, tm, (Uni __L), (Next __L),
                "The term in this position must be a type or a kind") in
          let _ =
            filterLevel
              (tm', (Next __L), 3,
                "The term in this position must be a type or a kind") in
          let _ = runDelayed () in jclass tm'
      | (__G, jof (tm1, tm2)) ->
          let _ = clearDelayed () in
          let __L = newLVar () in
          let (tm2', __V2) =
            checkApx
              (__G, tm2, (Uni __L), (Next __L),
                "The term in this position must be a type or a kind") in
          let (tm1', __U1) =
            checkApx
              (__G, tm1, __V2, __L, "Ascription in declaration did not hold") in
          let _ =
            filterLevel
              (tm1', __L, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jof (tm1', tm2')
      | (__G, jof' (tm1, __V)) ->
          let _ = clearDelayed () in
          let __L = newLVar () in
          let (__V2, _) = Apx.classToApx __V in
          let (tm1', __U1) =
            checkApx
              (__G, tm1, __V2, __L, "Ascription in declaration did not hold") in
          let _ =
            filterLevel
              (tm1', __L, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jof' (tm1', __V)
    let rec ctxToApx =
      function
      | IntSyn.Null -> IntSyn.Null
      | Decl (__G, NDec x) -> IntSyn.Decl ((ctxToApx __G), (NDec x))
      | Decl (__G, Dec (name, __V)) ->
          let (__V', _) = Apx.classToApx __V in
          IntSyn.Decl ((ctxToApx __G), (Dec (name, __V')))
    let rec inferApxJob' (__G) t = inferApxJob ((ctxToApx __G), t)
    open IntSyn
    type __Job =
      | JNothing 
      | JAnd of (__Job * __Job) 
      | JWithCtx of (IntSyn.__Dec IntSyn.__Ctx * __Job) 
      | JTerm of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Exp *
      IntSyn.__Uni) 
      | JClass of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Uni) 
      | JOf of ((IntSyn.__Exp * Paths.occExp) * (IntSyn.__Exp * Paths.occExp)
      * IntSyn.__Uni) 
    type __Bidi =
      | Elim of (IntSyn.__Sub -> IntSyn.__Spine -> IntSyn.__Exp) 
      | Intro of IntSyn.__Exp 
    let rec elimSub (__E) s s' (__S) = __E ((comp (s, s')), __S)
    let rec elimApp (__E) (__U) s (__S) =
      __E (s, (App ((EClo (__U, s)), __S)))
    let rec bvarElim n s (__S) =
      match bvarSub (n, s) with
      | Idx n' -> Root ((BVar n'), __S)
      | Exp (__U) -> Redex (__U, __S)
    let rec fvarElim name (__V) s s' (__S) =
      Root ((FVar (name, __V, (comp (s, s')))), __S)
    let rec redexElim (__U) s (__S) = Redex ((EClo (__U, s)), __S)
    let rec headElim =
      function
      | BVar n -> bvarElim n
      | FVar fv -> fvarElim fv
      | NSDef d -> redexElim (constDef d)
      | __H ->
          (match conDecStatus (headConDec __H) with
           | Foreign (csid, f) -> (fun s -> fun (__S) -> f __S)
           | _ -> (fun s -> fun (__S) -> Root (__H, __S)))
    let rec evarElim (EVar _ as X) s (__S) =
      EClo (__X, (Whnf.spineToSub (__S, s)))
    let rec etaExpandW __17__ __18__ =
      match (__17__, __18__) with
      | (__E, (Pi (((Dec (_, Va) as D), _), Vr), s)) ->
          let __U1 = etaExpand ((bvarElim 1), (Va, (comp (s, shift)))) in
          let __D' = decSub (__D, s) in
          Lam
            (__D',
              (etaExpand
                 ((elimApp ((elimSub (__E, shift)), __U1)), (Vr, (dot1 s)))))
      | (__E, _) -> __E (id, Nil)
    let rec etaExpand (__E) (__Vs) =
      etaExpandW (__E, (Whnf.whnfExpandDef __Vs))
    let rec toElim =
      function | Elim (__E) -> __E | Intro (__U) -> redexElim __U
    let rec toIntro __19__ __20__ =
      match (__19__, __20__) with
      | (Elim (__E), __Vs) -> etaExpand (__E, __Vs)
      | (Intro (__U), __Vs) -> __U
    let rec addImplicit1W (__G) (__E) (Pi ((Dec (_, Va), _), Vr), s) i =
      let __X = Whnf.newLoweredEVar (__G, (Va, s)) in
      addImplicit
        (__G, (elimApp (__E, __X)), (Vr, (Whnf.dotEta ((Exp __X), s))),
          (i - 1))(* >= 1 *)
    let rec addImplicit __21__ __22__ __23__ __24__ =
      match (__21__, __22__, __23__, __24__) with
      | (__G, __E, __Vs, 0) -> (__E, (EClo __Vs))
      | (__G, __E, __Vs, i) ->
          addImplicit1W (__G, __E, (Whnf.whnfExpandDef __Vs), i)
    let rec reportConstraints (Xnames) =
      try
        match Print.evarCnstrsToStringOpt Xnames with
        | NONE -> ()
        | Some constr -> print (("Constraints:\n" ^ constr) ^ "\n")
      with | Names.Unprintable -> print "%_constraints unprintable_%\n"
    let rec reportInst (Xnames) =
      try Msg.message ((Print.evarInstToString Xnames) ^ "\n")
      with | Names.Unprintable -> Msg.message "%_unifier unprintable_%\n"
    let rec delayMismatch (__G) (__V1) (__V2) r2 location_msg problem_msg =
      addDelayed
        (fun () ->
           let __Xs =
             Abstract.collectEVars
               (__G, (__V2, id),
                 (Abstract.collectEVars (__G, (__V1, id), nil))) in
           let Xnames =
             List.map
               (fun (__X) -> (__X, (Names.evarName (IntSyn.Null, __X)))) __Xs in
           let V1fmt = formatExp (__G, __V1) in
           let V2fmt = formatExp (__G, __V2) in
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
             match Print.evarCnstrsToStringOpt Xnames with
             | NONE -> F.makestring_fmt diff
             | Some cnstrs ->
                 ((F.makestring_fmt diff) ^ "\nConstraints:\n") ^ cnstrs in
           error
             (r2,
               ((((("Type mismatch\n" ^ diff) ^ "\n") ^ problem_msg) ^ "\n")
                  ^ location_msg)))
    let rec delayAmbiguous (__G) (__U) r msg =
      addDelayed
        (fun () ->
           let Ufmt = formatExp (__G, __U) in
           let amb =
             F.HVbox [F.String "Inferred:"; F.Space; formatExp (__G, __U)] in
           error
             (r,
               ((((^) "Ambiguous reconstruction\n" F.makestring_fmt amb) ^
                   "\n")
                  ^ msg)))
    let rec unifyIdem x =
      let _ = Unify.reset () in
      let _ =
        try Unify.unify x with | Unify _ as e -> (Unify.unwind (); raise e) in
      let _ = Unify.reset () in ((())
        (* this reset should be unnecessary -- for safety only *))
    let rec unifiableIdem x =
      let _ = Unify.reset () in
      let ok = Unify.unifiable x in
      let _ = if ok then Unify.reset () else Unify.unwind () in ((ok)
        (* this reset should be unnecessary -- for safety only *))
    type __TraceMode =
      | Progressive 
      | Omniscient 
    let trace = ref false__
    let traceMode = ref Omniscient
    let rec report f =
      match !traceMode with
      | Progressive -> f ()
      | Omniscient -> addDelayed f
    let rec reportMismatch (__G) (__Vs1) (__Vs2) problem_msg =
      report
        (fun () ->
           let __Xs =
             Abstract.collectEVars
               (__G, __Vs2, (Abstract.collectEVars (__G, __Vs1, nil))) in
           let Xnames =
             List.map
               (fun (__X) -> (__X, (Names.evarName (IntSyn.Null, __X)))) __Xs in
           let eqnsFmt =
             F.HVbox
               [F.String "|?";
               F.Space;
               formatExp (__G, (EClo __Vs1));
               F.Break;
               F.String "=";
               F.Space;
               formatExp (__G, (EClo __Vs2))] in
           let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
           let _ = reportConstraints Xnames in
           let _ =
             Msg.message
               ((("Failed: " ^ problem_msg) ^ "\n") ^
                  "Continuing with subterm replaced by _\n") in
           ())
    let rec reportUnify' (__G) (__Vs1) (__Vs2) =
      let __Xs =
        Abstract.collectEVars
          (__G, __Vs2, (Abstract.collectEVars (__G, __Vs1, nil))) in
      let Xnames =
        List.map (fun (__X) -> (__X, (Names.evarName (IntSyn.Null, __X))))
          __Xs in
      let eqnsFmt =
        F.HVbox
          [F.String "|?";
          F.Space;
          formatExp (__G, (EClo __Vs1));
          F.Break;
          F.String "=";
          F.Space;
          formatExp (__G, (EClo __Vs2))] in
      let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
      let _ =
        try unifyIdem (__G, __Vs1, __Vs2)
        with
        | Unify msg as e ->
            (Msg.message
               ((("Failed: " ^ msg) ^ "\n") ^
                  "Continuing with subterm replaced by _\n");
             raise e) in
      let _ = reportInst Xnames in let _ = reportConstraints Xnames in ()
    let rec reportUnify (__G) (__Vs1) (__Vs2) =
      match !traceMode with
      | Progressive -> reportUnify' (__G, __Vs1, __Vs2)
      | Omniscient ->
          (try unifyIdem (__G, __Vs1, __Vs2)
           with
           | Unify msg as e ->
               (reportMismatch (__G, __Vs1, __Vs2, msg); raise e))
    let rec reportInfer' __25__ __26__ __27__ __28__ =
      match (__25__, __26__, __27__, __28__) with
      | (__G, omitexact (_, _, r), __U, __V) ->
          let __Xs =
            Abstract.collectEVars
              (__G, (__U, id), (Abstract.collectEVars (__G, (__V, id), nil))) in
          let Xnames =
            List.map
              (fun (__X) -> (__X, (Names.evarName (IntSyn.Null, __X)))) __Xs in
          let omit =
            F.HVbox
              [F.String "|-";
              F.Space;
              F.String "_";
              F.Space;
              F.String "==>";
              F.Space;
              formatExp (__G, __U);
              F.Break;
              F.String ":";
              F.Space;
              formatExp (__G, __V)] in
          let _ = Msg.message ((F.makestring_fmt omit) ^ "\n") in
          let _ = reportConstraints Xnames in ()
      | (__G, mismatch (tm1, tm2, _, _), __U, __V) ->
          reportInfer' (__G, tm2, __U, __V)
      | (__G, hastype _, __U, __V) -> ()
      | (__G, tm, __U, __V) ->
          let __Xs =
            Abstract.collectEVars
              (__G, (__U, id), (Abstract.collectEVars (__G, (__V, id), nil))) in
          let Xnames =
            List.map
              (fun (__X) -> (__X, (Names.evarName (IntSyn.Null, __X)))) __Xs in
          let judg =
            F.HVbox
              [F.String "|-";
              F.Space;
              formatExp (__G, __U);
              F.Break;
              F.String ":";
              F.Space;
              formatExp (__G, __V)] in
          let _ = Msg.message ((F.makestring_fmt judg) ^ "\n") in
          let _ = reportConstraints Xnames in ()
    let rec reportInfer x = report (fun () -> reportInfer' x)
    let rec inferExactN __29__ __30__ =
      match (__29__, __30__) with
      | (__G, (internal (__U, __V, r) as tm)) -> (tm, (Intro __U), __V)
      | (__G, (constant (__H, r) as tm)) ->
          let cd = headConDec __H in
          let (__E, __V) =
            addImplicit
              (__G, (headElim __H), ((conDecType cd), id), (conDecImp cd)) in
          (tm, (Elim __E), __V)
      | (__G, (bvar (k, r) as tm)) ->
          let Dec (_, __V) = ctxDec (__G, k) in
          (tm, (Elim (bvarElim k)), __V)
      | (__G, (evar (name, r) as tm)) ->
          let (__X, __V) =
            try getEVar (name, false__)
            with
            | Apx.Ambiguous ->
                let (__X, __V) = getEVar (name, true__) in
                (delayAmbiguous
                   (__G, __V, r, "Free variable has ambiguous type");
                 (__X, __V)) in
          let s = Shift (ctxLength __G) in
          (((tm, (Elim (elimSub ((evarElim __X), s))), (EClo (__V, s))))
            (* externally EVars are raised elim forms *)
            (* necessary? -kw *))
      | (__G, (fvar (name, r) as tm)) ->
          let __V =
            try getFVarType (name, false__)
            with
            | Apx.Ambiguous ->
                let __V = getFVarType (name, true__) in
                (delayAmbiguous
                   (__G, __V, r, "Free variable has ambiguous type");
                 __V) in
          let s = Shift (ctxLength __G) in
          (((tm, (Elim (fvarElim (name, __V, s))), (EClo (__V, s))))
            (* necessary? -kw *))
      | (__G, (typ r as tm)) -> (tm, (Intro (Uni Type)), (Uni Kind))
      | (__G, arrow (tm1, tm2)) ->
          let (((tm1', __B1, _))(* Uni Type *)) =
            inferExact (__G, tm1) in
          let __D = Dec (NONE, (toIntro (__B1, ((Uni Type), id)))) in
          let (tm2', __B2, __L) = inferExact (__G, tm2) in
          let __V2 = toIntro (__B2, (__L, id)) in
          ((arrow (tm1', tm2')),
            (Intro (Pi ((__D, No), (EClo (__V2, shift))))), __L)
      | (__G, pi (tm1, tm2)) ->
          let (tm1', __D) = inferExactDec (__G, tm1) in
          let (tm2', __B2, __L) = inferExact ((Decl (__G, __D)), tm2) in
          let __V2 = toIntro (__B2, (__L, id)) in
          ((pi (tm1', tm2')), (Intro (Pi ((__D, Maybe), __V2))), __L)
      | (__G, lam (tm1, tm2)) ->
          let (tm1', __D) = inferExactDec (__G, tm1) in
          let (tm2', __B2, __V2) = inferExact ((Decl (__G, __D)), tm2) in
          let __U2 = toIntro (__B2, (__V2, id)) in
          ((lam (tm1', tm2')), (Intro (Lam (__D, __U2))),
            (Pi ((__D, Maybe), __V2)))
      | (__G, app (tm1, tm2)) ->
          let (tm1', __B1, __V1) = inferExact (__G, tm1) in
          let __E1 = toElim __B1 in
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (__V1, id) in
          let (tm2', __B2) =
            checkExact
              (__G, tm2, (Va, s),
                "Argument type did not match function domain type\n(Index object(s) did not match)") in
          let __U2 = toIntro (__B2, (Va, s)) in
          ((app (tm1', tm2')), (Elim (elimApp (__E1, __U2))),
            (EClo (Vr, (Whnf.dotEta ((Exp __U2), s)))))
      | (__G, hastype (tm1, tm2)) ->
          let (tm2', __B2, __L) = inferExact (__G, tm2) in
          let __V = toIntro (__B2, (__L, id)) in
          let (tm1', __B1) =
            checkExact
              (__G, tm1, (__V, id),
                "Ascription did not hold\n(Index object(s) did not match)") in
          ((hastype (tm1', tm2')), __B1, __V)
      | (__G, mismatch (tm1, tm2, location_msg, problem_msg)) ->
          let (tm1', _, __V1) = inferExact (__G, tm1) in
          let (tm2', __B, __V) = inferExactN (__G, tm2) in
          let _ =
            if !trace
            then reportMismatch (__G, (__V1, id), (__V, id), problem_msg)
            else () in
          let _ =
            delayMismatch
              (__G, __V1, __V, (termRegion tm2'), location_msg, problem_msg) in
          ((mismatch (tm1', tm2', location_msg, problem_msg)), __B, __V)
      | (__G, omitapx (__U, __V, __L, r)) ->
          let __V' =
            try Apx.apxToClass (__G, __V, __L, false__)
            with
            | Apx.Ambiguous ->
                let __V' = Apx.apxToClass (__G, __V, __L, true__) in
                (delayAmbiguous
                   (__G, __V', r,
                     ("Omitted term has ambiguous " ^
                        ((match Apx.whnfUni __L with
                          | Level 1 -> "type"
                          | Level 2 -> "kind"
                          | Level 3 -> "hyperkind")
                        (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                        (* FIX: this violates an invariant in printing *))));
                 __V') in
          let __U' =
            try Apx.apxToExact (__G, __U, (__V', id), false__)
            with
            | Apx.Ambiguous ->
                let __U' = Apx.apxToExact (__G, __U, (__V', id), true__) in
                (delayAmbiguous
                   (__G, __U', r,
                     (("Omitted " ^
                         (match Apx.whnfUni __L with
                          | Level 2 -> "type"
                          | Level 3 -> "kind"))
                        ^ " is ambiguous"));
                 __U') in
          ((omitexact (__U', __V', r)), (Intro __U'), __V')
    let rec inferExact (__G) tm =
      if not (!trace)
      then inferExactN (__G, tm)
      else
        (let (tm', __B', __V') = inferExactN (__G, tm) in
         reportInfer (__G, tm', (toIntro (__B', (__V', id))), __V');
         (tm', __B', __V'))
    let rec inferExactDec (__G) (dec (name, tm, r)) =
      let (((tm', __B1, _))(* Uni Type *)) =
        inferExact (__G, tm) in
      let __V1 = toIntro (__B1, ((Uni Type), id)) in
      let __D = Dec (name, __V1) in ((dec (name, tm', r)), __D)
    let rec checkExact1 __31__ __32__ __33__ =
      match (__31__, __32__, __33__) with
      | (__G, lam (dec (name, tm1, r), tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', __B1, _))(* Uni Type *)), ok1) =
            unifyExact (__G, tm1, (Va, s)) in
          let __V1 = toIntro (__B1, ((Uni Type), id)) in
          let __D = Dec (name, __V1) in
          let ((tm2', __B2, __V2), ok2) =
            if ok1
            then checkExact1 ((Decl (__G, __D)), tm2, (Vr, (dot1 s)))
            else ((inferExact ((Decl (__G, __D)), tm2)), false__) in
          let __U2 = toIntro (__B2, (__V2, id)) in
          (((lam ((dec (name, tm1', r)), tm2')), (Intro (Lam (__D, __U2))),
             (Pi ((__D, Maybe), __V2))), ok2)
      | (__G, hastype (tm1, tm2), Vhs) ->
          let ((tm2', __B2, __L), ok2) = unifyExact (__G, tm2, Vhs) in
          let __V = toIntro (__B2, (__L, id)) in
          let (tm1', __B1) =
            checkExact
              (__G, tm1, (__V, id),
                "Ascription did not hold\n(Index object(s) did not match)") in
          (((hastype (tm1', tm2')), __B1, __V), ok2)
      | (__G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
          let (tm1', _, __V1) = inferExact (__G, tm1) in
          let ((tm2', __B, __V), ok2) = checkExact1 (__G, tm2, Vhs) in
          let _ =
            delayMismatch
              (__G, __V1, __V, (termRegion tm2'), location_msg, problem_msg) in
          (((mismatch (tm1', tm2', location_msg, problem_msg)), __B, __V),
            ok2)
      | (__G, omitapx (((__U, __V, __L, r))(* = Vhs *)),
         Vhs) ->
          let __V' = EClo Vhs in
          let __U' =
            try Apx.apxToExact (__G, __U, Vhs, false__)
            with
            | Apx.Ambiguous ->
                let __U' = Apx.apxToExact (__G, __U, Vhs, true__) in
                (delayAmbiguous
                   (__G, __U', r,
                     (("Omitted " ^
                         (match Apx.whnfUni __L with
                          | Level 2 -> "type"
                          | Level 3 -> "kind"))
                        ^ " is ambiguous"));
                 __U') in
          (((omitexact (__U', __V', r)), (Intro __U'), __V'), true__)
      | (__G, tm, Vhs) ->
          let (tm', __B', __V') = inferExact (__G, tm) in
          ((tm', __B', __V'), (unifiableIdem (__G, Vhs, (__V', id))))
    let rec checkExact (__G) tm (__Vs) location_msg =
      if not (!trace)
      then
        let ((tm', __B', __V'), ok) = checkExact1 (__G, tm, __Vs) in
        (if ok
         then (tm', __B')
         else
           (try
              ((unifyIdem (__G, (__V', id), __Vs); raise Match)
              (* can't happen *))
            with
            | Unify problem_msg ->
                let r = termRegion tm in
                let __U' = toIntro (__B', (__V', id)) in
                let (Uapx, Vapx, Lapx) = Apx.exactToApx (__U', __V') in
                let ((((((tm'', B'', _))(* Vs *)), _))
                  (* true *)) =
                  checkExact1 (__G, (omitapx (Uapx, Vapx, Lapx, r)), __Vs) in
                let _ =
                  delayMismatch
                    (__G, __V', (EClo __Vs), r, location_msg, problem_msg) in
                ((mismatch (tm', tm'', location_msg, problem_msg)), B'')))
      else
        (let (tm', __B', __V') = inferExact (__G, tm) in
         try reportUnify (__G, (__V', id), __Vs); (tm', __B')
         with
         | Unify problem_msg ->
             let r = termRegion tm in
             let __U' = toIntro (__B', (__V', id)) in
             let (Uapx, Vapx, Lapx) = Apx.exactToApx (__U', __V') in
             let (tm'', B'') =
               checkExact
                 (__G, (omitapx (Uapx, Vapx, Lapx, r)), __Vs, location_msg) in
             let _ =
               delayMismatch
                 (__G, __V', (EClo __Vs), r, location_msg, problem_msg) in
             ((mismatch (tm', tm'', location_msg, problem_msg)), B''))
    let rec unifyExact __34__ __35__ __36__ =
      match (__34__, __35__, __36__) with
      | (__G, arrow (tm1, tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', __B1, _))(* Uni Type *)), ok1) =
            unifyExact (__G, tm1, (Va, s)) in
          let __V1 = toIntro (__B1, ((Uni Type), id)) in
          let __D = Dec (NONE, __V1) in
          let (tm2', __B2, __L) = inferExact (__G, tm2) in
          let __V2 = toIntro (__B2, (__L, id)) in
          (((arrow (tm1', tm2')),
             (Intro (Pi ((__D, No), (EClo (__V2, shift))))), __L),
            (ok1 &&
               (unifiableIdem
                  ((Decl (__G, __D)), (Vr, (dot1 s)), (__V2, shift)))))
      | (__G, pi (dec (name, tm1, r), tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', __B1, _))(* Uni Type *)), ok1) =
            unifyExact (__G, tm1, (Va, s)) in
          let __V1 = toIntro (__B1, ((Uni Type), id)) in
          let __D = Dec (name, __V1) in
          let ((tm2', __B2, __L), ok2) =
            if ok1
            then unifyExact ((Decl (__G, __D)), tm2, (Vr, (dot1 s)))
            else ((inferExact ((Decl (__G, __D)), tm2)), false__) in
          let __V2 = toIntro (__B2, (__L, id)) in
          (((pi ((dec (name, tm1', r)), tm2')),
             (Intro (Pi ((__D, Maybe), __V2))), __L), ok2)
      | (__G, hastype (tm1, tm2), Vhs) ->
          let (((tm2', _, _))(* Uni L *)(* Uni (Next L) *))
            = inferExact (__G, tm2) in
          let ((tm1', __B, __L), ok1) = unifyExact (__G, tm1, Vhs) in
          (((((hastype (tm1', tm2')), __B, __L), ok1))
            (* Vh : L by invariant *))
      | (__G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
          let (tm1', _, __L1) = inferExact (__G, tm1) in
          let ((tm2', __B, __L), ok2) = unifyExact (__G, tm2, Vhs) in
          let _ =
            delayMismatch
              (__G, __L1, __L, (termRegion tm2'), location_msg, problem_msg) in
          (((mismatch (tm1', tm2', location_msg, problem_msg)), __B, __L),
            ok2)
      | (__G, omitapx
         (((__V, __L, nL, r))(* = Vhs *)(* Next L *)),
         Vhs) ->
          let __L' = Apx.apxToClass (__G, __L, nL, false__) in
          let __V' = EClo Vhs in
          (((((omitexact (__V', __L', r)), (Intro __V'), __L'), true__))
            (* cannot raise Ambiguous *))
      | (__G, tm, Vhs) ->
          let (tm', __B', __L') = inferExact (__G, tm) in
          let __V' = toIntro (__B', (__L', id)) in
          ((tm', __B', __L'), (unifiableIdem (__G, Vhs, (__V', id))))
      (* lam impossible *)
    let rec occElim __37__ __38__ __39__ __40__ =
      match (__37__, __38__, __39__, __40__) with
      | (constant (__H, r), os, rs, i) ->
          let r' = List.foldr Paths.join r rs in
          ((((Paths.root
                (r', (Paths.leaf r), (conDecImp (headConDec __H)), i, os)),
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
          ((Paths.leaf r'), r')(* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)
    let rec occIntro =
      function
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
          let (oc, r) = occElim (tm, Paths.nils, nil, 0) in (((oc, r))
            (* still doesn't work quite right for the location -> occurrence map? *))
    let rec inferExactJob __41__ __42__ =
      match (__41__, __42__) with
      | (__G, jnothing) -> JNothing
      | (__G, jand (j1, j2)) ->
          JAnd ((inferExactJob (__G, j1)), (inferExactJob (__G, j2)))
      | (__G, jwithctx (g, j)) ->
          let rec ie =
            function
            | Null -> (__G, Null)
            | Decl (g, tm) ->
                let (__G', Gresult) = ie g in
                let (_, __D) = inferExactDec (__G', tm) in
                ((Decl (__G', __D)), (Decl (Gresult, __D))) in
          let (__G', Gresult) = ie g in
          JWithCtx (Gresult, (inferExactJob (__G', j)))
      | (__G, jterm tm) ->
          let (tm', __B, __V) = inferExact (__G, tm) in
          let __U = toIntro (__B, (__V, id)) in
          let (oc, r) = occIntro tm' in
          let rec iu =
            function
            | Uni (Type) -> Kind
            | Pi (_, __V) -> iu __V
            | Root _ -> Type
            | Redex (__V, _) -> iu __V
            | Lam (_, __V) -> iu __V
            | EClo (__V, _) -> iu __V in
          ((JTerm ((__U, oc), __V, (iu __V)))
            (* others impossible *))
      | (__G, jclass tm) ->
          let (tm', __B, __L) = inferExact (__G, tm) in
          let __V = toIntro (__B, (__L, id)) in
          let (oc, r) = occIntro tm' in
          let (Uni (__L), _) = Whnf.whnf (__L, id) in JClass ((__V, oc), __L)
      | (__G, jof (tm1, tm2)) ->
          let (tm2', __B2, __L2) = inferExact (__G, tm2) in
          let __V2 = toIntro (__B2, (__L2, id)) in
          let (tm1', __B1) =
            checkExact
              (__G, tm1, (__V2, id),
                ("Ascription in declaration did not hold\n" ^
                   "(Index object(s) did not match)")) in
          let __U1 = toIntro (__B1, (__V2, id)) in
          let (oc2, r2) = occIntro tm2' in
          let (oc1, r1) = occIntro tm1' in
          let (Uni (__L2), _) = Whnf.whnf (__L2, id) in
          JOf ((__U1, oc1), (__V2, oc2), __L2)
      | (__G, jof' (tm1, __V2)) ->
          let (tm1', __B1) =
            checkExact
              (__G, tm1, (__V2, id),
                ("Ascription in declaration did not hold\n" ^
                   "(Index object(s) did not match)")) in
          let __U1 = toIntro (__B1, (__V2, id)) in
          let (oc1, r1) = occIntro tm1' in
          ((JOf ((__U1, oc1), (__V2, oc1), Type))
            (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
            (*          val (oc2, r2) = occIntro tm2' *)
            (*          val (Uni L2, _) = Whnf.whnf (L2, id) *))
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
    let rec recon j = queryMode := false__; recon' j
    let rec reconQuery j = queryMode := true__; recon' j
    let rec reconWithCtx' (__G) j =
      let _ = Apx.varReset () in
      let _ = varReset () in
      let j' = inferApxJob' (__G, j) in
      let _ = clearDelayed () in
      let j'' = inferExactJob (__G, j') in
      let _ = runDelayed () in ((j'')
        (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
        (* context must already have called resetErrors *)
        (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *))
    let rec reconWithCtx (__G) j =
      queryMode := false__; reconWithCtx' (__G, j)
    let rec reconQueryWithCtx (__G) j =
      queryMode := true__; reconWithCtx' (__G, j)
    let rec internalInst x = raise Match
    let rec externalInst x = raise Match
  end ;;
