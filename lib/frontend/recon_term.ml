
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
  end (* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)
(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)
(*! structure Paths : PATHS !*)
(* term *) (* variable declaration *)
(* lower case id *) (* upper case id *)
(* quoted id, currently not parsed *)
(* string constant *)
(* unconditionally interpreted as such *)
(* type, region for "type" *)
(* tm -> tm *) (* tm <- tm *)
(* {d} tm *) (* [d] tm *)
(* tm tm *) (* tm : tm *)
(* _ as object, region for "_" *)
(* region for "{dec}" "[dec]" etc. *)
(* id : tm | _ : tm *)
(* id | _  (type omitted) *)
(* signature EXTSYN *)
(* signature RECON_TERM
   provides the interface to type reconstruction seen by Twelf 
*)
module type RECON_TERM  =
  sig
    (*! structure IntSyn : INTSYN !*)
    include EXTSYN
    exception Error of string 
    val resetErrors : string -> unit
    (* filename -fp *)
    val checkErrors : Paths.region -> unit
    type __TraceMode =
      | Progressive 
      | Omniscient 
    val trace : bool ref
    val traceMode : __TraceMode ref
    (* Reconstruction jobs *)
    type nonrec job
    val jnothing : job
    val jand : (job * job) -> job
    val jwithctx : (dec IntSyn.__Ctx * job) -> job
    val jterm : term -> job
    val jclass : term -> job
    val jof : (term * term) -> job
    val jof' : (term * IntSyn.__Exp) -> job
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
    val reconWithCtx : (IntSyn.dctx * job) -> __Job
    val reconQueryWithCtx : (IntSyn.dctx * job) -> __Job
    val termRegion : term -> Paths.region
    val decRegion : dec -> Paths.region
    val ctxRegion : dec IntSyn.__Ctx -> Paths.region option
    (* unimplemented for the moment *)
    val internalInst : 'a -> 'b
    val externalInst : 'a -> 'b
  end;;




(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)
(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)
module ReconTerm(ReconTerm:sig
                             (*! structure IntSyn' : INTSYN !*)
                             module Names : NAMES
                             module Approx : APPROX
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Abstract : ABSTRACT
                             module Print : PRINT
                             module StringTree : TABLE
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             (*! structure Paths' : PATHS !*)
                             (*! sharing Approx.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             (*! sharing Unify.IntSyn = IntSyn' !*)
                             (*! sharing Abstract.IntSyn = IntSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn' !*)
                             (*! structure CSManager : CS_MANAGER !*)
                             (*! sharing CSManager.IntSyn = IntSyn' !*)
                             module Msg : MSG
                           end) : RECON_TERM =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Paths = Paths' !*)
    module F = Print.Formatter
    module Apx = Approx
    (* Error handling *)
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
    let rec exceeds = function | (i, None) -> false__ | (i, Some j) -> i > j
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
    (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the "[Loading file ..." message and the closing "]",
     instead of after the closing "]".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as "[Loading file ...", terribly confusing the Emacs error parsing code.
   *)
    let rec chatterOneNewline () =
      if ((!Global.chatter) = 1) && ((!errorCount) = 1)
      then Msg.message "\n"
      else ()
    let rec fatalError (r, msg) =
      ((!) ((:=) errorCount) errorCount) + 1;
      chatterOneNewline ();
      Msg.message (((^) ((!errorFileName) ^ ":") Paths.wrap (r, msg)) ^ "\n");
      die r
    let rec error (r, msg) =
      ((!) ((:=) errorCount) errorCount) + 1;
      chatterOneNewline ();
      Msg.message (((^) ((!errorFileName) ^ ":") Paths.wrap (r, msg)) ^ "\n");
      if exceeds ((!errorCount), (!errorThreshold)) then die r else ()
    let rec formatExp (__g, __u) =
      try Print.formatExp (__g, __u)
      with | Names.Unprintable -> F.String "%_unprintable_%"
    (* this is a hack, i know *)
    let queryMode = ref false__
    open IntSyn
    let rec headConDec =
      function
      | Const c -> sgnLookup c
      | Skonst c -> sgnLookup c
      | Def d -> sgnLookup d
      | NSDef d -> sgnLookup d
      | FgnConst (_, cd) -> cd
    (* others impossible by invariant *)
    (* lowerType (__g, (__v, s)) = (__g', a)
     if   G0 |- __v : type and __g |- s : G0
     and  __g |- __v[s] = {{G1}} a : type
     then __g' = __g, G1 *)
    let rec lowerTypeW =
      function
      | (__g, (Pi ((__d, _), __v), s)) ->
          let __d' = decSub (__d, s) in lowerType ((Decl (__g, __d')), (__v, (dot1 s)))
      | (__g, __Vs) -> (__g, (EClo __Vs))
    let rec lowerType (__g, __Vs) = lowerTypeW (__g, (Whnf.whnfExpandDef __Vs))
    (* raiseType (__g, __v) = {{__g}} __v *)
    let rec raiseType =
      function
      | (Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (Pi ((__d, Maybe), __v)))
    (* open IntSyn *)
    let (evarApxTable : Apx.__Exp StringTree.__Table) = StringTree.new__ 0
    let (fvarApxTable : Apx.__Exp StringTree.__Table) = StringTree.new__ 0
    let (fvarTable : IntSyn.__Exp StringTree.__Table) = StringTree.new__ 0
    let rec varReset () =
      StringTree.clear evarApxTable;
      StringTree.clear fvarApxTable;
      StringTree.clear fvarTable
    let rec getEVarTypeApx name =
      match StringTree.lookup evarApxTable name with
      | Some (__v) -> __v
      | None ->
          (match Names.getEVarOpt name with
           | Some (EVar (_, _, __v, _)) ->
               let (((__v', _))(* Type *)) = Apx.classToApx __v in
               (StringTree.insert evarApxTable (name, __v'); __v')
           | None ->
               let __v = Apx.newCVar () in
               (StringTree.insert evarApxTable (name, __v); __v))
    let rec getFVarTypeApx name =
      match StringTree.lookup fvarApxTable name with
      | Some (__v) -> __v
      | None ->
          let __v = Apx.newCVar () in
          (StringTree.insert fvarApxTable (name, __v); __v)
    let rec getEVar (name, allowed) =
      match Names.getEVarOpt name with
      | Some (EVar (_, __g, __v, _) as x) -> (x, (raiseType (__g, __v)))
      | None ->
          let __v = Option.valOf (StringTree.lookup evarApxTable name) in
          let __v' = Apx.apxToClass (IntSyn.Null, __v, Apx.Type, allowed) in
          let (__g'', __v'') = lowerType (IntSyn.Null, (__v', IntSyn.id)) in
          let x = IntSyn.newEVar (__g'', __v'') in
          (Names.addEVar (x, name); (x, __v'))
    let rec getFVarType (name, allowed) =
      match StringTree.lookup fvarTable name with
      | Some (__v) -> __v
      | None ->
          let __v = Option.valOf (StringTree.lookup fvarApxTable name) in
          let __v' = Apx.apxToClass (IntSyn.Null, __v, Apx.Type, allowed) in
          (StringTree.insert fvarTable (name, __v'); __v')
    (* External syntax of terms *)
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
    let rec backarrow (tm1, tm2) = arrow (tm2, tm1)
    (* for now *)
    let rec dec0 (nameOpt, r) = dec (nameOpt, (omitted r), r)
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
      | internal (__u, __v, r) -> r
      | constant (H, r) -> r
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
      | omitapx (__u, __v, __l, r) -> r
      | omitexact (__u, __v, r) -> r
    let rec decRegion (dec (name, tm, r)) = r
    let rec ctxRegion =
      function
      | IntSyn.Null -> None
      | Decl (g, tm) -> ctxRegion' (g, (decRegion tm))
    let rec ctxRegion' =
      function
      | (IntSyn.Null, r) -> Some r
      | (Decl (g, tm), r) -> ctxRegion' (g, (Paths.join (r, (decRegion tm))))
    open Apx
    type __Ctx = IntSyn.__Ctx
    type __Dec =
      | Dec of (string option * __Exp) 
      | NDec of string option 
    (* Phase 1:
       Try to determine an approximate type/kind and level for each subterm.
       In cases where there's a mismatch, it's generally better not to report
       it immediately, but rather to wait until after the exact phase, so that
       the error message can mention more precise type information.  So instead
       the bad subterm is wrapped in a `mismatch' constructor, which also
       supplies a replacement (always an `omitted' in the current implementation)
       so that the invariant that the entire term is approximately well-typed
       after phase 1 is satisfied even in the presence of the error.
     *)
    (* inferApx (__g, tm, false) = (tm', __u, __v, __l)
       pre: __g is an approximate context
            tm is an approximate subject
       post: tm' is an approximate subject
             __u is an approximate subject
             __v is an approximate classifier
             __l is an approximate universe
             __g |- __u ~:~ __v ~:~ __l
             termToExp tm' = __u

       inferApx (__g, tm, true) = (tm', __u, __v, __l)
       pre: __g is an approximate context
            tm is an approximate classifier
       post: tm' is an approximate classifier
             __u is an approximate classifier
             __v is an approximate classifier
             __l is an approximate universe
             __g |- __u ~:~ __v ~:~ __l
             termToExp tm' = __u
     *)
    let rec filterLevel (tm, __l, max, msg) =
      let notGround = makeGroundUni __l in
      let Level i = whnfUni __l in
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
    let rec findOmitted (__g, qid, r) =
      error
        (r,
          ((^) "Undeclared identifier " Names.qidToString
             (valOf (Names.constUndef qid))));
      omitted r
    let rec findBVar' =
      function
      | (Null, name, k) -> None
      | (Decl (__g, Dec (None, _)), name, k) -> findBVar' (__g, name, (k + 1))
      | (Decl (__g, NDec _), name, k) -> findBVar' (__g, name, (k + 1))
      | (Decl (__g, Dec (Some name', _)), name, k) ->
          if name = name' then Some k else findBVar' (__g, name, (k + 1))
    let rec findBVar fc (__g, qid, r) =
      match Names.unqualified qid with
      | None -> fc (__g, qid, r)
      | Some name ->
          (match findBVar' (__g, name, 1) with
           | None -> fc (__g, qid, r)
           | Some k -> bvar (k, r))
    let rec findConst fc (__g, qid, r) =
      match Names.constLookup qid with
      | None -> fc (__g, qid, r)
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
    let rec findCSConst fc (__g, qid, r) =
      match Names.unqualified qid with
      | None -> fc (__g, qid, r)
      | Some name ->
          (match CSManager.parse name with
           | None -> fc (__g, qid, r)
           | Some (cs, conDec) ->
               constant ((IntSyn.FgnConst (cs, conDec)), r))
    let rec findEFVar fc (__g, qid, r) =
      match Names.unqualified qid with
      | None -> fc (__g, qid, r)
      | Some name -> (if !queryMode then evar else fvar) (name, r)
    let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x
    let rec findUCID x =
      findBVar (findConst (findCSConst (findEFVar findOmitted))) x
    let rec findQUID x = findConst (findCSConst findOmitted) x
    let rec inferApx =
      function
      | (__g, (internal (__u, __v, r) as tm)) ->
          let (__u', __v', __l') = exactToApx (__u, __v) in (tm, __u', __v', __l')
      | (__g, (lcid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__g, (findLCID (__g, qid, r)))
      | (__g, (ucid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__g, (findUCID (__g, qid, r)))
      | (__g, (quid (ids, name, r) as tm)) ->
          let qid = Names.Qid (ids, name) in
          inferApx (__g, (findQUID (__g, qid, r)))
      | (__g, (scon (name, r) as tm)) ->
          (match CSManager.parse name with
           | None ->
               (error (r, "Strings unsupported in current signature");
                inferApx (__g, (omitted r)))
           | Some (cs, conDec) ->
               inferApx (__g, (constant ((IntSyn.FgnConst (cs, conDec)), r))))
      | (__g, (constant (H, r) as tm)) ->
          let cd = headConDec H in
          let (__u', __v', __l') =
            exactToApx
              ((IntSyn.Root (H, IntSyn.Nil)), (IntSyn.conDecType cd)) in
          let rec dropImplicit =
            function
            | (__v, 0) -> __v
            | (Arrow (_, __v), i) -> dropImplicit (__v, (i - 1)) in
          let __v'' = dropImplicit (__v', (IntSyn.conDecImp cd)) in
          (tm, __u', __v'', __l')
      | (__g, (bvar (k, r) as tm)) ->
          let Dec (_, __v) = IntSyn.ctxLookup (__g, k) in
          (tm, Undefined, __v, Type)
      | (__g, (evar (name, r) as tm)) ->
          (tm, Undefined, (getEVarTypeApx name), Type)
      | (__g, (fvar (name, r) as tm)) ->
          (tm, Undefined, (getFVarTypeApx name), Type)
      | (__g, (typ r as tm)) -> (tm, (Uni Type), (Uni Kind), Hyperkind)
      | (__g, arrow (tm1, tm2)) ->
          let __l = newLVar () in
          let (tm1', V1) =
            checkApx
              (__g, tm1, (Uni Type), Kind,
                "Left-hand side of arrow must be a type") in
          let (tm2', V2) =
            checkApx
              (__g, tm2, (Uni __l), (Next __l),
                "Right-hand side of arrow must be a type or a kind") in
          ((arrow (tm1', tm2')), (Arrow (V1, V2)), (Uni __l), (Next __l))
      | (__g, pi (tm1, tm2)) ->
          let (tm1', (Dec (_, V1) as __d)) = inferApxDec (__g, tm1) in
          let __l = newLVar () in
          let (tm2', V2) =
            checkApx
              ((Decl (__g, __d)), tm2, (Uni __l), (Next __l),
                "Body of pi must be a type or a kind") in
          ((pi (tm1', tm2')), (Arrow (V1, V2)), (Uni __l), (Next __l))
      | (__g, (lam (tm1, tm2) as tm)) ->
          let (tm1', (Dec (_, V1) as __d)) = inferApxDec (__g, tm1) in
          let (tm2', __U2, V2, L2) = inferApx ((Decl (__g, __d)), tm2) in
          ((lam (tm1', tm2')), __U2, (Arrow (V1, V2)), L2)
      | (__g, (app (tm1, tm2) as tm)) ->
          let __l = newLVar () in
          let Va = newCVar () in
          let Vr = newCVar () in
          let (tm1', __U1) =
            checkApx
              (__g, tm1, (Arrow (Va, Vr)), __l,
                "Non-function was applied to an argument") in
          let (tm2', _) =
            checkApx
              (__g, tm2, Va, Type,
                "Argument type did not match function domain type") in
          ((((app (tm1', tm2')), __U1, Vr, __l))
            (* probably a confusing message if the problem is the level: *))
      | (__g, (hastype (tm1, tm2) as tm)) ->
          let __l = newLVar () in
          let (tm2', V2) =
            checkApx
              (__g, tm2, (Uni __l), (Next __l),
                "Right-hand side of ascription must be a type or a kind") in
          let (tm1', __U1) =
            checkApx (__g, tm1, V2, __l, "Ascription did not hold") in
          let _ =
            addDelayed
              (function
               | () ->
                   filterLevel
                     (tm, __l, 2,
                       "Ascription can only be applied to objects and type families")) in
          ((hastype (tm1', tm2')), __U1, V2, __l)
      | (__g, omitted r) ->
          let __l = newLVar () in
          let __v = newCVar () in
          let __u = newCVar () in ((((omitapx (__u, __v, __l, r)), __u, __v, __l))
            (* guaranteed not to be used if __l is type *))
    let rec checkApx (__g, tm, __v, __l, location_msg) =
      let (tm', __u', __v', __l') = inferApx (__g, tm) in
      try matchUni (__l, __l'); match__ (__v, __v'); (tm', __u')
      with
      | Unify problem_msg ->
          let r = termRegion tm in
          let (tm'', __u'') = checkApx (__g, (omitted r), __v, __l, location_msg) in
          let _ = addDelayed (function | () -> (makeGroundUni __l'; ())) in
          ((((mismatch (tm', tm'', location_msg, problem_msg)), __u''))
            (* just in case *))
    let rec inferApxDec (__g, dec (name, tm, r)) =
      let (tm', V1) =
        checkApx
          (__g, tm, (Uni Type), Kind,
            "Classifier in declaration must be a type") in
      let __d = Dec (name, V1) in ((dec (name, tm', r)), __d)
    let rec inferApxJob =
      function
      | (__g, jnothing) -> jnothing
      | (__g, jand (j1, j2)) ->
          jand ((inferApxJob (__g, j1)), (inferApxJob (__g, j2)))
      | (__g, jwithctx (g, j)) ->
          let rec ia =
            function
            | Null -> (__g, Null)
            | Decl (g, tm) ->
                let (__g', g') = ia g in
                let _ = clearDelayed () in
                let (tm', __d) = inferApxDec (__g', tm) in
                let _ = runDelayed () in ((Decl (__g', __d)), (Decl (g', tm'))) in
          let (__g', g') = ia g in jwithctx (g', (inferApxJob (__g', j)))
      | (__g, jterm tm) ->
          let _ = clearDelayed () in
          let (tm', __u, __v, __l) = inferApx (__g, tm) in
          let _ =
            filterLevel
              (tm', __l, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jterm tm'
      | (__g, jclass tm) ->
          let _ = clearDelayed () in
          let __l = newLVar () in
          let (tm', __v) =
            checkApx
              (__g, tm, (Uni __l), (Next __l),
                "The term in this position must be a type or a kind") in
          let _ =
            filterLevel
              (tm', (Next __l), 3,
                "The term in this position must be a type or a kind") in
          let _ = runDelayed () in jclass tm'
      | (__g, jof (tm1, tm2)) ->
          let _ = clearDelayed () in
          let __l = newLVar () in
          let (tm2', V2) =
            checkApx
              (__g, tm2, (Uni __l), (Next __l),
                "The term in this position must be a type or a kind") in
          let (tm1', __U1) =
            checkApx
              (__g, tm1, V2, __l, "Ascription in declaration did not hold") in
          let _ =
            filterLevel
              (tm1', __l, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jof (tm1', tm2')
      | (__g, jof' (tm1, __v)) ->
          let _ = clearDelayed () in
          let __l = newLVar () in
          let (V2, _) = Apx.classToApx __v in
          let (tm1', __U1) =
            checkApx
              (__g, tm1, V2, __l, "Ascription in declaration did not hold") in
          let _ =
            filterLevel
              (tm1', __l, 2,
                "The term in this position must be an object or a type family") in
          let _ = runDelayed () in jof' (tm1', __v)
    let rec ctxToApx =
      function
      | IntSyn.Null -> IntSyn.Null
      | Decl (__g, NDec x) -> IntSyn.Decl ((ctxToApx __g), (NDec x))
      | Decl (__g, Dec (name, __v)) ->
          let (__v', _) = Apx.classToApx __v in
          IntSyn.Decl ((ctxToApx __g), (Dec (name, __v')))
    let rec inferApxJob' (__g, t) = inferApxJob ((ctxToApx __g), t)
    (* open Apx *)
    open IntSyn
    (* Final reconstruction job syntax *)
    type __Job =
      | JNothing 
      | JAnd of (__Job * __Job) 
      | JWithCtx of (IntSyn.__Dec IntSyn.__Ctx * __Job) 
      | JTerm of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Exp *
      IntSyn.__Uni) 
      | JClass of ((IntSyn.__Exp * Paths.occExp) * IntSyn.__Uni) 
      | JOf of ((IntSyn.__Exp * Paths.occExp) * (IntSyn.__Exp * Paths.occExp)
      * IntSyn.__Uni) 
    (* This little datatype makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term __u if
       E (s, S) = __u[s] @ S *)
    type __Bidi =
      | Elim of ((IntSyn.__Sub * IntSyn.__Spine) -> IntSyn.__Exp) 
      | Intro of IntSyn.__Exp 
    let rec elimSub (E, s) = function | (s', S) -> E ((comp (s, s')), S)
    let rec elimApp (E, __u) =
      function | (s, S) -> E (s, (App ((EClo (__u, s)), S)))
    let rec bvarElim n =
      function
      | (s, S) ->
          (match bvarSub (n, s) with
           | Idx n' -> Root ((BVar n'), S)
           | Exp (__u) -> Redex (__u, S))
    let rec fvarElim (name, __v, s) =
      function | (s', S) -> Root ((FVar (name, __v, (comp (s, s')))), S)
    let rec redexElim (__u) = function | (s, S) -> Redex ((EClo (__u, s)), S)
    (* headElim (H) = E
     assumes H not Proj _ *)
    let rec headElim =
      function
      | BVar n -> bvarElim n
      | FVar fv -> fvarElim fv
      | NSDef d -> redexElim (constDef d)
      | H ->
          (match conDecStatus (headConDec H) with
           | Foreign (csid, f) -> (function | (s, S) -> f S)
           | _ -> (function | (s, S) -> Root (H, S)))
    (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[__g]] __v) *)
    let rec evarElim (EVar _ as x) =
      function | (s, S) -> EClo (x, (Whnf.spineToSub (S, s)))
    let rec etaExpandW =
      function
      | (E, (Pi (((Dec (_, Va) as __d), _), Vr), s)) ->
          let __U1 = etaExpand ((bvarElim 1), (Va, (comp (s, shift)))) in
          let __d' = decSub (__d, s) in
          Lam
            (__d',
              (etaExpand
                 ((elimApp ((elimSub (E, shift)), __U1)), (Vr, (dot1 s)))))
      | (E, _) -> E (id, Nil)
    let rec etaExpand (E, __Vs) = etaExpandW (E, (Whnf.whnfExpandDef __Vs))
    (* preserves redices *)
    let rec toElim = function | Elim (E) -> E | Intro (__u) -> redexElim __u
    let rec toIntro =
      function | (Elim (E), __Vs) -> etaExpand (E, __Vs) | (Intro (__u), __Vs) -> __u
    let rec addImplicit1W (__g, E, (Pi ((Dec (_, Va), _), Vr), s), i) =
      let x = Whnf.newLoweredEVar (__g, (Va, s)) in
      addImplicit
        (__g, (elimApp (E, x)), (Vr, (Whnf.dotEta ((Exp x), s))), (i - 1))
    let rec addImplicit =
      function
      | (__g, E, __Vs, 0) -> (E, (EClo __Vs))
      | (__g, E, __Vs, i) -> addImplicit1W (__g, E, (Whnf.whnfExpandDef __Vs), i)
    (* >= 1 *)
    (* Report mismatches after the entire process finishes -- yields better
     error messages *)
    let rec reportConstraints (Xnames) =
      try
        match Print.evarCnstrsToStringOpt Xnames with
        | None -> ()
        | Some constr -> print (("Constraints:\n" ^ constr) ^ "\n")
      with | Names.Unprintable -> print "%_constraints unprintable_%\n"
    let rec reportInst (Xnames) =
      try Msg.message ((Print.evarInstToString Xnames) ^ "\n")
      with | Names.Unprintable -> Msg.message "%_unifier unprintable_%\n"
    let rec delayMismatch (__g, V1, V2, r2, location_msg, problem_msg) =
      addDelayed
        (function
         | () ->
             let __Xs =
               Abstract.collectEVars
                 (__g, (V2, id), (Abstract.collectEVars (__g, (V1, id), nil))) in
             let Xnames =
               List.map
                 (function | x -> (x, (Names.evarName (IntSyn.Null, x)))) __Xs in
             let V1fmt = formatExp (__g, V1) in
             let V2fmt = formatExp (__g, V2) in
             let diff =
               F.Vbox0 0 1
                 [F.String "Expected:";
                 F.space;
                 V2fmt;
                 F.Break;
                 F.String "Inferred:";
                 F.space;
                 V1fmt] in
             let diff =
               match Print.evarCnstrsToStringOpt Xnames with
               | None -> F.makestring_fmt diff
               | Some cnstrs ->
                   ((F.makestring_fmt diff) ^ "\nConstraints:\n") ^ cnstrs in
             error
               (r2,
                 ((((("Type mismatch\n" ^ diff) ^ "\n") ^ problem_msg) ^ "\n")
                    ^ location_msg)))
    let rec delayAmbiguous (__g, __u, r, msg) =
      addDelayed
        (function
         | () ->
             let Ufmt = formatExp (__g, __u) in
             let amb =
               F.hVbox [F.String "Inferred:"; F.space; formatExp (__g, __u)] in
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
    (* tracing code *)
    type __TraceMode =
      | Progressive 
      | Omniscient 
    let trace = ref false__
    let traceMode = ref Omniscient
    let rec report f =
      match !traceMode with
      | Progressive -> f ()
      | Omniscient -> addDelayed f
    let rec reportMismatch (__g, Vs1, Vs2, problem_msg) =
      report
        (function
         | () ->
             let __Xs =
               Abstract.collectEVars
                 (__g, Vs2, (Abstract.collectEVars (__g, Vs1, nil))) in
             let Xnames =
               List.map
                 (function | x -> (x, (Names.evarName (IntSyn.Null, x)))) __Xs in
             let eqnsFmt =
               F.hVbox
                 [F.String "|?";
                 F.space;
                 formatExp (__g, (EClo Vs1));
                 F.Break;
                 F.String "=";
                 F.space;
                 formatExp (__g, (EClo Vs2))] in
             let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
             let _ = reportConstraints Xnames in
             let _ =
               Msg.message
                 ((("Failed: " ^ problem_msg) ^ "\n") ^
                    "Continuing with subterm replaced by _\n") in
             ())
    let rec reportUnify' (__g, Vs1, Vs2) =
      let __Xs =
        Abstract.collectEVars (__g, Vs2, (Abstract.collectEVars (__g, Vs1, nil))) in
      let Xnames =
        List.map (function | x -> (x, (Names.evarName (IntSyn.Null, x)))) __Xs in
      let eqnsFmt =
        F.hVbox
          [F.String "|?";
          F.space;
          formatExp (__g, (EClo Vs1));
          F.Break;
          F.String "=";
          F.space;
          formatExp (__g, (EClo Vs2))] in
      let _ = Msg.message ((F.makestring_fmt eqnsFmt) ^ "\n") in
      let _ =
        try unifyIdem (__g, Vs1, Vs2)
        with
        | Unify msg as e ->
            (Msg.message
               ((("Failed: " ^ msg) ^ "\n") ^
                  "Continuing with subterm replaced by _\n");
             raise e) in
      let _ = reportInst Xnames in let _ = reportConstraints Xnames in ()
    let rec reportUnify (__g, Vs1, Vs2) =
      match !traceMode with
      | Progressive -> reportUnify' (__g, Vs1, Vs2)
      | Omniscient ->
          (try unifyIdem (__g, Vs1, Vs2)
           with
           | Unify msg as e -> (reportMismatch (__g, Vs1, Vs2, msg); raise e))
    let rec reportInfer' =
      function
      | (__g, omitexact (_, _, r), __u, __v) ->
          let __Xs =
            Abstract.collectEVars
              (__g, (__u, id), (Abstract.collectEVars (__g, (__v, id), nil))) in
          let Xnames =
            List.map (function | x -> (x, (Names.evarName (IntSyn.Null, x))))
              __Xs in
          let omit =
            F.hVbox
              [F.String "|-";
              F.space;
              F.String "_";
              F.space;
              F.String "==>";
              F.space;
              formatExp (__g, __u);
              F.Break;
              F.String ":";
              F.space;
              formatExp (__g, __v)] in
          let _ = Msg.message ((F.makestring_fmt omit) ^ "\n") in
          let _ = reportConstraints Xnames in ()
      | (__g, mismatch (tm1, tm2, _, _), __u, __v) -> reportInfer' (__g, tm2, __u, __v)
      | (__g, hastype _, __u, __v) -> ()
      | (__g, tm, __u, __v) ->
          let __Xs =
            Abstract.collectEVars
              (__g, (__u, id), (Abstract.collectEVars (__g, (__v, id), nil))) in
          let Xnames =
            List.map (function | x -> (x, (Names.evarName (IntSyn.Null, x))))
              __Xs in
          let judg =
            F.hVbox
              [F.String "|-";
              F.space;
              formatExp (__g, __u);
              F.Break;
              F.String ":";
              F.space;
              formatExp (__g, __v)] in
          let _ = Msg.message ((F.makestring_fmt judg) ^ "\n") in
          let _ = reportConstraints Xnames in ()
    let rec reportInfer x = report (function | () -> reportInfer' x)
    (* inferExact (__g, tm) = (tm', __u, __v)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = __u-
       and  __u : __v
       and  __u, __v are most general such
       effect: as for unification *)
    let rec inferExactN =
      function
      | (__g, (internal (__u, __v, r) as tm)) -> (tm, (Intro __u), __v)
      | (__g, (constant (H, r) as tm)) ->
          let cd = headConDec H in
          let (E, __v) =
            addImplicit
              (__g, (headElim H), ((conDecType cd), id), (conDecImp cd)) in
          (tm, (Elim E), __v)
      | (__g, (bvar (k, r) as tm)) ->
          let Dec (_, __v) = ctxDec (__g, k) in (tm, (Elim (bvarElim k)), __v)
      | (__g, (evar (name, r) as tm)) ->
          let (x, __v) =
            try getEVar (name, false__)
            with
            | Apx.Ambiguous ->
                let (x, __v) = getEVar (name, true__) in
                (delayAmbiguous (__g, __v, r, "Free variable has ambiguous type");
                 (x, __v)) in
          let s = Shift (ctxLength __g) in
          (((tm, (Elim (elimSub ((evarElim x), s))), (EClo (__v, s))))
            (* externally EVars are raised elim forms *)
            (* necessary? -kw *))
      | (__g, (fvar (name, r) as tm)) ->
          let __v =
            try getFVarType (name, false__)
            with
            | Apx.Ambiguous ->
                let __v = getFVarType (name, true__) in
                (delayAmbiguous (__g, __v, r, "Free variable has ambiguous type");
                 __v) in
          let s = Shift (ctxLength __g) in
          (((tm, (Elim (fvarElim (name, __v, s))), (EClo (__v, s))))
            (* necessary? -kw *))
      | (__g, (typ r as tm)) -> (tm, (Intro (Uni Type)), (Uni Kind))
      | (__g, arrow (tm1, tm2)) ->
          let (((tm1', B1, _))(* Uni Type *)) =
            inferExact (__g, tm1) in
          let __d = Dec (None, (toIntro (B1, ((Uni Type), id)))) in
          let (tm2', B2, __l) = inferExact (__g, tm2) in
          let V2 = toIntro (B2, (__l, id)) in
          ((arrow (tm1', tm2')), (Intro (Pi ((__d, No), (EClo (V2, shift))))),
            __l)
      | (__g, pi (tm1, tm2)) ->
          let (tm1', __d) = inferExactDec (__g, tm1) in
          let (tm2', B2, __l) = inferExact ((Decl (__g, __d)), tm2) in
          let V2 = toIntro (B2, (__l, id)) in
          ((pi (tm1', tm2')), (Intro (Pi ((__d, Maybe), V2))), __l)
      | (__g, lam (tm1, tm2)) ->
          let (tm1', __d) = inferExactDec (__g, tm1) in
          let (tm2', B2, V2) = inferExact ((Decl (__g, __d)), tm2) in
          let __U2 = toIntro (B2, (V2, id)) in
          ((lam (tm1', tm2')), (Intro (Lam (__d, __U2))), (Pi ((__d, Maybe), V2)))
      | (__g, app (tm1, tm2)) ->
          let (tm1', B1, V1) = inferExact (__g, tm1) in
          let E1 = toElim B1 in
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (V1, id) in
          let (tm2', B2) =
            checkExact
              (__g, tm2, (Va, s),
                "Argument type did not match function domain type\n(Index object(s) did not match)") in
          let __U2 = toIntro (B2, (Va, s)) in
          ((app (tm1', tm2')), (Elim (elimApp (E1, __U2))),
            (EClo (Vr, (Whnf.dotEta ((Exp __U2), s)))))
      | (__g, hastype (tm1, tm2)) ->
          let (tm2', B2, __l) = inferExact (__g, tm2) in
          let __v = toIntro (B2, (__l, id)) in
          let (tm1', B1) =
            checkExact
              (__g, tm1, (__v, id),
                "Ascription did not hold\n(Index object(s) did not match)") in
          ((hastype (tm1', tm2')), B1, __v)
      | (__g, mismatch (tm1, tm2, location_msg, problem_msg)) ->
          let (tm1', _, V1) = inferExact (__g, tm1) in
          let (tm2', B, __v) = inferExactN (__g, tm2) in
          let _ =
            if !trace
            then reportMismatch (__g, (V1, id), (__v, id), problem_msg)
            else () in
          let _ =
            delayMismatch
              (__g, V1, __v, (termRegion tm2'), location_msg, problem_msg) in
          ((mismatch (tm1', tm2', location_msg, problem_msg)), B, __v)
      | (__g, omitapx (__u, __v, __l, r)) ->
          let __v' =
            try Apx.apxToClass (__g, __v, __l, false__)
            with
            | Apx.Ambiguous ->
                let __v' = Apx.apxToClass (__g, __v, __l, true__) in
                (delayAmbiguous
                   (__g, __v', r,
                     ("Omitted term has ambiguous " ^
                        ((match Apx.whnfUni __l with
                          | Level 1 -> "type"
                          | Level 2 -> "kind"
                          | Level 3 -> "hyperkind")
                        (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                        (* FIX: this violates an invariant in printing *))));
                 __v') in
          let __u' =
            try Apx.apxToExact (__g, __u, (__v', id), false__)
            with
            | Apx.Ambiguous ->
                let __u' = Apx.apxToExact (__g, __u, (__v', id), true__) in
                (delayAmbiguous
                   (__g, __u', r,
                     (("Omitted " ^
                         (match Apx.whnfUni __l with
                          | Level 2 -> "type"
                          | Level 3 -> "kind"))
                        ^ " is ambiguous"));
                 __u') in
          ((omitexact (__u', __v', r)), (Intro __u'), __v')
    let rec inferExact (__g, tm) =
      if not (!trace)
      then inferExactN (__g, tm)
      else
        (let (tm', B', __v') = inferExactN (__g, tm) in
         reportInfer (__g, tm', (toIntro (B', (__v', id))), __v'); (tm', B', __v'))
    let rec inferExactDec (__g, dec (name, tm, r)) =
      let (((tm', B1, _))(* Uni Type *)) =
        inferExact (__g, tm) in
      let V1 = toIntro (B1, ((Uni Type), id)) in
      let __d = Dec (name, V1) in ((dec (name, tm', r)), __d)
    let rec checkExact1 =
      function
      | (__g, lam (dec (name, tm1, r), tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', B1, _))(* Uni Type *)), ok1) =
            unifyExact (__g, tm1, (Va, s)) in
          let V1 = toIntro (B1, ((Uni Type), id)) in
          let __d = Dec (name, V1) in
          let ((tm2', B2, V2), ok2) =
            if ok1
            then checkExact1 ((Decl (__g, __d)), tm2, (Vr, (dot1 s)))
            else ((inferExact ((Decl (__g, __d)), tm2)), false__) in
          let __U2 = toIntro (B2, (V2, id)) in
          (((lam ((dec (name, tm1', r)), tm2')), (Intro (Lam (__d, __U2))),
             (Pi ((__d, Maybe), V2))), ok2)
      | (__g, hastype (tm1, tm2), Vhs) ->
          let ((tm2', B2, __l), ok2) = unifyExact (__g, tm2, Vhs) in
          let __v = toIntro (B2, (__l, id)) in
          let (tm1', B1) =
            checkExact
              (__g, tm1, (__v, id),
                "Ascription did not hold\n(Index object(s) did not match)") in
          (((hastype (tm1', tm2')), B1, __v), ok2)
      | (__g, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
          let (tm1', _, V1) = inferExact (__g, tm1) in
          let ((tm2', B, __v), ok2) = checkExact1 (__g, tm2, Vhs) in
          let _ =
            delayMismatch
              (__g, V1, __v, (termRegion tm2'), location_msg, problem_msg) in
          (((mismatch (tm1', tm2', location_msg, problem_msg)), B, __v), ok2)
      | (__g, omitapx (((__u, __v, __l, r))(* = Vhs *)), Vhs) ->
          let __v' = EClo Vhs in
          let __u' =
            try Apx.apxToExact (__g, __u, Vhs, false__)
            with
            | Apx.Ambiguous ->
                let __u' = Apx.apxToExact (__g, __u, Vhs, true__) in
                (delayAmbiguous
                   (__g, __u', r,
                     (("Omitted " ^
                         (match Apx.whnfUni __l with
                          | Level 2 -> "type"
                          | Level 3 -> "kind"))
                        ^ " is ambiguous"));
                 __u') in
          (((omitexact (__u', __v', r)), (Intro __u'), __v'), true__)
      | (__g, tm, Vhs) ->
          let (tm', B', __v') = inferExact (__g, tm) in
          ((tm', B', __v'), (unifiableIdem (__g, Vhs, (__v', id))))
    let rec checkExact (__g, tm, __Vs, location_msg) =
      if not (!trace)
      then
        let ((tm', B', __v'), ok) = checkExact1 (__g, tm, __Vs) in
        (if ok
         then (tm', B')
         else
           (try
              ((unifyIdem (__g, (__v', id), __Vs); raise Match)
              (* can't happen *))
            with
            | Unify problem_msg ->
                let r = termRegion tm in
                let __u' = toIntro (B', (__v', id)) in
                let (Uapx, Vapx, Lapx) = Apx.exactToApx (__u', __v') in
                let ((((((tm'', B'', _))(* __Vs *)), _))
                  (* true *)) =
                  checkExact1 (__g, (omitapx (Uapx, Vapx, Lapx, r)), __Vs) in
                let _ =
                  delayMismatch
                    (__g, __v', (EClo __Vs), r, location_msg, problem_msg) in
                ((mismatch (tm', tm'', location_msg, problem_msg)), B'')))
      else
        (let (tm', B', __v') = inferExact (__g, tm) in
         try reportUnify (__g, (__v', id), __Vs); (tm', B')
         with
         | Unify problem_msg ->
             let r = termRegion tm in
             let __u' = toIntro (B', (__v', id)) in
             let (Uapx, Vapx, Lapx) = Apx.exactToApx (__u', __v') in
             let (tm'', B'') =
               checkExact
                 (__g, (omitapx (Uapx, Vapx, Lapx, r)), __Vs, location_msg) in
             let _ =
               delayMismatch (__g, __v', (EClo __Vs), r, location_msg, problem_msg) in
             ((mismatch (tm', tm'', location_msg, problem_msg)), B''))
    let rec unifyExact =
      function
      | (__g, arrow (tm1, tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', B1, _))(* Uni Type *)), ok1) =
            unifyExact (__g, tm1, (Va, s)) in
          let V1 = toIntro (B1, ((Uni Type), id)) in
          let __d = Dec (None, V1) in
          let (tm2', B2, __l) = inferExact (__g, tm2) in
          let V2 = toIntro (B2, (__l, id)) in
          (((arrow (tm1', tm2')), (Intro (Pi ((__d, No), (EClo (V2, shift))))),
             __l),
            (ok1 &&
               (unifiableIdem ((Decl (__g, __d)), (Vr, (dot1 s)), (V2, shift)))))
      | (__g, pi (dec (name, tm1, r), tm2), Vhs) ->
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs in
          let ((((tm1', B1, _))(* Uni Type *)), ok1) =
            unifyExact (__g, tm1, (Va, s)) in
          let V1 = toIntro (B1, ((Uni Type), id)) in
          let __d = Dec (name, V1) in
          let ((tm2', B2, __l), ok2) =
            if ok1
            then unifyExact ((Decl (__g, __d)), tm2, (Vr, (dot1 s)))
            else ((inferExact ((Decl (__g, __d)), tm2)), false__) in
          let V2 = toIntro (B2, (__l, id)) in
          (((pi ((dec (name, tm1', r)), tm2')),
             (Intro (Pi ((__d, Maybe), V2))), __l), ok2)
      | (__g, hastype (tm1, tm2), Vhs) ->
          let (((tm2', _, _))(* Uni __l *)(* Uni (Next __l) *))
            = inferExact (__g, tm2) in
          let ((tm1', B, __l), ok1) = unifyExact (__g, tm1, Vhs) in
          (((((hastype (tm1', tm2')), B, __l), ok1))
            (* Vh : __l by invariant *))
      | (__g, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) ->
          let (tm1', _, L1) = inferExact (__g, tm1) in
          let ((tm2', B, __l), ok2) = unifyExact (__g, tm2, Vhs) in
          let _ =
            delayMismatch
              (__g, L1, __l, (termRegion tm2'), location_msg, problem_msg) in
          (((mismatch (tm1', tm2', location_msg, problem_msg)), B, __l), ok2)
      | (__g, omitapx
         (((__v, __l, nL, r))(* = Vhs *)(* Next __l *)),
         Vhs) ->
          let __l' = Apx.apxToClass (__g, __l, nL, false__) in
          let __v' = EClo Vhs in
          (((((omitexact (__v', __l', r)), (Intro __v'), __l'), true__))
            (* cannot raise Ambiguous *))
      | (__g, tm, Vhs) ->
          let (tm', B', __l') = inferExact (__g, tm) in
          let __v' = toIntro (B', (__l', id)) in
          ((tm', B', __l'), (unifiableIdem (__g, Vhs, (__v', id))))(* lam impossible *)
    let rec occElim =
      function
      | (constant (H, r), os, rs, i) ->
          let r' = List.foldr Paths.join r rs in
          ((((Paths.root
                (r', (Paths.leaf r), (conDecImp (headConDec H)), i, os)), r'))
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
    let rec inferExactJob =
      function
      | (__g, jnothing) -> JNothing
      | (__g, jand (j1, j2)) ->
          JAnd ((inferExactJob (__g, j1)), (inferExactJob (__g, j2)))
      | (__g, jwithctx (g, j)) ->
          let rec ie =
            function
            | Null -> (__g, Null)
            | Decl (g, tm) ->
                let (__g', Gresult) = ie g in
                let (_, __d) = inferExactDec (__g', tm) in
                ((Decl (__g', __d)), (Decl (Gresult, __d))) in
          let (__g', Gresult) = ie g in
          JWithCtx (Gresult, (inferExactJob (__g', j)))
      | (__g, jterm tm) ->
          let (tm', B, __v) = inferExact (__g, tm) in
          let __u = toIntro (B, (__v, id)) in
          let (oc, r) = occIntro tm' in
          let rec iu =
            function
            | Uni (Type) -> Kind
            | Pi (_, __v) -> iu __v
            | Root _ -> Type
            | Redex (__v, _) -> iu __v
            | Lam (_, __v) -> iu __v
            | EClo (__v, _) -> iu __v in
          ((JTerm ((__u, oc), __v, (iu __v)))
            (* others impossible *))
      | (__g, jclass tm) ->
          let (tm', B, __l) = inferExact (__g, tm) in
          let __v = toIntro (B, (__l, id)) in
          let (oc, r) = occIntro tm' in
          let (Uni (__l), _) = Whnf.whnf (__l, id) in JClass ((__v, oc), __l)
      | (__g, jof (tm1, tm2)) ->
          let (tm2', B2, L2) = inferExact (__g, tm2) in
          let V2 = toIntro (B2, (L2, id)) in
          let (tm1', B1) =
            checkExact
              (__g, tm1, (V2, id),
                ("Ascription in declaration did not hold\n" ^
                   "(Index object(s) did not match)")) in
          let __U1 = toIntro (B1, (V2, id)) in
          let (oc2, r2) = occIntro tm2' in
          let (oc1, r1) = occIntro tm1' in
          let (Uni (L2), _) = Whnf.whnf (L2, id) in
          JOf ((__U1, oc1), (V2, oc2), L2)
      | (__g, jof' (tm1, V2)) ->
          let (tm1', B1) =
            checkExact
              (__g, tm1, (V2, id),
                ("Ascription in declaration did not hold\n" ^
                   "(Index object(s) did not match)")) in
          let __U1 = toIntro (B1, (V2, id)) in
          let (oc1, r1) = occIntro tm1' in
          ((JOf ((__U1, oc1), (V2, oc1), Type))
            (*          val (tm2', B2, L2) = inferExact (__g, tm2)
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
    (* Invariant, __g must be named! *)
    let rec reconWithCtx' (__g, j) =
      let _ = Apx.varReset () in
      let _ = varReset () in
      let j' = inferApxJob' (__g, j) in
      let _ = clearDelayed () in
      let j'' = inferExactJob (__g, j') in
      let _ = runDelayed () in ((j'')
        (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
        (* context must already have called resetErrors *)
        (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *))
    let rec reconWithCtx (__g, j) = queryMode := false__; reconWithCtx' (__g, j)
    let rec reconQueryWithCtx (__g, j) =
      queryMode := true__; reconWithCtx' (__g, j)
    let rec internalInst x = raise Match
    let rec externalInst x = raise Match
  end ;;
