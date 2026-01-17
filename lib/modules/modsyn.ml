
module type MODSYN  =
  sig
    module Names :
    ((NAMES)(* Syntax for elaborated modules *)(* Author: Kevin Watkins *)
    (*! structure IntSyn : INTSYN !*))
    exception Error of
      ((string)(*! structure Paths : PATHS !*)) 
    val abbrevify : (IntSyn.cid * IntSyn.__ConDec) -> IntSyn.__ConDec
    val strictify : IntSyn.__ConDec -> IntSyn.__ConDec
    type nonrec module__
    val installStruct :
      (IntSyn.__StrDec * module__ * Names.namespace option *
        ((IntSyn.cid * (string * Paths.occConDec option)) -> unit) * bool) ->
        ((unit)(* action *)(*
  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.ConDec -> IntSyn.ConDec
  *))
    val installSig :
      (module__ * Names.namespace option *
        ((IntSyn.cid * (string * Paths.occConDec option)) -> unit) * bool) ->
        ((unit)(* action *))
    val instantiateModule :
      (module__ *
        (Names.namespace -> (IntSyn.cid * IntSyn.__ConDec) -> IntSyn.__ConDec))
        -> ((module__)(* Names.namespace -> transform *))
    val abstractModule :
      (Names.namespace * IntSyn.mid option) ->
        ((module__)(* Extract some entries of the current global signature table in order
     to create a self-contained module.
  *))
    val reset : unit -> unit
    val installSigDef : (string * module__) -> unit
    val lookupSigDef :
      string ->
        ((module__)(* Error if would shadow *)) option
    val sigDefSize : unit -> int
    val resetFrom : int -> unit
  end;;




module ModSyn(ModSyn:sig
                       module Global : GLOBAL
                       module Names' : NAMES
                       module Origins : ORIGINS
                       module Whnf : WHNF
                       module Strict : STRICT
                       module IntTree : TABLE
                       module HashTable :
                       ((TABLE)(* Syntax for elaborated modules *)
                       (* Author: Kevin Watkins *)(*! structure IntSyn' : INTSYN !*)
                       (*! sharing Names'.IntSyn = IntSyn' !*)(*! structure Paths' : PATHS !*)
                       (*! sharing Origins.Paths = Paths' !*)(*! sharing Whnf.IntSyn = IntSyn' !*)
                       (*! sharing Strict.IntSyn = IntSyn' !*))
                     end) : MODSYN =
  struct
    module Names =
      ((Names')(*! structure IntSyn = IntSyn' !*))
    module I = ((IntSyn)(*! structure Paths = Paths' !*))
    exception Error of string 
    type __ConstInfo =
      | ConstInfo of (IntSyn.__ConDec * Names.Fixity.fixity * (string list *
      string list) option * (string * Paths.occConDec option)) 
    type __StructInfo =
      | StructInfo of IntSyn.__StrDec 
    type nonrec module__ =
      (((__StructInfo)(* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for the constant (if any)
     2. a map from mids to structure entries containing
          a. a structure declaration entry (IntSyn.StrDec)
          b. the namespace of the structure
     3. the top-level namespace of the module *))
        IntTree.__Table * __ConstInfo IntTree.__Table * Names.namespace)
    type nonrec action =
      (IntSyn.cid * (string * Paths.occConDec option)) -> unit
    type nonrec transform = (IntSyn.cid * IntSyn.__ConDec) -> IntSyn.__ConDec
    let rec mapExpConsts
      ((f)(* invariant: U in nf, result in nf *)) (U) =
      let open IntSyn in
        let trExp =
          function
          | Uni (L) -> Uni L
          | Pi ((D, P), V) -> Pi (((trDec D), P), (trExp V))
          | Root (H, S) -> Root ((trHead H), (trSpine S))
          | Lam (D, U) -> Lam ((trDec D), (trExp U))
          | FgnExp csfe as U -> FgnExpStd.Map.apply csfe trExp
        and trDec (Dec (name, V)) = Dec (name, (trExp V))
        and trSpine =
          function | Nil -> Nil | App (U, S) -> App ((trExp U), (trSpine S))
        and trHead =
          function
          | BVar n -> BVar n
          | Const cid -> trConst cid
          | Skonst cid -> trConst cid
          | Def cid -> trConst cid
          | NSDef cid -> trConst cid
          | FgnConst (csid, condec) ->
              FgnConst (csid, (mapConDecConsts f condec))
        and trConst cid =
          let cid' = f cid in
          match IntSyn.sgnLookup cid' with
          | ConDec _ -> Const cid'
          | SkoDec _ -> Skonst cid'
          | ConDef _ -> Def cid'
          | AbbrevDef _ -> NSDef cid' in
        Whnf.normalize ((trExp U), IntSyn.id)
    let rec mapConDecConsts arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, ConDec (name, parent, i, status, V, L)) ->
          IntSyn.ConDec (name, parent, i, status, (mapExpConsts f V), L)
      | (f, ConDef (name, parent, i, U, V, L, Anc)) ->
          IntSyn.ConDef
            (name, parent, i, (mapExpConsts f U), (mapExpConsts f V), L, Anc)
      | (((f)(* reconstruct Anc?? -fp *)), AbbrevDef
         (name, parent, i, U, V, L)) ->
          IntSyn.AbbrevDef
            (name, parent, i, (mapExpConsts f U), (mapExpConsts f V), L)
      | (f, SkoDec (name, parent, i, V, L)) ->
          IntSyn.SkoDec (name, parent, i, (mapExpConsts f V), L)
    let rec mapStrDecParent f (StrDec (name, parent)) =
      IntSyn.StrDec (name, (f parent))
    let rec mapConDecParent arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, ConDec (name, parent, i, status, V, L)) ->
          IntSyn.ConDec (name, (f parent), i, status, V, L)
      | (f, ConDef (name, parent, i, U, V, L, Anc)) ->
          IntSyn.ConDef (name, (f parent), i, U, V, L, Anc)
      | (((f)(* reconstruct Anc?? -fp *)), AbbrevDef
         (name, parent, i, U, V, L)) ->
          IntSyn.AbbrevDef (name, (f parent), i, U, V, L)
      | (f, SkoDec (name, parent, i, V, L)) ->
          IntSyn.SkoDec (name, (f parent), i, V, L)
    let rec strictify =
      function
      | AbbrevDef (name, parent, i, U, V, IntSyn.Type) as condec ->
          (try
             Strict.check ((U, V), NONE);
             IntSyn.ConDef
               (name, parent, i, U, V, IntSyn.Type, (IntSyn.ancestor U))
           with | Error _ -> condec)
      | AbbrevDef _ as condec -> condec
    let rec abbrevify (cid, condec) =
      match condec with
      | ConDec (name, parent, i, _, V, L) ->
          let U = Whnf.normalize ((I.Root ((I.Const cid), I.Nil)), I.id) in
          I.AbbrevDef (name, parent, i, U, V, L)
      | SkoDec (name, parent, i, V, L) ->
          let U = Whnf.normalize ((I.Root ((I.Skonst cid), I.Nil)), I.id) in
          I.AbbrevDef (name, parent, i, U, V, L)
      | ConDef (name, parent, i, U, V, L, Anc) ->
          I.AbbrevDef (name, parent, i, U, V, L)
      | AbbrevDef data -> I.AbbrevDef data
    let rec installModule
      ((((structTable)(* In order to install a module, we walk through the mids in preorder,
     assigning global mids and building up a translation map from local
     mids to global mids.  Then we walk through the cids in dependency
     order, assigning global cids, building up a translation map from
     local to global cids, and replacing the cids contained in the terms
     with their global equivalents.

     NOTE that a module might not be closed with respect to the local
     cids; that is, it might refer to global cids not defined by the
     module.  It is a global invariant that such cids will still be in
     scope whenever a module that refers to them is installed. *)),
        constTable, namespace),
       topOpt, nsOpt, installAction, transformConDec)
      =
      let (structMap : IntSyn.mid IntTree.__Table) = IntTree.new__ 0 in
      let (constMap : IntSyn.cid IntTree.__Table) = IntTree.new__ 0 in
      let mapStruct mid = valOf (IntTree.lookup structMap mid) in
      let mapParent =
        function | NONE -> topOpt | SOME parent -> SOME (mapStruct parent) in
      let mapConst cid =
        match IntTree.lookup constMap cid with
        | NONE -> cid
        | SOME cid' -> cid' in
      let doStruct (mid, StructInfo strdec) =
        let strdec' = mapStrDecParent mapParent strdec in
        let mid' = IntSyn.sgnStructAdd strdec' in
        let parent = IntSyn.strDecParent strdec' in
        let nsOpt =
          match parent with
          | NONE -> nsOpt
          | SOME mid -> SOME (Names.getComponents mid) in
        let _ =
          match nsOpt with
          | SOME ns -> Names.insertStruct (ns, mid')
          | _ -> () in
        let _ =
          match parent with | NONE -> Names.installStructName mid' | _ -> () in
        let ns = Names.newNamespace () in
        let _ = Names.installComponents (mid', ns) in
        IntTree.insert structMap (mid, mid') in
      let doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin)) =
        let condec1 = mapConDecParent mapParent condec in
        let condec2 = mapConDecConsts mapConst condec1 in
        let condec3 = transformConDec (cid, condec2) in
        let cid' = IntSyn.sgnAdd condec3 in
        let parent = IntSyn.conDecParent condec3 in
        let nsOpt =
          match parent with
          | NONE -> nsOpt
          | SOME mid -> SOME (Names.getComponents mid) in
        let _ =
          match nsOpt with
          | SOME ns -> Names.insertConst (ns, cid')
          | _ -> () in
        let _ =
          match parent with | NONE -> Names.installConstName cid' | _ -> () in
        let _ = installAction (cid', origin) in
        let _ =
          match fixity with
          | Names.Fixity.Nonfix -> ()
          | _ -> Names.installFixity (cid', fixity) in
        let _ =
          match namePrefOpt with
          | NONE -> ()
          | SOME (n1, n2) -> Names.installNamePref (cid', (n1, n2)) in
        IntTree.insert constMap (cid, cid') in
      IntTree.app doStruct structTable; IntTree.app doConst constTable
    let decToDef = strictify o abbrevify
    let rec installStruct (strdec, module__, nsOpt, installAction, isDef) =
      let transformConDec =
        if isDef then decToDef else (function | (_, condec) -> condec) in
      let mid = IntSyn.sgnStructAdd strdec in
      let _ =
        match nsOpt with
        | SOME namespace -> Names.insertStruct (namespace, mid)
        | _ -> () in
      let _ = Names.installStructName mid in
      let ns = Names.newNamespace () in
      let _ = Names.installComponents (mid, ns) in
      installModule
        (module__, (SOME mid), NONE, installAction, transformConDec)
    let rec installSig (module__, nsOpt, installAction, isDef) =
      let transformConDec =
        if isDef then decToDef else (function | (_, condec) -> condec) in
      installModule (module__, NONE, nsOpt, installAction, transformConDec)
    let rec abstractModule (namespace, topOpt) =
      let (structTable : __StructInfo IntTree.__Table) = IntTree.new__ 0 in
      let (constTable : __ConstInfo IntTree.__Table) = IntTree.new__ 0 in
      let mapParent =
        match topOpt with
        | NONE -> (function | parent -> parent)
        | SOME mid ->
            (function | SOME mid' -> if mid = mid' then NONE else SOME mid') in
      let doStruct (_, mid) =
        let strdec = IntSyn.sgnStructLookup mid in
        let strdec' = mapStrDecParent mapParent strdec in
        let ns = Names.getComponents mid in
        IntTree.insert structTable (mid, (StructInfo strdec')); doNS ns
      and doConst (_, cid) =
        let condec = IntSyn.sgnLookup cid in
        let condec' = mapConDecParent mapParent condec in
        let fixity = Names.getFixity cid in
        let namePref = Names.getNamePref cid in
        let origin = Origins.originLookup cid in
        IntTree.insert constTable
          (cid, (ConstInfo (condec', fixity, namePref, origin)))
      and doNS ns = Names.appStructs doStruct ns; Names.appConsts doConst ns in
      doNS namespace; (structTable, constTable, namespace)
    let rec instantiateModule (((_, _, namespace) as module__), transform) =
      let transformConDec = transform namespace in
      let mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", NONE)) in
      let ns = Names.newNamespace () in
      let _ = Names.installComponents (mid, ns) in
      let _ =
        installModule
          (module__, (SOME mid), NONE, (function | _ -> ()), transformConDec) in
      abstractModule (ns, (SOME mid))
    let (defList : string list ref) = ref nil
    let (defCount : int ref) = ref 0
    let (defs : module__ HashTable.__Table) = HashTable.new__ 4096
    let rec defsClear () = HashTable.clear defs
    let defsInsert = HashTable.insertShadow defs
    let defsLookup = HashTable.lookup defs
    let defsDelete = HashTable.delete defs
    let rec reset () = defList := nil; defCount := 0; defsClear ()
    let rec resetFrom mark =
      let ct (l, i) =
        if i <= mark
        then l
        else (let h::t = l in defsDelete h; ct (t, (i - 1))) in
      (:=) defList ct ((!defList), (!defCount)); defCount := mark
    let rec sigDefSize () = !defCount
    let rec installSigDef (id, module__) =
      match defsInsert (id, module__) with
      | NONE ->
          ((defList := id) :: (!defList); ((!) ((:=) defCount) defCount) + 1)
      | SOME entry ->
          (raise
             (Error
                (("Shadowing: A signature named " ^ id) ^
                   "\nhas already been declared"));
           defsInsert entry;
           ())
    let lookupSigDef = defsLookup
  end ;;
