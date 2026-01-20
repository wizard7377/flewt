
module type MODSYN  =
  sig
    module Names : NAMES
    exception Error of string 
    val abbrevify : IntSyn.cid -> IntSyn.__ConDec -> IntSyn.__ConDec
    val strictify : IntSyn.__ConDec -> IntSyn.__ConDec
    type nonrec module__
    val installStruct :
      ((IntSyn.__StrDec ->
          module__ ->
            Names.namespace option ->
              (IntSyn.cid -> (string * Paths.occConDec option) -> unit) ->
                bool -> unit)(* action *))
    val installSig :
      ((module__ ->
          Names.namespace option ->
            (IntSyn.cid -> (string * Paths.occConDec option) -> unit) ->
              bool -> unit)(* action *))
    val instantiateModule :
      ((module__ ->
          (Names.namespace ->
             IntSyn.cid -> IntSyn.__ConDec -> IntSyn.__ConDec)
            -> module__)(* Names.namespace -> transform *))
    val abstractModule : Names.namespace -> IntSyn.mid option -> module__
    val reset : unit -> unit
    val installSigDef : string -> module__ -> unit
    val lookupSigDef : string -> module__ option
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
                       module HashTable : TABLE
                     end) : MODSYN =
  struct
    module Names = Names'
    module I = IntSyn
    exception Error of string 
    type __ConstInfo =
      | ConstInfo of (IntSyn.__ConDec * Names.Fixity.fixity * (string list *
      string list) option * (string * Paths.occConDec option)) 
    type __StructInfo =
      | StructInfo of IntSyn.__StrDec 
    type nonrec module__ =
      (__StructInfo IntTree.__Table * __ConstInfo IntTree.__Table *
        Names.namespace)
    type nonrec action =
      IntSyn.cid -> (string * Paths.occConDec option) -> unit
    type nonrec transform = IntSyn.cid -> IntSyn.__ConDec -> IntSyn.__ConDec
    let rec mapExpConsts f (__U) =
      let open IntSyn in
        let rec trExp =
          function
          | Uni (__L) -> Uni __L
          | Pi ((__D, __P), __V) -> Pi (((trDec __D), __P), (trExp __V))
          | Root (__H, __S) -> Root ((trHead __H), (trSpine __S))
          | Lam (__D, __U) -> Lam ((trDec __D), (trExp __U))
          | FgnExp csfe as U -> FgnExpStd.Map.apply csfe trExp
        and trDec (Dec (name, __V)) = Dec (name, (trExp __V))
        and trSpine =
          function
          | Nil -> Nil
          | App (__U, __S) -> App ((trExp __U), (trSpine __S))
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
        Whnf.normalize ((trExp __U), IntSyn.id)
    let rec mapConDecConsts __0__ __1__ =
      match (__0__, __1__) with
      | (f, ConDec (name, parent, i, status, __V, __L)) ->
          IntSyn.ConDec (name, parent, i, status, (mapExpConsts f __V), __L)
      | (f, ConDef (name, parent, i, __U, __V, __L, Anc)) ->
          IntSyn.ConDef
            (name, parent, i, (mapExpConsts f __U), (mapExpConsts f __V),
              __L, Anc)
      | (f, AbbrevDef (name, parent, i, __U, __V, __L)) ->
          IntSyn.AbbrevDef
            (name, parent, i, (mapExpConsts f __U), (mapExpConsts f __V),
              __L)
      | (f, SkoDec (name, parent, i, __V, __L)) ->
          IntSyn.SkoDec (name, parent, i, (mapExpConsts f __V), __L)(* reconstruct Anc?? -fp *)
    let rec mapStrDecParent f (StrDec (name, parent)) =
      IntSyn.StrDec (name, (f parent))
    let rec mapConDecParent __2__ __3__ =
      match (__2__, __3__) with
      | (f, ConDec (name, parent, i, status, __V, __L)) ->
          IntSyn.ConDec (name, (f parent), i, status, __V, __L)
      | (f, ConDef (name, parent, i, __U, __V, __L, Anc)) ->
          IntSyn.ConDef (name, (f parent), i, __U, __V, __L, Anc)
      | (f, AbbrevDef (name, parent, i, __U, __V, __L)) ->
          IntSyn.AbbrevDef (name, (f parent), i, __U, __V, __L)
      | (f, SkoDec (name, parent, i, __V, __L)) ->
          IntSyn.SkoDec (name, (f parent), i, __V, __L)(* reconstruct Anc?? -fp *)
    let rec strictify =
      function
      | AbbrevDef (name, parent, i, __U, __V, IntSyn.Type) as condec ->
          (try
             Strict.check ((__U, __V), None);
             IntSyn.ConDef
               (name, parent, i, __U, __V, IntSyn.Type,
                 (IntSyn.ancestor __U))
           with | Error _ -> condec)
      | AbbrevDef _ as condec -> condec
    let rec abbrevify cid condec =
      match condec with
      | ConDec (name, parent, i, _, __V, __L) ->
          let __U = Whnf.normalize ((I.Root ((I.Const cid), I.Nil)), I.id) in
          I.AbbrevDef (name, parent, i, __U, __V, __L)
      | SkoDec (name, parent, i, __V, __L) ->
          let __U = Whnf.normalize ((I.Root ((I.Skonst cid), I.Nil)), I.id) in
          I.AbbrevDef (name, parent, i, __U, __V, __L)
      | ConDef (name, parent, i, __U, __V, __L, Anc) ->
          I.AbbrevDef (name, parent, i, __U, __V, __L)
      | AbbrevDef data -> I.AbbrevDef data
    let rec installModule (structTable, constTable, namespace) topOpt nsOpt
      installAction transformConDec =
      let (structMap : IntSyn.mid IntTree.__Table) = IntTree.new__ 0 in
      let (constMap : IntSyn.cid IntTree.__Table) = IntTree.new__ 0 in
      let rec mapStruct mid = valOf (IntTree.lookup structMap mid) in
      let rec mapParent =
        function | None -> topOpt | Some parent -> Some (mapStruct parent) in
      let rec mapConst cid =
        match IntTree.lookup constMap cid with
        | None -> cid
        | Some cid' -> cid' in
      let rec doStruct mid (StructInfo strdec) =
        let strdec' = mapStrDecParent mapParent strdec in
        let mid' = IntSyn.sgnStructAdd strdec' in
        let parent = IntSyn.strDecParent strdec' in
        let nsOpt =
          match parent with
          | None -> nsOpt
          | Some mid -> Some (Names.getComponents mid) in
        let _ =
          match nsOpt with
          | Some ns -> Names.insertStruct (ns, mid')
          | _ -> () in
        let _ =
          match parent with | None -> Names.installStructName mid' | _ -> () in
        let ns = Names.newNamespace () in
        let _ = Names.installComponents (mid', ns) in
        IntTree.insert structMap (mid, mid') in
      let rec doConst cid (ConstInfo (condec, fixity, namePrefOpt, origin)) =
        let condec1 = mapConDecParent mapParent condec in
        let condec2 = mapConDecConsts mapConst condec1 in
        let condec3 = transformConDec (cid, condec2) in
        let cid' = IntSyn.sgnAdd condec3 in
        let parent = IntSyn.conDecParent condec3 in
        let nsOpt =
          match parent with
          | None -> nsOpt
          | Some mid -> Some (Names.getComponents mid) in
        let _ =
          match nsOpt with
          | Some ns -> Names.insertConst (ns, cid')
          | _ -> () in
        let _ =
          match parent with | None -> Names.installConstName cid' | _ -> () in
        let _ = installAction (cid', origin) in
        let _ =
          match fixity with
          | Names.Fixity.Nonfix -> ()
          | _ -> Names.installFixity (cid', fixity) in
        let _ =
          match namePrefOpt with
          | None -> ()
          | Some (n1, n2) -> Names.installNamePref (cid', (n1, n2)) in
        IntTree.insert constMap (cid, cid') in
      IntTree.app doStruct structTable; IntTree.app doConst constTable
    let decToDef = strictify o abbrevify
    let rec installStruct strdec module__ nsOpt installAction isDef =
      let transformConDec =
        if isDef then decToDef else (fun _ -> fun condec -> condec) in
      let mid = IntSyn.sgnStructAdd strdec in
      let _ =
        match nsOpt with
        | Some namespace -> Names.insertStruct (namespace, mid)
        | _ -> () in
      let _ = Names.installStructName mid in
      let ns = Names.newNamespace () in
      let _ = Names.installComponents (mid, ns) in
      installModule
        (module__, (Some mid), None, installAction, transformConDec)
    let rec installSig module__ nsOpt installAction isDef =
      let transformConDec =
        if isDef then decToDef else (fun _ -> fun condec -> condec) in
      installModule (module__, None, nsOpt, installAction, transformConDec)
    let rec abstractModule namespace topOpt =
      let (structTable : __StructInfo IntTree.__Table) = IntTree.new__ 0 in
      let (constTable : __ConstInfo IntTree.__Table) = IntTree.new__ 0 in
      let mapParent =
        match topOpt with
        | None -> (fun parent -> parent)
        | Some mid ->
            (fun (Some mid') -> if mid = mid' then None else Some mid') in
      let rec doStruct _ mid =
        let strdec = IntSyn.sgnStructLookup mid in
        let strdec' = mapStrDecParent mapParent strdec in
        let ns = Names.getComponents mid in
        IntTree.insert structTable (mid, (StructInfo strdec')); doNS ns
      and doConst _ cid =
        let condec = IntSyn.sgnLookup cid in
        let condec' = mapConDecParent mapParent condec in
        let fixity = Names.getFixity cid in
        let namePref = Names.getNamePref cid in
        let origin = Origins.originLookup cid in
        IntTree.insert constTable
          (cid, (ConstInfo (condec', fixity, namePref, origin)))
      and doNS ns = Names.appStructs doStruct ns; Names.appConsts doConst ns in
      doNS namespace; (structTable, constTable, namespace)
    let rec instantiateModule ((_, _, namespace) as module__) transform =
      let transformConDec = transform namespace in
      let mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", None)) in
      let ns = Names.newNamespace () in
      let _ = Names.installComponents (mid, ns) in
      let _ =
        installModule
          (module__, (Some mid), None, (fun _ -> ()), transformConDec) in
      abstractModule (ns, (Some mid))
    let (defList : string list ref) = ref nil
    let (defCount : int ref) = ref 0
    let (defs : module__ HashTable.__Table) = HashTable.new__ 4096
    let rec defsClear () = HashTable.clear defs
    let defsInsert = HashTable.insertShadow defs
    let defsLookup = HashTable.lookup defs
    let defsDelete = HashTable.delete defs
    let rec reset () = defList := nil; defCount := 0; defsClear ()
    let rec resetFrom mark =
      let rec ct l i =
        if i <= mark
        then l
        else (let h::t = l in defsDelete h; ct (t, (i - 1))) in
      (:=) defList ct ((!defList), (!defCount)); defCount := mark
    let rec sigDefSize () = !defCount
    let rec installSigDef id module__ =
      match defsInsert (id, module__) with
      | None ->
          ((defList := id) :: (!defList); ((!) ((:=) defCount) defCount) + 1)
      | Some entry ->
          (raise
             (Error
                (("Shadowing: A signature named " ^ id) ^
                   "\nhas already been declared"));
           defsInsert entry;
           ())
    let lookupSigDef = defsLookup
  end ;;
