module type MODSYN  =
  sig
    module Names : NAMES
    exception Error of string 
    val abbrevify : (IntSyn.cid * IntSyn.conDec_) -> IntSyn.conDec_
    val strictify : IntSyn.conDec_ -> IntSyn.conDec_
    type nonrec module_
    val installStruct :
      (((IntSyn.strDec_ * module_ * Names.namespace option *
          ((IntSyn.cid * (string * Paths.occConDec option)) -> unit) * bool))
        (* action *)) -> unit
    val installSig :
      (((module_ * Names.namespace option *
          ((IntSyn.cid * (string * Paths.occConDec option)) -> unit) * bool))
        (* action *)) -> unit
    val instantiateModule :
      (((module_ *
          (Names.namespace -> (IntSyn.cid * IntSyn.conDec_) -> IntSyn.conDec_))
          -> module_)(* Names.namespace -> transform *))
    val abstractModule : (Names.namespace * IntSyn.mid option) -> module_
    val reset : unit -> unit
    val installSigDef : (string * module_) -> unit
    val lookupSigDef : string -> module_ option
    val sigDefSize : unit -> int
    val resetFrom : int -> unit
  end


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
    type constInfo_ =
      | ConstInfo of (IntSyn.conDec_ * Names.Fixity.fixity * (string list *
      string list) option * (string * Paths.occConDec option)) 
    type structInfo_ =
      | StructInfo of IntSyn.strDec_ 
    type nonrec module_ =
      (structInfo_ IntTree.table_ * constInfo_ IntTree.table_ *
        Names.namespace)
    type nonrec action =
      (IntSyn.cid * (string * Paths.occConDec option)) -> unit
    type nonrec transform = (IntSyn.cid * IntSyn.conDec_) -> IntSyn.conDec_
    let rec mapExpConsts f (u_) =
      let open IntSyn in
        let rec trExp =
          begin function
          | Uni (l_) -> Uni l_
          | Pi ((d_, p_), v_) -> Pi (((trDec d_), p_), (trExp v_))
          | Root (h_, s_) -> Root ((trHead h_), (trSpine s_))
          | Lam (d_, u_) -> Lam ((trDec d_), (trExp u_))
          | FgnExp csfe as u_ -> FgnExpStd.Map.apply csfe trExp end
          and trDec (Dec (name, v_)) = Dec (name, (trExp v_))
          and trSpine =
            begin function
            | Nil -> Nil
            | App (u_, s_) -> App ((trExp u_), (trSpine s_)) end
        and trHead =
          begin function
          | BVar n -> BVar n
          | Const cid -> trConst cid
          | Skonst cid -> trConst cid
          | Def cid -> trConst cid
          | NSDef cid -> trConst cid
          | FgnConst (csid, condec) ->
              FgnConst (csid, (mapConDecConsts f condec)) end
      and trConst cid =
        let cid' = f cid in
        begin match IntSyn.sgnLookup cid' with
        | ConDec _ -> Const cid'
        | SkoDec _ -> Skonst cid'
        | ConDef _ -> Def cid'
        | AbbrevDef _ -> NSDef cid' end in
  Whnf.normalize ((trExp u_), IntSyn.id)
let rec mapConDecConsts arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, ConDec (name, parent, i, status, v_, l_)) ->
      IntSyn.ConDec (name, parent, i, status, (mapExpConsts f v_), l_)
  | (f, ConDef (name, parent, i, u_, v_, l_, Anc)) ->
      IntSyn.ConDef
        (name, parent, i, (mapExpConsts f u_), (mapExpConsts f v_), l_, Anc)
  | (f, AbbrevDef (name, parent, i, u_, v_, l_)) ->
      IntSyn.AbbrevDef
        (name, parent, i, (mapExpConsts f u_), (mapExpConsts f v_), l_)
  | (f, SkoDec (name, parent, i, v_, l_)) ->
      IntSyn.SkoDec (name, parent, i, (mapExpConsts f v_), l_) end(* reconstruct Anc?? -fp *)
let rec mapStrDecParent f (StrDec (name, parent)) =
  IntSyn.StrDec (name, (f parent))
let rec mapConDecParent arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (f, ConDec (name, parent, i, status, v_, l_)) ->
      IntSyn.ConDec (name, (f parent), i, status, v_, l_)
  | (f, ConDef (name, parent, i, u_, v_, l_, Anc)) ->
      IntSyn.ConDef (name, (f parent), i, u_, v_, l_, Anc)
  | (f, AbbrevDef (name, parent, i, u_, v_, l_)) ->
      IntSyn.AbbrevDef (name, (f parent), i, u_, v_, l_)
  | (f, SkoDec (name, parent, i, v_, l_)) ->
      IntSyn.SkoDec (name, (f parent), i, v_, l_) end(* reconstruct Anc?? -fp *)
let rec strictify =
  begin function
  | AbbrevDef (name, parent, i, u_, v_, IntSyn.Type) as condec ->
      (begin try
               begin Strict.check ((u_, v_), None);
               IntSyn.ConDef
                 (name, parent, i, u_, v_, IntSyn.Type, (IntSyn.ancestor u_)) end
      with | Error _ -> condec end)
  | AbbrevDef _ as condec -> condec end
let rec abbrevify (cid, condec) =
  begin match condec with
  | ConDec (name, parent, i, _, v_, l_) ->
      let u_ = Whnf.normalize ((I.Root ((I.Const cid), I.Nil)), I.id) in
      I.AbbrevDef (name, parent, i, u_, v_, l_)
  | SkoDec (name, parent, i, v_, l_) ->
      let u_ = Whnf.normalize ((I.Root ((I.Skonst cid), I.Nil)), I.id) in
      I.AbbrevDef (name, parent, i, u_, v_, l_)
  | ConDef (name, parent, i, u_, v_, l_, Anc) ->
      I.AbbrevDef (name, parent, i, u_, v_, l_)
  | AbbrevDef data -> I.AbbrevDef data end
let rec installModule
  ((structTable, constTable, namespace), topOpt, nsOpt, installAction,
   transformConDec)
  =
  let (structMap : IntSyn.mid IntTree.table_) = IntTree.new_ 0 in
  let (constMap : IntSyn.cid IntTree.table_) = IntTree.new_ 0 in
  let rec mapStruct mid = valOf (IntTree.lookup structMap mid) in
  let rec mapParent =
    begin function | None -> topOpt | Some parent -> Some (mapStruct parent) end in
  let rec mapConst cid =
    begin match IntTree.lookup constMap cid with
    | None -> cid
    | Some cid' -> cid' end in
  let rec doStruct (mid, StructInfo strdec) =
    let strdec' = mapStrDecParent mapParent strdec in
    let mid' = IntSyn.sgnStructAdd strdec' in
    let parent = IntSyn.strDecParent strdec' in
    let nsOpt =
      begin match parent with
      | None -> nsOpt
      | Some mid -> Some (Names.getComponents mid) end in
    let _ =
      begin match nsOpt with
      | Some ns -> Names.insertStruct (ns, mid')
      | _ -> () end in
    let _ =
      begin match parent with
      | None -> Names.installStructName mid'
      | _ -> () end in
    let ns = Names.newNamespace () in
    let _ = Names.installComponents (mid', ns) in
    IntTree.insert structMap (mid, mid') in
  let rec doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin)) =
    let condec1 = mapConDecParent mapParent condec in
    let condec2 = mapConDecConsts mapConst condec1 in
    let condec3 = transformConDec (cid, condec2) in
    let cid' = IntSyn.sgnAdd condec3 in
    let parent = IntSyn.conDecParent condec3 in
    let nsOpt =
      begin match parent with
      | None -> nsOpt
      | Some mid -> Some (Names.getComponents mid) end in
    let _ =
      begin match nsOpt with
      | Some ns -> Names.insertConst (ns, cid')
      | _ -> () end in
    let _ =
      begin match parent with | None -> Names.installConstName cid' | _ -> () end in
    let _ = installAction (cid', origin) in
    let _ =
      begin match fixity with
      | Names.Fixity.Nonfix -> ()
      | _ -> Names.installFixity (cid', fixity) end in
    let _ =
      begin match namePrefOpt with
      | None -> ()
      | Some (n1, n2) -> Names.installNamePref (cid', (n1, n2)) end in
    IntTree.insert constMap (cid, cid') in
begin IntTree.app doStruct structTable; IntTree.app doConst constTable end
let decToDef = strictify o abbrevify
let rec installStruct (strdec, module_, nsOpt, installAction, isDef) =
  let transformConDec = if isDef then begin decToDef end
    else begin (begin function | (_, condec) -> condec end) end in
let mid = IntSyn.sgnStructAdd strdec in
let _ =
begin match nsOpt with
| Some namespace -> Names.insertStruct (namespace, mid)
| _ -> () end in
let _ = Names.installStructName mid in
let ns = Names.newNamespace () in
let _ = Names.installComponents (mid, ns) in
installModule (module_, (Some mid), None, installAction, transformConDec)
let rec installSig (module_, nsOpt, installAction, isDef) =
  let transformConDec = if isDef then begin decToDef end
    else begin (begin function | (_, condec) -> condec end) end in
installModule (module_, None, nsOpt, installAction, transformConDec)
let rec abstractModule (namespace, topOpt) =
  let (structTable : structInfo_ IntTree.table_) = IntTree.new_ 0 in
  let (constTable : constInfo_ IntTree.table_) = IntTree.new_ 0 in
  let mapParent =
    begin match topOpt with | None -> (begin function | parent -> parent end)
    | Some mid ->
        (begin function
         | Some mid' -> if mid = mid' then begin None end
             else begin Some mid' end end) end in
let rec doStruct (_, mid) =
let strdec = IntSyn.sgnStructLookup mid in
let strdec' = mapStrDecParent mapParent strdec in
let ns = Names.getComponents mid in
begin IntTree.insert structTable (mid, (StructInfo strdec')); doNS ns end
and doConst (_, cid) =
  let condec = IntSyn.sgnLookup cid in
  let condec' = mapConDecParent mapParent condec in
  let fixity = Names.getFixity cid in
  let namePref = Names.getNamePref cid in
  let origin = Origins.originLookup cid in
  IntTree.insert constTable
    (cid, (ConstInfo (condec', fixity, namePref, origin)))
and doNS ns =
  begin Names.appStructs doStruct ns; Names.appConsts doConst ns end in
begin doNS namespace; (structTable, constTable, namespace) end
let rec instantiateModule (((_, _, namespace) as module_), transform) =
  let transformConDec = transform namespace in
  let mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", None)) in
  let ns = Names.newNamespace () in
  let _ = Names.installComponents (mid, ns) in
  let _ =
    installModule (module_, (Some mid), None, (begin function | _ -> () end),
      transformConDec) in
  abstractModule (ns, (Some mid))
let (defList : string list ref) = ref []
let (defCount : int ref) = ref 0
let (defs : module_ HashTable.table_) = HashTable.new_ 4096
let rec defsClear () = HashTable.clear defs
let defsInsert = HashTable.insertShadow defs
let defsLookup = HashTable.lookup defs
let defsDelete = HashTable.delete defs
let rec reset () = begin defList := []; defCount := 0; defsClear () end
let rec resetFrom mark =
  let rec ct (l, i) = if i <= mark then begin l end
    else begin (let h::t = l in begin defsDelete h; ct (t, (i - 1)) end) end in
begin (:=) defList ct (!defList, !defCount); defCount := mark end
let rec sigDefSize () = !defCount
let rec installSigDef (id, module_) =
  begin match defsInsert (id, module_) with
  | None ->
      (begin (defList := id) :: !defList; ((!) ((:=) defCount) defCount) + 1 end)
  | Some entry ->
      (begin raise
               (Error
                  (("Shadowing: A signature named " ^ id) ^
                     "\nhas already been declared"));
       defsInsert entry;
       () end) end
let lookupSigDef = defsLookup end
