module type SUBORDINATE  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val install : IntSyn.cid -> unit
    val installDef : IntSyn.cid -> unit
    val installBlock : IntSyn.cid -> unit
    val freeze : IntSyn.cid list -> IntSyn.cid list
    val thaw : IntSyn.cid list -> IntSyn.cid list
    val frozen : IntSyn.cid list -> bool
    val addSubord : (IntSyn.cid * IntSyn.cid) -> unit
    val below : (IntSyn.cid * IntSyn.cid) -> bool
    val belowEq : (IntSyn.cid * IntSyn.cid) -> bool
    val equiv : (IntSyn.cid * IntSyn.cid) -> bool
    val respects : (IntSyn.dctx * IntSyn.eclo) -> unit
    val respectsN : (IntSyn.dctx * IntSyn.exp_) -> unit
    val checkNoDef : IntSyn.cid -> unit
    val weaken : (IntSyn.dctx * IntSyn.cid) -> IntSyn.sub_
    val show : unit -> unit
    val showDef : unit -> unit
  end


module Subordinate(Subordinate:sig
                                 module Global : GLOBAL
                                 module Whnf : WHNF
                                 module Names : NAMES
                                 module Table : TABLE
                                 module MemoTable : TABLE
                                 module IntSet : INTSET
                               end) : SUBORDINATE =
  struct
    exception Error of string 
    module I = IntSyn
    let (soGraph : IntSet.intset Table.table_) = Table.new_ 32
    let insert = Table.insert soGraph
    let rec adjNodes a = valOf (Table.lookup soGraph a)
    let rec insertNewFam a = Table.insert soGraph (a, IntSet.empty)
    let updateFam = Table.insert soGraph
    let (memoTable : (bool * int) MemoTable.table_) = MemoTable.new_ 2048
    let memoInsert = MemoTable.insert memoTable
    let memoLookup = MemoTable.lookup memoTable
    let memoClear = begin function | () -> MemoTable.clear memoTable end
    let memoCounter = ref 0
    let rec appReachable f b =
      let rec rch (b, visited) =
        if IntSet.member (b, visited) then begin visited end
        else begin
          (begin f b;
           IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b) end) end in
  begin rch (b, IntSet.empty); () end
exception Reachable 
let rec reach (b, a, visited) =
  let rec rch (b, visited) =
    if IntSet.member (b, visited) then begin visited end
    else begin
      (let adj = adjNodes b in
       if IntSet.member (a, adj) then begin raise Reachable end
         else begin IntSet.foldl rch (IntSet.insert (b, visited)) adj end) end in
rch (b, visited)
let rec reachable (b, a) = reach (b, a, IntSet.empty)
let rec addNewEdge (b, a) =
  begin ((!) ((:=) memoCounter) memoCounter) + 1;
  memoInsert ((b, a), (true, !memoCounter));
  updateFam (b, (IntSet.insert (a, (adjNodes b)))) end
let (fTable : bool Table.table_) = Table.new_ 32
let fLookup = Table.lookup fTable
let fInsert = Table.insert fTable
let rec fGet a =
  begin match fLookup a with | Some frozen -> frozen | None -> false end
let rec fSet (a, frozen) =
  let _ =
    Global.chPrint 5
      (begin function
       | () ->
           ((^) (if frozen then begin "Freezing " end
              else begin "Thawing " end)
           Names.qidToString (Names.constQid a))
       ^
       "\n" end) in
fInsert (a, frozen)
let rec checkFreeze (c, a) =
  if fGet a
  then
    begin raise
            (Error
               ((^) (((^) "Freezing violation: constant " Names.qidToString
                        (Names.constQid c))
                       ^ "\nextends type family ")
                  Names.qidToString (Names.constQid a))) end
  else begin () end
let rec expandFamilyAbbrevs a =
  begin match I.constUni a with
  | I.Type ->
      raise
        (Error
           (((^) "Constant " Names.qidToString (Names.constQid a)) ^
              " must be a type family to be frozen or thawed"))
  | I.Kind ->
      (begin match IntSyn.sgnLookup a with
       | ConDec _ -> a
       | ConDef _ -> IntSyn.targetFam (IntSyn.constDef a)
       | SkoDec _ -> a
       | AbbrevDef _ -> IntSyn.targetFam (IntSyn.constDef a) end) end
let (freezeList : IntSet.intset ref) = ref IntSet.empty
let rec freeze (l_) =
  let _ = freezeList := IntSet.empty in
  let l'_ = map expandFamilyAbbrevs l_ in
  let _ =
    List.app
      (begin function
       | a ->
           appReachable
             (begin function
              | b ->
                  (begin fSet (b, true);
                   (:=) freezeList IntSet.insert (b, !freezeList) end) end)
       a end)
    l'_ in
let cids = IntSet.foldl (::) [] !freezeList in cids
let rec frozen (l_) =
  let l'_ = map expandFamilyAbbrevs l_ in
  List.exists (begin function | a -> fGet a end) l'_
let rec computeBelow (a, b) =
  begin try
          begin reachable (b, a);
          memoInsert ((b, a), (false, !memoCounter));
          false end
  with
  | Reachable -> (begin memoInsert ((b, a), (true, !memoCounter)); true end) end
let rec below (a, b) =
  ((begin match memoLookup (b, a) with
    | None -> computeBelow (a, b)
    | Some (true, c) -> true
    | Some (false, c) -> if (!) ((=) c) memoCounter then begin false end
        else begin computeBelow (a, b) end end)
(* true entries remain valid *))
let rec belowEq (a, b) = (a = b) || (below (a, b))
let rec equiv (a, b) = (belowEq (a, b)) && (belowEq (b, a))
let rec addSubord (a, b) = if below (a, b) then begin () end
  else begin
    ((if fGet b
      then
        begin raise
                (Error
                   ((^) (((^) "Freezing violation: " Names.qidToString
                            (Names.constQid b))
                           ^ " would depend on ")
                      Names.qidToString (Names.constQid a))) end
    else begin addNewEdge (b, a) end)
  (* if b is frozen and not already b #> a *)(* subordination would change; signal error *)) end
let (aboveList : IntSyn.cid list ref) = ref []
let rec addIfBelowEq a's =
  begin function
  | b -> if List.exists (begin function | a -> belowEq (a, b) end) a's
      then begin (aboveList := b) :: !aboveList end
  else begin () end end
let rec thaw a's =
  let a's' = map expandFamilyAbbrevs a's in
  let _ = aboveList := [] in
  let _ = Table.app (begin function | (b, _) -> addIfBelowEq a's' b end)
    soGraph in
  let _ = List.app (begin function | b -> fSet (b, false) end) !aboveList in
  !aboveList
let (defGraph : IntSet.intset Table.table_) = Table.new_ 32
let rec occursInDef a =
  begin match Table.lookup defGraph a with | None -> false | Some _ -> true end
let rec insertNewDef (b, a) =
  begin match Table.lookup defGraph a with
  | None -> Table.insert defGraph (a, (IntSet.insert (b, IntSet.empty)))
  | Some bs -> Table.insert defGraph (a, (IntSet.insert (b, bs))) end
let rec installConDec =
  begin function
  | (b, ConDef (_, _, _, a_, k_, I.Kind, _)) ->
      insertNewDef (b, (I.targetFam a_))
  | _ -> () end(* I.targetFam must be defined, but expands definitions! *)
let rec installDef c = installConDec (c, (I.sgnLookup c))
let rec checkNoDef a =
  if occursInDef a
  then
    begin raise
            (Error
               (((^) "Definition violation: family " Names.qidToString
                   (Names.constQid a))
                  ^ "\noccurs as right-hand side of type-level definition")) end
  else begin
    appReachable
      (begin function
       | a' ->
           if occursInDef a'
           then
             begin raise
                     (Error
                        (((^) (((^) "Definition violation: family "
                                  Names.qidToString (Names.constQid a))
                                 ^ " |> ")
                            Names.qidToString (Names.constQid a'))
                           ^
                           ",\nwhich occurs as right-hand side of a type-level definition")) end
           else begin () end end)
  a end
let rec reset () =
  begin Table.clear soGraph;
  Table.clear fTable;
  MemoTable.clear memoTable;
  Table.clear defGraph end
let rec installTypeN' =
  begin function
  | (Pi (((Dec (_, v1_) as d_), _), v2_), a) ->
      (begin addSubord ((I.targetFam v1_), a);
       installTypeN v1_;
       installTypeN' (v2_, a) end)
  | ((Root (Def _, _) as v_), a) ->
      let v'_ = Whnf.normalize (Whnf.expandDef (v_, I.id)) in
      installTypeN' (v'_, a)
  | (Root _, _) -> () end(* Sun Nov 10 11:15:47 2002 -fp *)
(* this looks like blatant overkill ... *)
let rec installTypeN (v_) = installTypeN' (v_, (I.targetFam v_))
let rec installKindN =
  begin function
  | (Uni (l_), a) -> ()
  | (Pi ((Dec (_, v1_), p_), v2_), a) ->
      (begin addSubord ((I.targetFam v1_), a);
       installTypeN v1_;
       installKindN (v2_, a) end) end
let rec install c =
  let v_ = I.constType c in
  begin match I.targetFamOpt v_ with
  | None -> (begin insertNewFam c; installKindN (v_, c) end)
    | Some a ->
        (((begin (((begin match IntSyn.sgnLookup c with
                    | ConDec _ -> checkFreeze (c, a)
                    | SkoDec _ -> checkFreeze (c, a)
                    | _ -> () end))
        (* FIX: skolem types should probably be created frozen -kw *));
        installTypeN' (v_, a) end))
  (* simplified  Tue Mar 27 20:58:31 2001 -fp *)) end
let rec installDec (Dec (_, v_)) = installTypeN v_
let rec installSome =
  begin function
  | I.Null -> ()
  | Decl (g_, d_) -> (begin installSome g_; installDec d_ end) end
let rec installBlock b =
  let BlockDec (_, _, g_, ds_) = I.sgnLookup b in
  begin installSome g_;
  List.app (begin function | d_ -> installDec d_ end)
  ds_ end
let rec checkBelow (a, b) =
  if not (below (a, b))
  then
    begin raise
            (Error
               ((^) (((^) "Subordination violation: " Names.qidToString
                        (Names.constQid a))
                       ^ " not <| ")
                  Names.qidToString (Names.constQid b))) end
  else begin () end
let rec respectsTypeN' =
  begin function
  | (Pi (((Dec (_, v1_) as d_), _), v2_), a) ->
      (begin checkBelow ((I.targetFam v1_), a);
       respectsTypeN v1_;
       respectsTypeN' (v2_, a) end)
  | ((Root (Def _, _) as v_), a) ->
      let v'_ = Whnf.normalize (Whnf.expandDef (v_, I.id)) in
      respectsTypeN' (v'_, a)
  | (Root _, _) -> () end(* Sun Nov 10 11:15:47 2002 -fp *)
(* this looks like blatant overkill ... *)
let rec respectsTypeN (v_) = respectsTypeN' (v_, (I.targetFam v_))
let rec respects (g_, (v_, s)) = respectsTypeN (Whnf.normalize (v_, s))
let rec respectsN (g_, v_) = respectsTypeN v_
let rec famsToString (bs, msg) =
  IntSet.foldl
    (begin function
     | (a, msg) -> ((Names.qidToString (Names.constQid a)) ^ " ") ^ msg end)
  "\n" bs
let rec showFam (a, bs) =
  print
    ((^) ((Names.qidToString (Names.constQid a)) ^
            (if fGet a then begin " #> " end else begin " |> " end))
  famsToString (bs, "\n"))
let rec show () = Table.app showFam soGraph
let rec weaken =
  begin function
  | (I.Null, a) -> I.id
  | (Decl (g'_, (Dec (name, v_) as d_)), a) ->
      let w' = weaken (g'_, a) in
      if belowEq ((I.targetFam v_), a) then begin I.dot1 w' end
        else begin I.comp (w', I.shift) end end
let declared = ref 0
let defined = ref 0
let abbrev = ref 0
let other = ref 0
let heightArray = Array.array (32, 0)
let maxHeight = ref 0
let rec inc r = ((!) ((:=) r) r) + 1
let rec incArray h =
  Array.update (heightArray, h, ((Array.sub (heightArray, h)) + 1))
let rec max h = (:=) maxHeight Int.max (h, !maxHeight)
let rec reset () =
  begin declared := 0;
  defined := 0;
  abbrev := 0;
  other := 0;
  Array.modify (begin function | i -> 0 end)
  heightArray; maxHeight := 0 end
let rec analyzeAnc =
  begin function
  | Anc (None, _, _) -> incArray 0
  | Anc (_, h, _) -> (begin incArray h; max h end) end
let rec analyze =
  begin function
  | ConDec (_, _, _, _, _, l_) -> inc declared
  | ConDef (_, _, _, _, _, l_, ancestors) ->
      (begin inc defined; analyzeAnc ancestors end)
  | AbbrevDef (_, _, _, _, _, l_) -> inc abbrev | _ -> inc other end
let rec showDef () =
  let _ = reset () in
  let _ = I.sgnApp (begin function | c -> analyze (I.sgnLookup c) end) in
  let _ = print (((^) "Declared: " Int.toString !declared) ^ "\n") in
  let _ = print (((^) "Defined : " Int.toString !defined) ^ "\n") in
  let _ = print (((^) "Abbrevs : " Int.toString !abbrev) ^ "\n") in
  let _ = print (((^) "Other   : " Int.toString !other) ^ "\n") in
  let _ =
    print (((^) "Max definition height: " Int.toString !maxHeight) ^ "\n") in
  let _ =
    ArraySlice.appi
      (begin function
       | (h, i) ->
           print
             (((^) (((^) " Height " Int.toString h) ^ ": ") Int.toString i) ^
                " definitions\n") end)
    (ArraySlice.slice (heightArray, 0, (Some (!maxHeight + 1)))) in
  ()
let reset = reset
let install = install
let installDef = installDef
let installBlock = installBlock
let freeze = freeze
let frozen = frozen
let thaw = thaw
let addSubord = addSubord
let below = below
let belowEq = belowEq
let equiv = equiv
let checkNoDef = checkNoDef
let respects = respects
let respectsN = respectsN
let weaken = weaken
let show = show
let showDef = showDef end



module MemoTable =
  (HashTable)(struct
                     type nonrec key' = (int * int)
                     let hash = begin function | (n, m) -> (7 * n) + m end
                     let eq = (=) end)
module Subordinate =
  (Subordinate)(struct
                       module Global = Global
                       module Whnf = Whnf
                       module Names = Names
                       module Table = IntRedBlackTree
                       module MemoTable = MemoTable
                       module IntSet = IntSet
                     end)