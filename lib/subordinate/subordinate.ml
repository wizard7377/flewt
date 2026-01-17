
module type SUBORDINATE  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Modified: Frank Pfenning *)
      (* Author: Carsten Schuermann *)(* Subordination *))
      
    val reset : unit -> unit
    val install : IntSyn.cid -> unit
    val installDef : IntSyn.cid -> unit
    val installBlock : IntSyn.cid -> unit
    val freeze :
      IntSyn.cid list ->
        ((IntSyn.cid)(* superseded by freeze *)(* val installFrozen : IntSyn.cid list -> unit *))
          list
    val thaw :
      IntSyn.cid list ->
        ((IntSyn.cid)(* transitive freeze, returns frozen cids *))
          list
    val frozen :
      IntSyn.cid list ->
        ((bool)(* reverse transitive thaw, returns thawed cids *))
    val addSubord :
      (IntSyn.cid * IntSyn.cid) ->
        ((unit)(* any cid in list frozen? *))
    val below : (IntSyn.cid * IntSyn.cid) -> bool
    val belowEq :
      (IntSyn.cid * IntSyn.cid) ->
        ((bool)(* transitive closure *))
    val equiv :
      (IntSyn.cid * IntSyn.cid) ->
        ((bool)(* refl. transitive closure *))
    val respects :
      (IntSyn.dctx * IntSyn.eclo) ->
        ((unit)(* mutual dependency *))
    val respectsN :
      (IntSyn.dctx * IntSyn.__Exp) ->
        ((unit)(* respects current subordination? *))
    val checkNoDef :
      IntSyn.cid -> ((unit)(* respectsN(G, V), V in nf *))
    val weaken :
      (IntSyn.dctx * IntSyn.cid) ->
        ((IntSyn.__Sub)(* not involved in type-level definition? *))
    val show : unit -> unit
    val showDef : unit -> unit
  end;;




module Subordinate(Subordinate:sig
                                 module Global : GLOBAL
                                 module Whnf : WHNF
                                 module Names : NAMES
                                 module Table : TABLE
                                 module MemoTable : TABLE
                                 module IntSet :
                                 ((INTSET)(* Subordination a la Virga [Technical Report 96] *)
                                 (* Author: Carsten Schuermann *)
                                 (* Reverse subordination order *)
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Names.IntSyn = IntSyn' !*))
                               end) : SUBORDINATE =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    module I = IntSyn
    let (soGraph : IntSet.intset Table.__Table) = Table.new__ 32
    let insert = Table.insert soGraph
    let rec adjNodes a = valOf (Table.lookup soGraph a)
    let rec insertNewFam a = Table.insert soGraph (a, IntSet.empty)
    let updateFam = Table.insert soGraph
    let (memoTable : (bool * int) MemoTable.__Table) = MemoTable.new__ 2048
    let memoInsert = MemoTable.insert memoTable
    let memoLookup = MemoTable.lookup memoTable
    let memoClear = function | () -> MemoTable.clear memoTable
    let memoCounter = ref 0
    let rec appReachable f b =
      let rch (b, visited) =
        if IntSet.member (b, visited)
        then visited
        else
          (f b; IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b)) in
      rch (b, IntSet.empty); ()
    exception Reachable 
    let rec reach (b, a, visited) =
      let rch (b, visited) =
        if IntSet.member (b, visited)
        then visited
        else
          (let adj = adjNodes b in
           if IntSet.member (a, adj)
           then raise Reachable
           else IntSet.foldl rch (IntSet.insert (b, visited)) adj) in
      rch (b, visited)
    let rec reachable (b, a) = reach (b, a, IntSet.empty)
    let rec addNewEdge (b, a) =
      ((!) ((:=) memoCounter) memoCounter) + 1;
      memoInsert ((b, a), (true__, (!memoCounter)));
      updateFam (b, (IntSet.insert (a, (adjNodes b))))
    let (fTable : bool Table.__Table) = Table.new__ 32
    let fLookup = Table.lookup fTable
    let fInsert = Table.insert fTable
    let rec fGet a =
      match fLookup a with | SOME frozen -> frozen | NONE -> false__
    let rec fSet (a, frozen) =
      let _ =
        Global.chPrint 5
          (function
           | () ->
               ((^) (if frozen then "Freezing " else "Thawing ")
                  Names.qidToString (Names.constQid a))
                 ^ "\n") in
      fInsert (a, frozen)
    let rec checkFreeze (c, a) =
      if fGet a
      then
        raise
          (Error
             ((^) (((^) "Freezing violation: constant " Names.qidToString
                      (Names.constQid c))
                     ^ "\nextends type family ")
                Names.qidToString (Names.constQid a)))
      else ()
    let rec expandFamilyAbbrevs a =
      match I.constUni a with
      | I.Type ->
          raise
            (Error
               (((^) "Constant " Names.qidToString (Names.constQid a)) ^
                  " must be a type family to be frozen or thawed"))
      | I.Kind ->
          (match IntSyn.sgnLookup a with
           | ConDec _ -> a
           | ConDef _ -> IntSyn.targetFam (IntSyn.constDef a)
           | SkoDec _ -> a
           | AbbrevDef _ -> IntSyn.targetFam (IntSyn.constDef a))
    let (freezeList : IntSet.intset ref) = ref IntSet.empty
    let rec freeze (L) =
      let _ = freezeList := IntSet.empty in
      let L' = map expandFamilyAbbrevs L in
      let _ =
        List.app
          (function
           | a ->
               appReachable
                 (function
                  | b ->
                      (fSet (b, true__);
                       (:=) freezeList IntSet.insert (b, (!freezeList)))) a)
          L' in
      let cids = IntSet.foldl (::) nil (!freezeList) in cids
    let rec frozen (L) =
      let L' = map expandFamilyAbbrevs L in
      List.exists (function | a -> fGet a) L'
    let rec computeBelow (a, b) =
      try
        reachable (b, a);
        memoInsert ((b, a), (false__, (!memoCounter)));
        false__
      with
      | Reachable -> (memoInsert ((b, a), (true__, (!memoCounter))); true__)
    let rec below (a, b) =
      match memoLookup (b, a) with
      | NONE -> computeBelow (a, b)
      | SOME (true__, c) -> true__
      | SOME (false__, c) ->
          if (!) ((=) c) memoCounter then false__ else computeBelow (a, b)
    let rec belowEq (a, b) = (a = b) || (below (a, b))
    let rec equiv (a, b) = (belowEq (a, b)) && (belowEq (b, a))
    let rec addSubord (a, b) =
      if below (a, b)
      then ()
      else
        if fGet b
        then
          raise
            (Error
               ((^) (((^) "Freezing violation: " Names.qidToString
                        (Names.constQid b))
                       ^ " would depend on ")
                  Names.qidToString (Names.constQid a)))
        else addNewEdge (b, a)
    let (aboveList : IntSyn.cid list ref) = ref nil
    let rec addIfBelowEq a's =
      function
      | b ->
          if List.exists (function | a -> belowEq (a, b)) a's
          then (aboveList := b) :: (!aboveList)
          else ()
    let rec thaw a's =
      let a's' = map expandFamilyAbbrevs a's in
      let _ = aboveList := nil in
      let _ = Table.app (function | (b, _) -> addIfBelowEq a's' b) soGraph in
      let _ = List.app (function | b -> fSet (b, false__)) (!aboveList) in
      !aboveList
    let (defGraph : IntSet.intset Table.__Table) = Table.new__ 32
    let rec occursInDef a =
      match Table.lookup defGraph a with | NONE -> false__ | SOME _ -> true__
    let rec insertNewDef (b, a) =
      match Table.lookup defGraph a with
      | NONE -> Table.insert defGraph (a, (IntSet.insert (b, IntSet.empty)))
      | SOME bs -> Table.insert defGraph (a, (IntSet.insert (b, bs)))
    let rec installConDec =
      function
      | (b, ConDef (_, _, _, A, K, I.Kind, _)) ->
          insertNewDef (b, (I.targetFam A))
      | _ -> ()
    let rec installDef c = installConDec (c, (I.sgnLookup c))
    let rec checkNoDef a =
      if occursInDef a
      then
        raise
          (Error
             (((^) "Definition violation: family " Names.qidToString
                 (Names.constQid a))
                ^ "\noccurs as right-hand side of type-level definition"))
      else
        appReachable
          (function
           | a' ->
               if occursInDef a'
               then
                 raise
                   (Error
                      (((^) (((^) "Definition violation: family "
                                Names.qidToString (Names.constQid a))
                               ^ " |> ")
                          Names.qidToString (Names.constQid a'))
                         ^
                         ",\nwhich occurs as right-hand side of a type-level definition"))
               else ()) a
    let rec reset () =
      Table.clear soGraph;
      Table.clear fTable;
      MemoTable.clear memoTable;
      Table.clear defGraph
    let rec installTypeN' =
      function
      | (Pi (((Dec (_, V1) as D), _), V2), a) ->
          (addSubord ((I.targetFam V1), a);
           installTypeN V1;
           installTypeN' (V2, a))
      | ((Root (Def _, _) as V), a) ->
          let V' = Whnf.normalize (Whnf.expandDef (V, I.id)) in
          installTypeN' (V', a)
      | (Root _, _) -> ()
    let rec installTypeN (V) = installTypeN' (V, (I.targetFam V))
    let rec installKindN =
      function
      | (Uni (L), a) -> ()
      | (Pi ((Dec (_, V1), P), V2), a) ->
          (addSubord ((I.targetFam V1), a);
           installTypeN V1;
           installKindN (V2, a))
    let rec install c =
      let V = I.constType c in
      match I.targetFamOpt V with
      | NONE -> (insertNewFam c; installKindN (V, c))
      | SOME a ->
          ((match IntSyn.sgnLookup c with
            | ConDec _ -> checkFreeze (c, a)
            | SkoDec _ -> checkFreeze (c, a)
            | _ -> ());
           installTypeN' (V, a))
    let rec installDec (Dec (_, V)) = installTypeN V
    let rec installSome =
      function | I.Null -> () | Decl (G, D) -> (installSome G; installDec D)
    let rec installBlock b =
      let BlockDec (_, _, G, Ds) = I.sgnLookup b in
      installSome G; List.app (function | D -> installDec D) Ds
    let rec checkBelow (a, b) =
      if not (below (a, b))
      then
        raise
          (Error
             ((^) (((^) "Subordination violation: " Names.qidToString
                      (Names.constQid a))
                     ^ " not <| ")
                Names.qidToString (Names.constQid b)))
      else ()
    let rec respectsTypeN' =
      function
      | (Pi (((Dec (_, V1) as D), _), V2), a) ->
          (checkBelow ((I.targetFam V1), a);
           respectsTypeN V1;
           respectsTypeN' (V2, a))
      | ((Root (Def _, _) as V), a) ->
          let V' = Whnf.normalize (Whnf.expandDef (V, I.id)) in
          respectsTypeN' (V', a)
      | (Root _, _) -> ()
    let rec respectsTypeN (V) = respectsTypeN' (V, (I.targetFam V))
    let rec respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
    let rec respectsN (G, V) = respectsTypeN V
    let rec famsToString (bs, msg) =
      IntSet.foldl
        (function
         | (a, msg) -> ((Names.qidToString (Names.constQid a)) ^ " ") ^ msg)
        "\n" bs
    let rec showFam (a, bs) =
      print
        ((^) ((Names.qidToString (Names.constQid a)) ^
                (if fGet a then " #> " else " |> "))
           famsToString (bs, "\n"))
    let rec show () = Table.app showFam soGraph
    let rec weaken =
      function
      | (I.Null, a) -> I.id
      | (Decl (G', (Dec (name, V) as D)), a) ->
          let w' = weaken (G', a) in
          if belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let declared = ref 0
    let defined = ref 0
    let abbrev = ref 0
    let other = ref 0
    let heightArray = Array.array (32, 0)
    let maxHeight = ref 0
    let rec inc r = ((!) ((:=) r) r) + 1
    let rec incArray h =
      Array.update (heightArray, h, ((Array.sub (heightArray, h)) + 1))
    let rec max h = (:=) maxHeight Int.max (h, (!maxHeight))
    let rec reset () =
      declared := 0;
      defined := 0;
      abbrev := 0;
      other := 0;
      Array.modify (function | i -> 0) heightArray;
      maxHeight := 0
    let rec analyzeAnc =
      function
      | Anc (NONE, _, _) -> incArray 0
      | Anc (_, h, _) -> (incArray h; max h)
    let rec analyze =
      function
      | ConDec (_, _, _, _, _, L) -> inc declared
      | ConDef (_, _, _, _, _, L, ancestors) ->
          (inc defined; analyzeAnc ancestors)
      | AbbrevDef (_, _, _, _, _, L) -> inc abbrev
      | _ -> inc other
    let rec showDef () =
      let _ = reset () in
      let _ = I.sgnApp (function | c -> analyze (I.sgnLookup c)) in
      let _ = print (((^) "Declared: " Int.toString (!declared)) ^ "\n") in
      let _ = print (((^) "Defined : " Int.toString (!defined)) ^ "\n") in
      let _ = print (((^) "Abbrevs : " Int.toString (!abbrev)) ^ "\n") in
      let _ = print (((^) "Other   : " Int.toString (!other)) ^ "\n") in
      let _ =
        print
          (((^) "Max definition height: " Int.toString (!maxHeight)) ^ "\n") in
      let _ =
        ArraySlice.appi
          (function
           | (h, i) ->
               print
                 (((^) (((^) " Height " Int.toString h) ^ ": ") Int.toString
                     i)
                    ^ " definitions\n"))
          (ArraySlice.slice (heightArray, 0, (SOME ((!maxHeight) + 1)))) in
      ()
    let ((reset)(* Subordination graph

       soGraph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)
      (* must be defined! *)(* memotable to avoid repeated graph traversal *)
      (* think of hash-table model *)(* Apply f to every node reachable from b *)
      (* Includes the node itself (reflexive) *)(* b must be new *)
      (* this is sometimes violated below, is this a bug? *)
      (* Thu Mar 10 13:13:01 2005 -fp *)(*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)
      (* pre: a is not a type definition *)(* no longer needed since freeze is now transitive *)
      (* Sat Mar 12 21:40:15 2005 -fp *)(*
    fun frozenSubError (a, b) =
        raise Error ("Freezing violation: frozen type family "
                     ^ Names.qidToString (Names.constQid b)
                     ^ "\nwould depend on unfrozen type family "
                     ^ Names.qidToString (Names.constQid a))
    *)
      (* no longer needed since freeze is now transitive *)
      (* Sat Mar 12 21:40:15 2005 -fp *)(* pre: a, b are not type definitions *)
      (*
    fun checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())
    *)
      (* pre: b is not a type definition *)(* no longer needed since freeze is transitive *)
      (* Sat Mar 12 21:38:58 2005 -fp *)(*
    fun checkMakeFrozen (b, otherFrozen) =
         Is this broken ??? *)
      (* Mon Nov 11 16:54:29 2002 -fp *)(* Example:
           a : type.
           b : type.
           %freeze a b.
           h : (a -> b) -> type.
           is OK, but as b |> a in its subordination
        *)
      (* superseded by freeze *)(*
    fun installFrozen (L) =
        let
          val L = map expandFamilyAbbrevs L
           val _ = print ("L = " ^ (foldl (fn (c,s) => Names.qidToString (Names.constQid c) ^ s) "\n" L)); *)
      (* freeze L = ()
       freezes all families in L, and all families transitively
       reachable from families in L

       Intended to be called from programs
    *)
      (* frozen L = true if one of the families in L is frozen *)
      (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
      (* true entries remain valid *)(* false entries are invalidated *)
      (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
      (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
      (* if b is frozen and not already b #> a *)(* subordination would change; signal error *)
      (* Thawing frozen families *)(* Returns list of families that were thawed *)
      (*
       Definition graph
       The definitions graph keeps track of chains of
       definitions for type families (not object-level definitions)

       We say b <# a if b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S

       The definition graph should be interpreted transitively.
       It can never be reflexive.

       The #> relation is stored in order to prevent totality
       checking on type families involved in definitions, because
       in the present implementation this would yield unsound
       results.

       NOTE: presently, the head "a" is always expanded until it is
       no longer a definition.  So if a #> b then a is always declared,
       never defined and b is always defined, never declared.

       Fri Dec 27 08:37:42 2002 -fp (just before 1.4 alpha)
    *)
      (* occursInDef a = true
       iff there is a b such that a #> b
    *)
      (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)
      (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)
      (* I.targetFam must be defined, but expands definitions! *)
      (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for some a' < a.
    *)
      (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)
      (*
       Subordination checking no longer traverses spines,
       so approximate types are no longer necessary.
       This takes stronger advantage of the normal form invariant.
       Mon Nov 11 16:59:52 2002  -fp
    *)
      (* installTypeN' (V, a) = ()
       installTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: add subordination info from V into table
    *)
      (* this looks like blatant overkill ... *)(* Sun Nov 10 11:15:47 2002 -fp *)
      (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
      (* there are no kind-level definitions *)(* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
      (* FIX: skolem types should probably be created frozen -kw *)
      (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
      (* installBlock b = ()
       Effect: if b : Block, add subordination from Block into table
    *)
      (* BDec, ADec, NDec are disallowed here *)(* b must be block *)
      (* Respecting subordination *)(* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
      (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
      (* this looks like blatant overkill ... *)(* Sun Nov 10 11:15:47 2002 -fp *)
      (* Printing *)(* Right now, AL is in always reverse order *)
      (* Reverse again --- do not sort *)(* Right now, Table.app will pick int order -- do not sort *)
      (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)
      (* weaken (G, a) = (w') *)(* showDef () = ()
       Effect: print some statistics about constant definitions
    *)
      (* ignore blocks and skolem constants *)) = reset
    let install = install
    let installDef = installDef
    let installBlock = installBlock
    let ((freeze)(* val installFrozen = installFrozen *)) =
      freeze
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
    let showDef = showDef
  end ;;




module MemoTable =
  (Make_HashTable)(struct
                     type nonrec key' = (int * int)
                     let hash = function | (n, m) -> (7 * n) + m
                     let eq = (=)
                   end)
module Subordinate =
  (Make_Subordinate)(struct
                       module Global = Global
                       module Whnf =
                         ((Whnf)(*! structure IntSyn' = IntSyn !*))
                       module Names = Names
                       module Table = IntRedBlackTree
                       module MemoTable = MemoTable
                       module IntSet = IntSet
                     end);;
