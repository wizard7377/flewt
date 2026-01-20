
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
    val addSubord : IntSyn.cid -> IntSyn.cid -> unit
    val below : IntSyn.cid -> IntSyn.cid -> bool
    val belowEq : IntSyn.cid -> IntSyn.cid -> bool
    val equiv : IntSyn.cid -> IntSyn.cid -> bool
    val respects : IntSyn.dctx -> IntSyn.eclo -> unit
    val respectsN : IntSyn.dctx -> IntSyn.__Exp -> unit
    val checkNoDef : IntSyn.cid -> unit
    val weaken : IntSyn.dctx -> IntSyn.cid -> IntSyn.__Sub
    val show : unit -> unit
    val showDef : unit -> unit
  end;;




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
    let (soGraph : IntSet.intset Table.__Table) = Table.new__ 32
    let insert = Table.insert soGraph
    let rec adjNodes a = valOf (Table.lookup soGraph a)
    let rec insertNewFam a = Table.insert soGraph (a, IntSet.empty)
    let updateFam = Table.insert soGraph
    let (memoTable : (bool * int) MemoTable.__Table) = MemoTable.new__ 2048
    let memoInsert = MemoTable.insert memoTable
    let memoLookup = MemoTable.lookup memoTable
    let memoClear () = MemoTable.clear memoTable
    let memoCounter = ref 0
    let rec appReachable f b =
      let rec rch b visited =
        if IntSet.member (b, visited)
        then visited
        else
          (f b; IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b)) in
      rch (b, IntSet.empty); ()
    exception Reachable 
    let rec reach b a visited =
      let rec rch b visited =
        if IntSet.member (b, visited)
        then visited
        else
          (let adj = adjNodes b in
           if IntSet.member (a, adj)
           then raise Reachable
           else IntSet.foldl rch (IntSet.insert (b, visited)) adj) in
      rch (b, visited)
    let rec reachable b a = reach (b, a, IntSet.empty)
    let rec addNewEdge b a =
      ((!) ((:=) memoCounter) memoCounter) + 1;
      memoInsert ((b, a), (true, (!memoCounter)));
      updateFam (b, (IntSet.insert (a, (adjNodes b))))
    let (fTable : bool Table.__Table) = Table.new__ 32
    let fLookup = Table.lookup fTable
    let fInsert = Table.insert fTable
    let rec fGet a =
      match fLookup a with | Some frozen -> frozen | None -> false
    let rec fSet a frozen =
      let _ =
        Global.chPrint 5
          (fun () ->
             ((^) (if frozen then "Freezing " else "Thawing ")
                Names.qidToString (Names.constQid a))
               ^ "\n") in
      fInsert (a, frozen)
    let rec checkFreeze c a =
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
    let rec freeze (__L) =
      let _ = freezeList := IntSet.empty in
      let __L' = map expandFamilyAbbrevs __L in
      let _ =
        List.app
          (fun a ->
             appReachable
               (fun b ->
                  fSet (b, true);
                  (:=) freezeList IntSet.insert (b, (!freezeList))) a) __L' in
      let cids = IntSet.foldl (::) nil (!freezeList) in cids
    let rec frozen (__L) =
      let __L' = map expandFamilyAbbrevs __L in
      List.exists (fun a -> fGet a) __L'
    let rec computeBelow a b =
      try
        reachable (b, a);
        memoInsert ((b, a), (false, (!memoCounter)));
        false
      with
      | Reachable -> (memoInsert ((b, a), (true, (!memoCounter))); true)
    let rec below a b =
      ((match memoLookup (b, a) with
        | None -> computeBelow (a, b)
        | Some (true, c) -> true
        | Some (false, c) ->
            if (!) ((=) c) memoCounter then false else computeBelow (a, b))
      (* true entries remain valid *))
    let rec belowEq a b = (a = b) || (below (a, b))
    let rec equiv a b = (belowEq (a, b)) && (belowEq (b, a))
    let rec addSubord a b =
      if below (a, b)
      then ()
      else
        ((if fGet b
          then
            raise
              (Error
                 ((^) (((^) "Freezing violation: " Names.qidToString
                          (Names.constQid b))
                         ^ " would depend on ")
                    Names.qidToString (Names.constQid a)))
          else addNewEdge (b, a))
        (* if b is frozen and not already b #> a *)(* subordination would change; signal error *))
    let (aboveList : IntSyn.cid list ref) = ref nil
    let rec addIfBelowEq a's b =
      if List.exists (fun a -> belowEq (a, b)) a's
      then (aboveList := b) :: (!aboveList)
      else ()
    let rec thaw a's =
      let a's' = map expandFamilyAbbrevs a's in
      let _ = aboveList := nil in
      let _ = Table.app (fun b -> fun _ -> addIfBelowEq a's' b) soGraph in
      let _ = List.app (fun b -> fSet (b, false)) (!aboveList) in
      !aboveList
    let (defGraph : IntSet.intset Table.__Table) = Table.new__ 32
    let rec occursInDef a =
      match Table.lookup defGraph a with | None -> false | Some _ -> true
    let rec insertNewDef b a =
      match Table.lookup defGraph a with
      | None -> Table.insert defGraph (a, (IntSet.insert (b, IntSet.empty)))
      | Some bs -> Table.insert defGraph (a, (IntSet.insert (b, bs)))
    let rec installConDec __0__ __1__ =
      match (__0__, __1__) with
      | (b, ConDef (_, _, _, __A, __K, I.Kind, _)) ->
          insertNewDef (b, (I.targetFam __A))
      | _ -> ()(* I.targetFam must be defined, but expands definitions! *)
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
          (fun a' ->
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
    let rec installTypeN' __2__ __3__ =
      match (__2__, __3__) with
      | (Pi (((Dec (_, __V1) as D), _), __V2), a) ->
          (addSubord ((I.targetFam __V1), a);
           installTypeN __V1;
           installTypeN' (__V2, a))
      | ((Root (Def _, _) as V), a) ->
          let __V' = Whnf.normalize (Whnf.expandDef (__V, I.id)) in
          installTypeN' (__V', a)
      | (Root _, _) -> ()(* Sun Nov 10 11:15:47 2002 -fp *)
      (* this looks like blatant overkill ... *)
    let rec installTypeN (__V) = installTypeN' (__V, (I.targetFam __V))
    let rec installKindN __4__ __5__ =
      match (__4__, __5__) with
      | (Uni (__L), a) -> ()
      | (Pi ((Dec (_, __V1), __P), __V2), a) ->
          (addSubord ((I.targetFam __V1), a);
           installTypeN __V1;
           installKindN (__V2, a))
    let rec install c =
      let __V = I.constType c in
      match I.targetFamOpt __V with
      | None -> (insertNewFam c; installKindN (__V, c))
      | Some a ->
          ((((((match IntSyn.sgnLookup c with
                | ConDec _ -> checkFreeze (c, a)
                | SkoDec _ -> checkFreeze (c, a)
                | _ -> ()))
             (* FIX: skolem types should probably be created frozen -kw *));
             installTypeN' (__V, a)))
          (* simplified  Tue Mar 27 20:58:31 2001 -fp *))
    let rec installDec (Dec (_, __V)) = installTypeN __V
    let rec installSome =
      function
      | I.Null -> ()
      | Decl (__G, __D) -> (installSome __G; installDec __D)
    let rec installBlock b =
      let BlockDec (_, _, __G, __Ds) = I.sgnLookup b in
      installSome __G; List.app (fun (__D) -> installDec __D) __Ds
    let rec checkBelow a b =
      if not (below (a, b))
      then
        raise
          (Error
             ((^) (((^) "Subordination violation: " Names.qidToString
                      (Names.constQid a))
                     ^ " not <| ")
                Names.qidToString (Names.constQid b)))
      else ()
    let rec respectsTypeN' __6__ __7__ =
      match (__6__, __7__) with
      | (Pi (((Dec (_, __V1) as D), _), __V2), a) ->
          (checkBelow ((I.targetFam __V1), a);
           respectsTypeN __V1;
           respectsTypeN' (__V2, a))
      | ((Root (Def _, _) as V), a) ->
          let __V' = Whnf.normalize (Whnf.expandDef (__V, I.id)) in
          respectsTypeN' (__V', a)
      | (Root _, _) -> ()(* Sun Nov 10 11:15:47 2002 -fp *)
      (* this looks like blatant overkill ... *)
    let rec respectsTypeN (__V) = respectsTypeN' (__V, (I.targetFam __V))
    let rec respects (__G) (__V, s) = respectsTypeN (Whnf.normalize (__V, s))
    let rec respectsN (__G) (__V) = respectsTypeN __V
    let rec famsToString bs msg =
      IntSet.foldl
        (fun a ->
           fun msg -> ((Names.qidToString (Names.constQid a)) ^ " ") ^ msg)
        "\n" bs
    let rec showFam a bs =
      print
        ((^) ((Names.qidToString (Names.constQid a)) ^
                (if fGet a then " #> " else " |> "))
           famsToString (bs, "\n"))
    let rec show () = Table.app showFam soGraph
    let rec weaken __8__ __9__ =
      match (__8__, __9__) with
      | (I.Null, a) -> I.id
      | (Decl (__G', (Dec (name, __V) as D)), a) ->
          let w' = weaken (__G', a) in
          if belowEq ((I.targetFam __V), a)
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
      Array.modify (fun i -> 0) heightArray;
      maxHeight := 0
    let rec analyzeAnc =
      function
      | Anc (None, _, _) -> incArray 0
      | Anc (_, h, _) -> (incArray h; max h)
    let rec analyze =
      function
      | ConDec (_, _, _, _, _, __L) -> inc declared
      | ConDef (_, _, _, _, _, __L, ancestors) ->
          (inc defined; analyzeAnc ancestors)
      | AbbrevDef (_, _, _, _, _, __L) -> inc abbrev
      | _ -> inc other
    let rec showDef () =
      let _ = reset () in
      let _ = I.sgnApp (fun c -> analyze (I.sgnLookup c)) in
      let _ = print (((^) "Declared: " Int.toString (!declared)) ^ "\n") in
      let _ = print (((^) "Defined : " Int.toString (!defined)) ^ "\n") in
      let _ = print (((^) "Abbrevs : " Int.toString (!abbrev)) ^ "\n") in
      let _ = print (((^) "Other   : " Int.toString (!other)) ^ "\n") in
      let _ =
        print
          (((^) "Max definition height: " Int.toString (!maxHeight)) ^ "\n") in
      let _ =
        ArraySlice.appi
          (fun h ->
             fun i ->
               print
                 (((^) (((^) " Height " Int.toString h) ^ ": ") Int.toString
                     i)
                    ^ " definitions\n"))
          (ArraySlice.slice (heightArray, 0, (Some ((!maxHeight) + 1)))) in
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
    let showDef = showDef
  end ;;




module MemoTable =
  (Make_HashTable)(struct
                     type nonrec key' = (int * int)
                     let hash n m = (7 * n) + m
                     let eq = (=)
                   end)
module Subordinate =
  (Make_Subordinate)(struct
                       module Global = Global
                       module Whnf = Whnf
                       module Names = Names
                       module Table = IntRedBlackTree
                       module MemoTable = MemoTable
                       module IntSet = IntSet
                     end);;
