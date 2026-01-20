
module type COMPSYN  =
  sig
    type __Opt =
      | No 
      | LinearHeads 
      | Indexing 
    val optimize : __Opt ref
    type __Goal =
      | Atom of IntSyn.__Exp 
      | Impl of
      (((__ResGoal * IntSyn.__Exp * IntSyn.__Head * __Goal))(*     | (r,A,a) => g         *))
      
      | All of (IntSyn.__Dec * __Goal) 
    and __ResGoal =
      | Eq of IntSyn.__Exp 
      | Assign of (IntSyn.__Exp * __AuxGoal) 
      | And of
      (((__ResGoal * IntSyn.__Exp * __Goal))(*     | r & (A,g)            *))
      
      | In of
      (((__ResGoal * IntSyn.__Exp * __Goal))(*     | r virt& (A,g)        *))
      
      | Exists of (IntSyn.__Dec * __ResGoal) 
      | Axists of (IntSyn.__Dec * __ResGoal) 
    and __AuxGoal =
      | Trivial 
      | UnifyEq of
      (((IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __AuxGoal))(* call unify *))
      
    type __Conjunction =
      | True 
      | Conjunct of (__Goal * IntSyn.__Exp * __Conjunction) 
    type __CompHead =
      | Head of (IntSyn.__Exp * IntSyn.__Dec IntSyn.__Ctx * __AuxGoal *
      IntSyn.cid) 
    type __Flatterm =
      | Pc of int 
      | Dc of int 
      | Csolver of IntSyn.__Exp 
    type nonrec pskeleton = __Flatterm list
    type __ComDec =
      | Parameter 
      | Dec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) 
      | BDec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) list 
      | PDec 
    type __DProg =
      | DProg of (IntSyn.dctx * __ComDec IntSyn.__Ctx) 
    type __ConDec =
      | SClause of __ResGoal 
      | Void 
    val sProgInstall : IntSyn.cid -> __ConDec -> unit
    val sProgLookup : IntSyn.cid -> __ConDec
    val sProgReset : unit -> unit
    val detTableInsert : IntSyn.cid -> bool -> unit
    val detTableCheck : IntSyn.cid -> bool
    val detTableReset : unit -> unit
    val goalSub : __Goal -> IntSyn.__Sub -> __Goal
    val resGoalSub : __ResGoal -> IntSyn.__Sub -> __ResGoal
    val pskeletonToString : pskeleton -> string
  end;;




module CompSyn(CompSyn:sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module Table : TABLE
                       end) : COMPSYN =
  struct
    type __Opt =
      | No 
      | LinearHeads 
      | Indexing 
    let optimize = ref LinearHeads
    type __Goal =
      | Atom of IntSyn.__Exp 
      | Impl of
      (((__ResGoal * IntSyn.__Exp * IntSyn.__Head * __Goal))(*     | (r,A,a) => g         *))
      
      | All of (IntSyn.__Dec * __Goal) 
    and __ResGoal =
      | Eq of IntSyn.__Exp 
      | Assign of (IntSyn.__Exp * __AuxGoal) 
      | And of
      (((__ResGoal * IntSyn.__Exp * __Goal))(*     | r & (A,g)            *))
      
      | In of
      (((__ResGoal * IntSyn.__Exp * __Goal))(*     | r && (A,g)           *))
      
      | Exists of (IntSyn.__Dec * __ResGoal) 
      | Axists of (IntSyn.__Dec * __ResGoal) 
    and __AuxGoal =
      | Trivial 
      | UnifyEq of
      (((IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __AuxGoal))(* call unify *))
      
    type __Conjunction =
      | True 
      | Conjunct of (__Goal * IntSyn.__Exp * __Conjunction) 
    type __CompHead =
      | Head of (IntSyn.__Exp * IntSyn.__Dec IntSyn.__Ctx * __AuxGoal *
      IntSyn.cid) 
    type __Flatterm =
      | Pc of IntSyn.cid 
      | Dc of IntSyn.cid 
      | Csolver of IntSyn.__Exp 
    type nonrec pskeleton = __Flatterm list
    type __ConDec =
      | SClause of __ResGoal 
      | Void 
    type __ConDecDirect =
      | HeadGoals of (__CompHead * __Conjunction) 
      | Null 
    type __ComDec =
      | Parameter 
      | Dec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) 
      | BDec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) list 
      | PDec 
    type __DProg =
      | DProg of (IntSyn.dctx * __ComDec IntSyn.__Ctx) 
    let maxCid = Global.maxCid
    let sProgArray =
      (Array.array ((maxCid + 1), Void) : __ConDec Array.array)
    let (detTable : bool Table.__Table) = Table.new__ 32
    let rec sProgInstall cid conDec = Array.update (sProgArray, cid, conDec)
    let rec sProgLookup cid = Array.sub (sProgArray, cid)
    let rec sProgReset () = Array.modify (fun _ -> Void) sProgArray
    let detTableInsert = Table.insert detTable
    let rec detTableCheck cid =
      match Table.lookup detTable cid with
      | Some deterministic -> deterministic
      | None -> false
    let rec detTableReset () = Table.clear detTable
    let rec goalSub __0__ __1__ =
      match (__0__, __1__) with
      | (Atom p, s) -> Atom (IntSyn.EClo (p, s))
      | (Impl (d, __A, Ha, g), s) ->
          Impl
            ((resGoalSub (d, s)), (IntSyn.EClo (__A, s)), Ha,
              (goalSub (g, (IntSyn.dot1 s))))
      | (All (__D, g), s) ->
          All ((IntSyn.decSub (__D, s)), (goalSub (g, (IntSyn.dot1 s))))
    let rec resGoalSub __2__ __3__ =
      match (__2__, __3__) with
      | (Eq q, s) -> Eq (IntSyn.EClo (q, s))
      | (And (r, __A, g), s) ->
          And
            ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (__A, s)),
              (goalSub (g, s)))
      | (In (r, __A, g), s) ->
          In
            ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (__A, s)),
              (goalSub (g, s)))
      | (Exists (__D, r), s) ->
          Exists
            ((IntSyn.decSub (__D, s)), (resGoalSub (r, (IntSyn.dot1 s))))
    let rec pskeletonToString =
      function
      | [] -> " "
      | (Pc i)::__O ->
          ((Names.qidToString (Names.constQid i)) ^ " ") ^
            (pskeletonToString __O)
      | (Dc i)::__O ->
          (("(Dc " ^ (Int.toString i)) ^ ") ") ^ (pskeletonToString __O)
      | (Csolver (__U))::__O -> "(cs _ ) " ^ (pskeletonToString __O)
  end 
module CompSyn =
  (Make_CompSyn)(struct
                   module Global = Global
                   module Names = Names
                   module Table = IntRedBlackTree
                 end);;
