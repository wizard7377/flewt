module type COMPSYN  =
  sig
    type opt_ =
      | No 
      | LinearHeads 
      | Indexing 
    val optimize : opt_ ref
    type goal_ =
      | Atom of IntSyn.exp_ 
      | Impl of
      (((resGoal_ * IntSyn.exp_ * IntSyn.head_ * goal_))(*     | (r,A,a) => g         *))
      
      | All of (IntSyn.dec_ * goal_) 
    and resGoal_ =
      | Eq of IntSyn.exp_ 
      | Assign of (IntSyn.exp_ * auxGoal_) 
      | And of
      (((resGoal_ * IntSyn.exp_ * goal_))(*     | r & (A,g)            *))
      
      | In of
      (((resGoal_ * IntSyn.exp_ * goal_))(*     | r virt& (A,g)        *))
      
      | Exists of (IntSyn.dec_ * resGoal_) 
      | Axists of (IntSyn.dec_ * resGoal_) 
    and auxGoal_ =
      | Trivial 
      | UnifyEq of
      (((IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * auxGoal_))(* call unify *))
      
    type conjunction_ =
      | True 
      | Conjunct of (goal_ * IntSyn.exp_ * conjunction_) 
    type compHead_ =
      | Head of (IntSyn.exp_ * IntSyn.dec_ IntSyn.ctx_ * auxGoal_ *
      IntSyn.cid) 
    type flatterm_ =
      | Pc of int 
      | Dc of int 
      | Csolver of IntSyn.exp_ 
    type nonrec pskeleton = flatterm_ list
    type comDec_ =
      | Parameter 
      | Dec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) 
      | BDec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) list 
      | PDec 
    type dProg_ =
      | DProg of (IntSyn.dctx * comDec_ IntSyn.ctx_) 
    type conDec_ =
      | SClause of resGoal_ 
      | Void 
    val sProgInstall : (IntSyn.cid * conDec_) -> unit
    val sProgLookup : IntSyn.cid -> conDec_
    val sProgReset : unit -> unit
    val detTableInsert : (IntSyn.cid * bool) -> unit
    val detTableCheck : IntSyn.cid -> bool
    val detTableReset : unit -> unit
    val goalSub : (goal_ * IntSyn.sub_) -> goal_
    val resGoalSub : (resGoal_ * IntSyn.sub_) -> resGoal_
    val pskeletonToString : pskeleton -> string
  end


module CompSyn(CompSyn:sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module Table : TABLE
                       end) : COMPSYN =
  struct
    type opt_ =
      | No 
      | LinearHeads 
      | Indexing 
    let optimize = ref LinearHeads
    type goal_ =
      | Atom of IntSyn.exp_ 
      | Impl of
      (((resGoal_ * IntSyn.exp_ * IntSyn.head_ * goal_))(*     | (r,A,a) => g         *))
      
      | All of (IntSyn.dec_ * goal_) 
    and resGoal_ =
      | Eq of IntSyn.exp_ 
      | Assign of (IntSyn.exp_ * auxGoal_) 
      | And of
      (((resGoal_ * IntSyn.exp_ * goal_))(*     | r & (A,g)            *))
      
      | In of
      (((resGoal_ * IntSyn.exp_ * goal_))(*     | r && (A,g)           *))
      
      | Exists of (IntSyn.dec_ * resGoal_) 
      | Axists of (IntSyn.dec_ * resGoal_) 
    and auxGoal_ =
      | Trivial 
      | UnifyEq of
      (((IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * auxGoal_))(* call unify *))
      
    type conjunction_ =
      | True 
      | Conjunct of (goal_ * IntSyn.exp_ * conjunction_) 
    type compHead_ =
      | Head of (IntSyn.exp_ * IntSyn.dec_ IntSyn.ctx_ * auxGoal_ *
      IntSyn.cid) 
    type flatterm_ =
      | Pc of IntSyn.cid 
      | Dc of IntSyn.cid 
      | Csolver of IntSyn.exp_ 
    type nonrec pskeleton = flatterm_ list
    type conDec_ =
      | SClause of resGoal_ 
      | Void 
    type conDecDirect_ =
      | HeadGoals of (compHead_ * conjunction_) 
      | Null 
    type comDec_ =
      | Parameter 
      | Dec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) 
      | BDec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) list 
      | PDec 
    type dProg_ =
      | DProg of (IntSyn.dctx * comDec_ IntSyn.ctx_) 
    let maxCid = Global.maxCid
    let sProgArray = (Array.array ((maxCid + 1), Void) : conDec_ Array.array)
    let (detTable : bool Table.table_) = Table.new_ 32
    let rec sProgInstall (cid, conDec) =
      Array.update (sProgArray, cid, conDec)
    let rec sProgLookup cid = Array.sub (sProgArray, cid)
    let rec sProgReset () = Array.modify (begin function | _ -> Void end)
      sProgArray
    let detTableInsert = Table.insert detTable
    let rec detTableCheck cid =
      begin match Table.lookup detTable cid with
      | Some deterministic -> deterministic
      | None -> false end
  let rec detTableReset () = Table.clear detTable
  let rec goalSub =
    begin function
    | (Atom p, s) -> Atom (IntSyn.EClo (p, s))
    | (Impl (d, a_, Ha, g), s) ->
        Impl
          ((resGoalSub (d, s)), (IntSyn.EClo (a_, s)), Ha,
            (goalSub (g, (IntSyn.dot1 s))))
    | (All (d_, g), s) ->
        All ((IntSyn.decSub (d_, s)), (goalSub (g, (IntSyn.dot1 s)))) end
let rec resGoalSub =
  begin function
  | (Eq q, s) -> Eq (IntSyn.EClo (q, s))
  | (And (r, a_, g), s) ->
      And
        ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (a_, s)),
          (goalSub (g, s)))
  | (In (r, a_, g), s) ->
      In
        ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (a_, s)),
          (goalSub (g, s)))
  | (Exists (d_, r), s) ->
      Exists ((IntSyn.decSub (d_, s)), (resGoalSub (r, (IntSyn.dot1 s)))) end
let rec pskeletonToString =
  begin function
  | [] -> " "
  | (Pc i)::o_ ->
      ((Names.qidToString (Names.constQid i)) ^ " ") ^ (pskeletonToString o_)
  | (Dc i)::o_ ->
      (("(Dc " ^ (Int.toString i)) ^ ") ") ^ (pskeletonToString o_)
  | (Csolver (u_))::o_ -> "(cs _ ) " ^ (pskeletonToString o_) end end 
module CompSyn =
  (CompSyn)(struct
                   module Global = Global
                   module Names = Names
                   module Table = IntRedBlackTree
                 end)