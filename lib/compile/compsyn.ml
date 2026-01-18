
(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
module type COMPSYN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    type __Opt =
      | No 
      | LinearHeads 
      | Indexing 
    val optimize : __Opt ref
    type __Goal =
      | Atom of IntSyn.__Exp 
      | Impl of (__ResGoal * IntSyn.__Exp * IntSyn.__Head * __Goal) 
      | All of (IntSyn.__Dec * __Goal) 
    and __ResGoal =
      | Eq of IntSyn.__Exp 
      | Assign of (IntSyn.__Exp * __AuxGoal) 
      | And of (__ResGoal * IntSyn.__Exp * __Goal) 
      | In of (__ResGoal * IntSyn.__Exp * __Goal) 
      | Exists of (IntSyn.__Dec * __ResGoal) 
      | Axists of (IntSyn.__Dec * __ResGoal) 
    and __AuxGoal =
      | Trivial 
      | UnifyEq of (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __AuxGoal) 
    (*     | (r,A,a) => g         *)
    (*     | r & (A,g)            *)
    (*     | r virt& (A,g)        *)
    (* call unify *)
    (* Static programs -- compiled version for substitution trees *)
    type __Conjunction =
      | True 
      | Conjunct of (__Goal * IntSyn.__Exp * __Conjunction) 
    type __CompHead =
      | Head of (IntSyn.__Exp * IntSyn.__Dec IntSyn.__Ctx * __AuxGoal *
      IntSyn.cid) 
    (* pskeleton instead of proof term *)
    type __Flatterm =
      | Pc of int 
      | Dc of int 
      | Csolver of IntSyn.__Exp 
    type nonrec pskeleton = __Flatterm list
    (* The dynamic clause pool --- compiled version of the context *)
    (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)
    (* Compiled Declarations *)
    (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
    type __ComDec =
      | Parameter 
      | Dec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) 
      | BDec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) list 
      | PDec 
    (* Dynamic programs: context with synchronous clause pool *)
    type __DProg =
      | DProg of (IntSyn.dctx * __ComDec IntSyn.__Ctx) 
    (* Programs --- compiled version of the signature (no direct head access) *)
    type __ConDec =
      | SClause of __ResGoal 
      | Void 
    (* Other declarations are ignored  *)
    (* Install Programs (without indexing) *)
    val sProgInstall : (IntSyn.cid * __ConDec) -> unit
    val sProgLookup : IntSyn.cid -> __ConDec
    val sProgReset : unit -> unit
    (* Deterministic flag *)
    val detTableInsert : (IntSyn.cid * bool) -> unit
    val detTableCheck : IntSyn.cid -> bool
    val detTableReset : unit -> unit
    (* Explicit Substitutions *)
    val goalSub : (__Goal * IntSyn.__Sub) -> __Goal
    val resGoalSub : (__ResGoal * IntSyn.__Sub) -> __ResGoal
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
      | Impl of (__ResGoal * IntSyn.__Exp * IntSyn.__Head * __Goal) 
      | All of (IntSyn.__Dec * __Goal) 
    and __ResGoal =
      | Eq of IntSyn.__Exp 
      | Assign of (IntSyn.__Exp * __AuxGoal) 
      | And of (__ResGoal * IntSyn.__Exp * __Goal) 
      | In of (__ResGoal * IntSyn.__Exp * __Goal) 
      | Exists of (IntSyn.__Dec * __ResGoal) 
      | Axists of (IntSyn.__Dec * __ResGoal) 
    and __AuxGoal =
      | Trivial 
      | UnifyEq of (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __AuxGoal) 
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
    let rec sProgInstall (cid, conDec) =
      Array.update (sProgArray, cid, conDec)
    let rec sProgLookup cid = Array.sub (sProgArray, cid)
    let rec sProgReset () = Array.modify (function | _ -> Void) sProgArray
    let detTableInsert = Table.insert detTable
    let rec detTableCheck cid =
      match Table.lookup detTable cid with
      | Some deterministic -> deterministic
      | None -> false__
    let rec detTableReset () = Table.clear detTable
    let rec goalSub =
      function
      | (Atom p, s) -> Atom (IntSyn.EClo (p, s))
      | (Impl (d, A, Ha, g), s) ->
          Impl
            ((resGoalSub (d, s)), (IntSyn.EClo (A, s)), Ha,
              (goalSub (g, (IntSyn.dot1 s))))
      | (All (__d, g), s) ->
          All ((IntSyn.decSub (__d, s)), (goalSub (g, (IntSyn.dot1 s))))
    let rec resGoalSub =
      function
      | (Eq q, s) -> Eq (IntSyn.EClo (q, s))
      | (And (r, A, g), s) ->
          And
            ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (A, s)),
              (goalSub (g, s)))
      | (In (r, A, g), s) ->
          In
            ((resGoalSub (r, (IntSyn.dot1 s))), (IntSyn.EClo (A, s)),
              (goalSub (g, s)))
      | (Exists (__d, r), s) ->
          Exists ((IntSyn.decSub (__d, s)), (resGoalSub (r, (IntSyn.dot1 s))))
    let rec pskeletonToString =
      function
      | [] -> " "
      | (Pc i)::O ->
          ((Names.qidToString (Names.constQid i)) ^ " ") ^
            (pskeletonToString O)
      | (Dc i)::O ->
          (("(Dc " ^ (Int.toString i)) ^ ") ") ^ (pskeletonToString O)
      | (Csolver (__u))::O -> "(cs _ ) " ^ (pskeletonToString O)
  end  (* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Brigitte Pientka *)
(*! structure IntSyn' : INTSYN !*)
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure IntSyn = IntSyn' !*)
(* Goals                      *)
(* g ::= p                    *)
(*     | (r,A,a) => g         *)
(*     | all x:A. g           *)
(* Residual Goals             *)
(* r ::= p = ?                *)
(*     | p = ?, where p has   *)
(* only new vars,             *)
(* then unify all the vars    *)
(*     | r & (A,g)            *)
(*     | r && (A,g)           *)
(*     | exists x:A. r        *)
(*     | exists' x:_. r       *)
(* exists' is used for local evars
                                           which are introduced to linearize
                                           the head of a clause;
                                           they do not have a type -bp *)
(* trivially done *) (* call unify *)
(* Static programs -- compiled version for substitution trees *)
(* proof skeletons instead of proof term *)
(* Representation invariants for compiled syntax:
     Judgments:
       __g |- g goal   g is a valid goal in __g
       __g |- r resgoal  g is a valid residual goal in __g

       __g |- A ~> g   A compiles to goal g
       __g |- A ~> r   A compiles to residual goal r
       __g |- A ~> <head , subgoals>

     __g |- p  goal
     if  __g |- p : type, p = H @ S        mod whnf *)
(* mod whnf *)
(* Static programs --- compiled version of the signature (no indexing) *)
(* Compiled constant declaration           *)
(* c : A  -- static clause (residual goal) *)
(* Other declarations are ignored          *)
(* Static programs --- compiled version of the signature (indexed by first argument) *)
(* Compiled constant declaration     *)
(* static clause with direct head access   *)
(* Other declarations are ignored          *)
(* Compiled Declarations *)
(* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
(* The dynamic clause pool --- compiled version of the context *)
(* Dynamic programs: context with synchronous clause pool *)
(* program array indexed by clause names (no direct head access) *)
(* Invariants *)
(* 0 <= cid < I.sgnSize () *)
(* program array indexed by clause names (no direct head access) *)
(* goalSub (g, s) = g'

     Invariants:
     If   __g  |- s : __g'    __g' |- g : A
     then g' = g[s]
     and  __g  |- g' : A
  *)
(* resGoalSub (r, s) = r'

     Invariants:
     If   __g  |- s : __g'    __g' |- r : A
     then r' = r[s]
     and  __g  |- r' : A [s]
  *)
(* functor CompSyn *)
module CompSyn =
  (Make_CompSyn)(struct
                   module Global = Global
                   (*! structure IntSyn' = IntSyn !*)
                   module Names = Names
                   module Table = IntRedBlackTree
                 end);;
