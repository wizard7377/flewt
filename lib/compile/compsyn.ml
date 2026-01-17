
module type COMPSYN  =
  sig
    type __Opt =
      | No 
      | LinearHeads 
      | Indexing (*! structure IntSyn : INTSYN !*)(* Modified: Jeff Polakow *)
    (* Author: Iliano Cervesato *)(* Compiled Syntax *)
    val optimize : __Opt ref
    type __Goal =
      | Atom of
      ((IntSyn.__Exp)(* Goals                      *)) 
      | Impl of
      (((__ResGoal)(* g ::= p                    *)) *
      IntSyn.__Exp *
      ((IntSyn.__Head)(*     | (r,A,a) => g         *)) *
      __Goal) 
      | All of (IntSyn.__Dec * __Goal) 
    and __ResGoal =
      | Eq of
      ((IntSyn.__Exp)(* Residual Goals             *)
      (* dynamic clauses *)(*     | all x:A. g           *))
      
      | Assign of
      (((IntSyn.__Exp)(* r ::= p = ?                *)) *
      __AuxGoal) 
      | And of
      (((__ResGoal)(* then unify all the vars    *)(* only new vars,             *)
      (*     | p = ?, where p has   *)) *
      ((IntSyn.__Exp)(*     | r & (A,g)            *)) *
      __Goal) 
      | In of (__ResGoal *
      ((IntSyn.__Exp)(*     | r virt& (A,g)        *)) *
      __Goal) 
      | Exists of (IntSyn.__Dec * __ResGoal) 
      | Axists of
      (((IntSyn.__Dec)(*     | exists x:A. r        *)) *
      __ResGoal) 
    and __AuxGoal =
      | Trivial 
      | UnifyEq of
      (((IntSyn.dctx)(* trivially done *)(*     | exists x:_. r        *))
      * IntSyn.__Exp * ((IntSyn.__Exp)(* call unify *)) *
      __AuxGoal) 
    type __Conjunction =
      | True 
      | Conjunct of
      (((__Goal)(* Static programs -- compiled version for substitution trees *))
      * IntSyn.__Exp * __Conjunction) 
    type __CompHead =
      | Head of (IntSyn.__Exp * IntSyn.__Dec IntSyn.__Ctx * __AuxGoal *
      IntSyn.cid) 
    type __Flatterm =
      | Pc of ((int)(* pskeleton instead of proof term *)) 
      | Dc of int 
      | Csolver of IntSyn.__Exp 
    type nonrec pskeleton = __Flatterm list
    type __ComDec =
      | Parameter 
      | Dec of
      (((__ResGoal)(* added Thu Jun 13 13:41:32 EDT 2002 -cs *)(* Compiled Declarations *)
      (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)
      (* The dynamic clause pool --- compiled version of the context *))
      * IntSyn.__Sub * IntSyn.__Head) 
      | BDec of (__ResGoal * IntSyn.__Sub * IntSyn.__Head) list 
      | PDec 
    type __DProg =
      | DProg of
      (((IntSyn.dctx)(* Dynamic programs: context with synchronous clause pool *))
      * __ComDec IntSyn.__Ctx) 
    type __ConDec =
      | SClause of
      ((__ResGoal)(* Compiled constant declaration *)
      (* Programs --- compiled version of the signature (no direct head access) *))
      
      | Void 
    val sProgInstall :
      (IntSyn.cid * __ConDec) ->
        ((unit)(* Install Programs (without indexing) *)
        (* Other declarations are ignored  *)(* c : A  -- static clause (residual goal) *))
    val sProgLookup : IntSyn.cid -> __ConDec
    val sProgReset : unit -> unit
    val detTableInsert :
      (IntSyn.cid * bool) ->
        ((unit)(* Deterministic flag *))
    val detTableCheck : IntSyn.cid -> bool
    val detTableReset : unit -> unit
    val goalSub :
      (__Goal * IntSyn.__Sub) ->
        ((__Goal)(* Explicit Substitutions *))
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
      | SOME deterministic -> deterministic
      | NONE -> false__
    let rec detTableReset () = Table.clear detTable
    let rec goalSub =
      function
      | (Atom p, s) -> Atom (IntSyn.EClo (p, s))
      | (Impl (d, A, Ha, g), s) ->
          Impl
            ((resGoalSub (d, s)), (IntSyn.EClo (A, s)), Ha,
              (goalSub (g, (IntSyn.dot1 s))))
      | (All (D, g), s) ->
          All ((IntSyn.decSub (D, s)), (goalSub (g, (IntSyn.dot1 s))))
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
      | (Exists (D, r), s) ->
          Exists ((IntSyn.decSub (D, s)), (resGoalSub (r, (IntSyn.dot1 s))))
    let rec pskeletonToString =
      function
      | [] -> " "
      | (Pc i)::O ->
          ((Names.qidToString (Names.constQid i)) ^ " ") ^
            (pskeletonToString O)
      | (Dc i)::O ->
          (("(Dc " ^ (Int.toString i)) ^ ") ") ^ (pskeletonToString O)
      | (Csolver (U))::O -> "(cs _ ) " ^ (pskeletonToString O)
  end 
module CompSyn =
  (Make_CompSyn)(struct
                   module Global =
                     ((Global)(* Compiled Syntax *)(* Author: Iliano Cervesato *)
                     (* Modified: Jeff Polakow *)(* Modified: Frank Pfenning *)
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
                     (* trivially done *)(* call unify *)
                     (* Static programs -- compiled version for substitution trees *)
                     (* proof skeletons instead of proof term *)
                     (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r
       G |- A ~> <head , subgoals>

     G |- p  goal
     if  G |- p : type, p = H @ S        mod whnf *)
                     (* mod whnf *)(* Static programs --- compiled version of the signature (no indexing) *)
                     (* Compiled constant declaration           *)
                     (* c : A  -- static clause (residual goal) *)
                     (* Other declarations are ignored          *)
                     (* Static programs --- compiled version of the signature (indexed by first argument) *)
                     (* Compiled constant declaration     *)
                     (* static clause with direct head access   *)
                     (* Other declarations are ignored          *)
                     (* Compiled Declarations *)(* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
                     (* The dynamic clause pool --- compiled version of the context *)
                     (* Dynamic programs: context with synchronous clause pool *)
                     (* program array indexed by clause names (no direct head access) *)
                     (* Invariants *)(* 0 <= cid < I.sgnSize () *)
                     (* program array indexed by clause names (no direct head access) *)
                     (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
                     (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
                     (* functor CompSyn *))
                   module Names =
                     ((Names)(*! structure IntSyn' = IntSyn !*))
                   module Table = IntRedBlackTree
                 end);;
