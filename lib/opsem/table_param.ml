module type TABLEPARAM  =
  sig
    exception Error of string 
    type resEqn_ =
      | Trivial 
      | Unify of
      (((IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * resEqn_))(* call unify *))
      
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type status_ =
      | Complete 
      | Incomplete 
    val globalTable :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ * resEqn_ *
        answer * status_) list ref
    val resetGlobalTable : unit -> unit
    val emptyAnsw : unit -> answer
    val addSolution :
      (((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) * answer) -> unit
    val updateAnswLookup : (int * answer) -> unit
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list
    val lookup : answer -> int
    val noAnswers : answer -> bool
    type nonrec asub = IntSyn.exp_ RBSet.ordSet
    val aid : unit -> asub
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.sub_ * IntSyn.sub_) * answer * status_) 
      | DivergingEntry of (IntSyn.sub_ * answer) 
    type answState =
      | new_ 
      | repeated 
    type strategy_ =
      | Variant 
      | Subsumption 
    val strategy : strategy_ ref
    val stageCtr : int ref
    val divHeuristic : bool ref
    val termDepth : int option ref
    val ctxDepth : int option ref
    val ctxLength : int option ref
    val strengthen : bool ref
  end


module TableParam(TableParam:sig module Global : GLOBAL end) : TABLEPARAM =
  struct
    exception Error of string 
    type strategy_ =
      | Variant 
      | Subsumption 
    type resEqn_ =
      | Trivial 
      | Unify of
      (((IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * resEqn_))(* call unify *))
      
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type status_ =
      | Complete 
      | Incomplete 
    let (globalTable :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ * resEqn_ *
        answer * status_) list ref)
      = ref []
    let rec resetGlobalTable () = globalTable := []
    let rec emptyAnsw () = ref { solutions = []; lookup = 0 }
    let rec addSolution (s_, answRef) =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = (s_ :: SList); lookup = k }
    let rec updateAnswLookup (k', answRef) =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = SList; lookup = k' }
    let rec solutions
      ({ contents = { solutions = s_; lookup = i; lookup = i } } as answ) =
      s_
    let rec lookup
      ({ contents = { solutions = s_; lookup = i; lookup = i } } as answ) = i
    let rec noAnswers answ =
      ((begin match List.take ((solutions answ), (lookup answ)) with
        | [] -> true
        | l_ -> false end)
      (*solutions(answ) *))
    type nonrec asub = IntSyn.exp_ RBSet.ordSet
    let (aid : unit -> asub) = RBSet.new_
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.sub_ * IntSyn.sub_) * answer * status_) 
      | DivergingEntry of (IntSyn.sub_ * answer) 
    type answState =
      | new_ [@sml.renamed "new_"][@sml.renamed "new_"]
      | repeated [@sml.renamed "repeated"][@sml.renamed "repeated"]
    let strategy = ref Variant
    let divHeuristic = ref false
    let stageCtr = ref 0
    let termDepth = (ref None : int option ref)
    let ctxDepth = (ref None : int option ref)
    let ctxLength = (ref None : int option ref)
    let strengthen = ref false end 


module TableParam = (TableParam)(struct module Global = Global end)