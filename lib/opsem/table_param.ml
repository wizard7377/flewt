
module type TABLEPARAM  =
  sig
    exception Error of string 
    type __ResEqn =
      | Trivial 
      | Unify of
      (((IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __ResEqn))(* call unify *))
      
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type __Status =
      | Complete 
      | Incomplete 
    val globalTable :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * __ResEqn *
        answer * __Status) list ref
    val resetGlobalTable : unit -> unit
    val emptyAnsw : unit -> answer
    val addSolution :
      ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) -> answer -> unit
    val updateAnswLookup : int -> answer -> unit
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list
    val lookup : answer -> int
    val noAnswers : answer -> bool
    type nonrec asub = IntSyn.__Exp RBSet.ordSet
    val aid : unit -> asub
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.__Sub * IntSyn.__Sub) * answer * __Status)
      
      | DivergingEntry of (IntSyn.__Sub * answer) 
    type answState =
      | new__ 
      | repeated 
    type __Strategy =
      | Variant 
      | Subsumption 
    val strategy : __Strategy ref
    val stageCtr : int ref
    val divHeuristic : bool ref
    val termDepth : int option ref
    val ctxDepth : int option ref
    val ctxLength : int option ref
    val strengthen : bool ref
  end;;




module TableParam(TableParam:sig module Global : GLOBAL end) : TABLEPARAM =
  struct
    exception Error of string 
    type __Strategy =
      | Variant 
      | Subsumption 
    type __ResEqn =
      | Trivial 
      | Unify of
      (((IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __ResEqn))(* call unify *))
      
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type __Status =
      | Complete 
      | Incomplete 
    let (globalTable :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * __ResEqn *
        answer * __Status) list ref)
      = ref []
    let rec resetGlobalTable () = globalTable := []
    let rec emptyAnsw () = ref { solutions = []; lookup = 0 }
    let rec addSolution (__S) answRef =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = (__S :: SList); lookup = k }
    let rec updateAnswLookup k' answRef =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = SList; lookup = k' }
    let rec solutions
      ({ contents = { solutions = __S; lookup = i; lookup = i } } as answ) =
      __S
    let rec lookup
      ({ contents = { solutions = __S; lookup = i; lookup = i } } as answ) =
      i
    let rec noAnswers answ =
      ((match List.take ((solutions answ), (lookup answ)) with
        | [] -> true__
        | __L -> false__)
      (*solutions(answ) *))
    type nonrec asub = IntSyn.__Exp RBSet.ordSet
    let (aid : unit -> asub) = RBSet.new__
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.__Sub * IntSyn.__Sub) * answer * __Status)
      
      | DivergingEntry of (IntSyn.__Sub * answer) 
    type answState =
      | new__ [@sml.renamed "new__"][@sml.renamed "new__"]
      | repeated [@sml.renamed "repeated"][@sml.renamed "repeated"]
    let strategy = ref Variant
    let divHeuristic = ref false__
    let stageCtr = ref 0
    let termDepth = (ref NONE : int option ref)
    let ctxDepth = (ref NONE : int option ref)
    let ctxLength = (ref NONE : int option ref)
    let strengthen = ref false__
  end ;;




module TableParam = (Make_TableParam)(struct module Global = Global end);;
