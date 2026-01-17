
module type TABLEPARAM  =
  sig
    exception Error of
      ((string)(*! structure RBSet : RBSET !*)(*! structure CompSyn : COMPSYN !*)
      (*! structure IntSyn : INTSYN !*)(* Author: Brigitte Pientka *)
      (* Global Table parameters *)) 
    type __ResEqn =
      | Trivial 
      | Unify of
      (((IntSyn.dctx)(* trivially done *)(* Residual equation *))
      * IntSyn.__Exp * ((IntSyn.__Exp)(* call unify *)) *
      __ResEqn) 
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
      (((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) * answer) ->
        ((unit)(* destructively updates answers *))
    val updateAnswLookup : (int * answer) -> unit
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list
    val lookup : answer -> int
    val noAnswers : answer -> bool
    type nonrec asub =
      ((IntSyn.__Exp)(* ---------------------------------------------------------------------- *))
        RBSet.ordSet
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
      | Subsumption (* ---------------------------------------------------------------------- *)
    val strategy : __Strategy ref
    val stageCtr : int ref
    val divHeuristic : bool ref
    val termDepth : int option ref
    val ctxDepth : int option ref
    val ctxLength : int option ref
    val strengthen : bool ref
  end;;




module TableParam(TableParam:sig
                               module Global :
                               ((GLOBAL)(* Table parameters *)(* Author: Brigitte Pientka *))
                             end) : TABLEPARAM =
  struct
    exception Error of
      ((string)(*! structure RBSet = RBSet !*)(*! structure CompSyn = CompSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure RBSet : RBSET!*)
      (*!  sharing CompSyn'.IntSyn = IntSyn'!*)(*! structure CompSyn' : COMPSYN !*)
      (*! structure IntSyn' : INTSYN !*)) 
    type __Strategy =
      | Variant 
      | Subsumption 
    type __ResEqn =
      | Trivial 
      | Unify of (((IntSyn.dctx)(* trivially done *)) *
      IntSyn.__Exp * ((IntSyn.__Exp)(* call unify *)) *
      __ResEqn) 
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type __Status =
      | Complete 
      | Incomplete 
    let (globalTable :
      (((IntSyn.dctx)(* globalTable stores the queries whose solution we want to keep *))
        * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * __ResEqn * answer *
        __Status) list ref)
      = ref []
    let rec resetGlobalTable () = globalTable := []
    let rec emptyAnsw () = ref { solutions = []; lookup = 0 }
    let rec addSolution (S, answRef) =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = (S :: SList); lookup = k }
    let rec updateAnswLookup (k', answRef) =
      let { solutions = SList; lookup = k; lookup = k } = !answRef in
      answRef := { solutions = SList; lookup = k' }
    let rec solutions (ref { solutions = S; lookup = i; lookup = i } as answ)
      = S
    let rec lookup (ref { solutions = S; lookup = i; lookup = i } as answ) =
      i
    let rec noAnswers answ =
      match List.take ((solutions answ), (lookup answ)) with
      | [] -> ((true__)(*solutions(answ) *))
      | L -> false__
    type nonrec asub = IntSyn.__Exp RBSet.ordSet
    let (aid : unit -> asub) = RBSet.new__
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.__Sub * IntSyn.__Sub) * answer * __Status)
      
      | DivergingEntry of (IntSyn.__Sub * answer) 
    type answState =
      | new__ [@sml.renamed "new__"][@sml.renamed "new__"]
      | repeated [@sml.renamed "repeated"][@sml.renamed "repeated"]
    let ((strategy)(* ---------------------------------------------------------------------- *)
      (* global search parameters *)) = ref Variant
    let ((divHeuristic)(* Subsumption *)) = ref false__
    let ((stageCtr)(*  val divHeuristic = ref true;*)) =
      ref 0
    let ((termDepth)(* term abstraction and ctx abstraction *)(* currently not used *))
      = (ref NONE : int option ref)
    let ctxDepth = (ref NONE : int option ref)
    let ctxLength = (ref NONE : int option ref)
    let ((strengthen)(* apply strengthening during abstraction *))
      = ref false__
  end ;;




module TableParam = (Make_TableParam)(struct module Global = Global end);;
