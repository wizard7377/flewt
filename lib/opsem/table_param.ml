
(* Global Table parameters *)
(* Author: Brigitte Pientka *)
module type TABLEPARAM  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    (*! structure RBSet : RBSET !*)
    exception Error of string 
    (* Residual equation *)
    type __ResEqn =
      | Trivial 
      | Unify of (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __ResEqn) 
    (* call unify *)
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
    (* destructively updates answers *)
    val addSolution :
      (((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) * answer) -> unit
    val updateAnswLookup : (int * answer) -> unit
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list
    val lookup : answer -> int
    val noAnswers : answer -> bool
    (* ---------------------------------------------------------------------- *)
    type nonrec asub = IntSyn.__Exp RBSet.ordSet
    val aid : unit -> asub
    type callCheckResult =
      | NewEntry of answer 
      | RepeatedEntry of ((IntSyn.__Sub * IntSyn.__Sub) * answer * __Status)
      
      | DivergingEntry of (IntSyn.__Sub * answer) 
    type answState =
      | new__ 
      | repeated 
    (* ---------------------------------------------------------------------- *)
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




(* Table parameters *)
(* Author: Brigitte Pientka *)
module TableParam(TableParam:sig module Global : GLOBAL end) : TABLEPARAM =
  struct
    (*! structure IntSyn' : INTSYN !*)
    (*! structure CompSyn' : COMPSYN !*)
    (*!  sharing CompSyn'.IntSyn = IntSyn'!*)
    (*! structure RBSet : RBSET!*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    (*! structure RBSet = RBSet !*)
    exception Error of string 
    type __Strategy =
      | Variant 
      | Subsumption 
    type __ResEqn =
      | Trivial 
      | Unify of (IntSyn.dctx * IntSyn.__Exp * IntSyn.__Exp * __ResEqn) 
    (* call unify *)
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   >  ref
    type __Status =
      | Complete 
      | Incomplete 
    (* globalTable stores the queries whose solution we want to keep *)
    let (globalTable :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * __ResEqn *
        answer * __Status) list ref)
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
      ((match List.take ((solutions answ), (lookup answ)) with
        | [] -> true__
        | L -> false__)
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
    (* ---------------------------------------------------------------------- *)
    (* global search parameters *)
    let strategy = ref Variant
    (* Subsumption *)
    let divHeuristic = ref false__
    (*  val divHeuristic = ref true;*)
    let stageCtr = ref 0
    (* term abstraction and ctx abstraction *)
    (* currently not used *)
    let termDepth = (ref NONE : int option ref)
    let ctxDepth = (ref NONE : int option ref)
    let ctxLength = (ref NONE : int option ref)
    (* apply strengthening during abstraction *)
    let strengthen = ref false__
  end ;;




module TableParam = (Make_TableParam)(struct module Global = Global end);;
