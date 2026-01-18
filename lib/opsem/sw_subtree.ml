
(* Indexing *)
(* Author: Brigitte Pientka *)
module type MEMOTABLE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    (*! structure TableParam : TABLEPARAM !*)
    (* call check/insert *)
    (* callCheck (__g, __d, __u, eqn)
   *
   * if __d, __g |- __u & eqn     in table  then RepeatedEntry (entries)
   * if __d, __g |- __u & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: __d, __g |- __u added to table
   *)
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
        TableParam.__ResEqn * TableParam.__Status) ->
        TableParam.callCheckResult
    val insertIntoTree :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
        TableParam.__ResEqn * TableParam.answer * TableParam.__Status) ->
        TableParam.callCheckResult
    (* answer check/insert *)
    (* answerCheck (__g, __d, (__u,s))
   * 
   * Assupmtion: __d, __g |- __u is in table
   *             and A represents the corresponding solutions
   * 
   * __g |- s : __d, __g
   * Dk, __g |- sk : __d, __g
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
    val answerCheck :
      (IntSyn.__Sub * TableParam.answer * CompSyn.pskeleton) ->
        TableParam.answState
    (* reset table *)
    val reset : unit -> unit
    (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
    val updateTable : unit -> bool
    val tableSize : unit -> int
    val memberCtx :
      ((IntSyn.dctx * IntSyn.__Exp) * IntSyn.dctx) -> IntSyn.__Dec option
  end;;




module SwMemoTable(SwMemoTable:sig
                                 (* structure TableParam : TABLEPARAM *)
                                 module MemoTable : MEMOTABLE
                                 module MemoTableInst : MEMOTABLE
                               end) : MEMOTABLE =
  struct
    (*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
    (*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
    (*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
    (*! structure IntSyn = MemoTable.IntSyn !*)
    (*! structure CompSyn = MemoTable.CompSyn !*)
    (*! structure TableParam = MemoTable.TableParam !*)
    let rec callCheck args =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.callCheck args
      | TableParam.Subsumption -> MemoTableInst.callCheck args
    let rec insertIntoTree args =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.insertIntoTree args
      | TableParam.Subsumption -> MemoTableInst.insertIntoTree args
    let rec answerCheck args =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.answerCheck args
      | TableParam.Subsumption -> MemoTableInst.answerCheck args
    let rec reset () =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.reset ()
      | TableParam.Subsumption -> MemoTableInst.reset ()
    let rec updateTable () =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.updateTable ()
      | TableParam.Subsumption -> MemoTableInst.updateTable ()
    let rec tableSize () =
      match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.tableSize ()
      | TableParam.Subsumption -> MemoTableInst.tableSize ()
    let rec memberCtx args =
      match !TableParam.strategy with
      | TableParam.Subsumption -> MemoTableInst.memberCtx args
      | TableParam.Variant -> MemoTable.memberCtx args
  end ;;
