
module type MEMOTABLE  =
  sig
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
        TableParam.__ResEqn * TableParam.__Status) ->
        ((TableParam.callCheckResult)(* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)
        (* call check/insert *)(*! structure TableParam : TABLEPARAM !*)
        (*! structure CompSyn : COMPSYN !*)(*! structure IntSyn : INTSYN !*)
        (* Author: Brigitte Pientka *)(* Indexing *))
    val insertIntoTree :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
        TableParam.__ResEqn * TableParam.answer * TableParam.__Status) ->
        TableParam.callCheckResult
    val answerCheck :
      (IntSyn.__Sub * TableParam.answer * CompSyn.pskeleton) ->
        ((TableParam.answState)(* answerCheck (G, D, (U,s))
   * 
   * Assupmtion: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
        (* answer check/insert *))
    val reset : unit -> ((unit)(* reset table *))
    val updateTable :
      unit ->
        ((bool)(* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *))
    val tableSize : unit -> int
    val memberCtx :
      ((IntSyn.dctx * IntSyn.__Exp) * IntSyn.dctx) -> IntSyn.__Dec option
  end;;




module SwMemoTable(SwMemoTable:sig
                                 module MemoTable : MEMOTABLE
                                 module MemoTableInst :
                                 ((MEMOTABLE)(* structure TableParam : TABLEPARAM *))
                               end) : MEMOTABLE =
  struct
    let rec callCheck
      ((args)(*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
      (*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)(*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
      (*! structure IntSyn = MemoTable.IntSyn !*)(*! structure CompSyn = MemoTable.CompSyn !*)
      (*! structure TableParam = MemoTable.TableParam !*)) =
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
