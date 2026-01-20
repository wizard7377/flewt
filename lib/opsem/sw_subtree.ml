
module type MEMOTABLE  =
  sig
    val callCheck :
      IntSyn.dctx ->
        IntSyn.dctx ->
          IntSyn.dctx ->
            IntSyn.__Exp ->
              TableParam.__ResEqn ->
                TableParam.__Status -> TableParam.callCheckResult
    val insertIntoTree :
      IntSyn.dctx ->
        IntSyn.dctx ->
          IntSyn.dctx ->
            IntSyn.__Exp ->
              TableParam.__ResEqn ->
                TableParam.answer ->
                  TableParam.__Status -> TableParam.callCheckResult
    val answerCheck :
      IntSyn.__Sub ->
        TableParam.answer -> CompSyn.pskeleton -> TableParam.answState
    val reset : unit -> unit
    val updateTable : unit -> bool
    val tableSize : unit -> int
    val memberCtx :
      (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.dctx -> IntSyn.__Dec option
  end;;




module SwMemoTable(SwMemoTable:sig
                                 module MemoTable : MEMOTABLE
                                 module MemoTableInst : MEMOTABLE
                               end) : MEMOTABLE =
  struct
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
