module type MEMOTABLE  =
  sig
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ *
        TableParam.resEqn_ * TableParam.status_) ->
        TableParam.callCheckResult
    val insertIntoTree :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ *
        TableParam.resEqn_ * TableParam.answer * TableParam.status_) ->
        TableParam.callCheckResult
    val answerCheck :
      (IntSyn.sub_ * TableParam.answer * CompSyn.pskeleton) ->
        TableParam.answState
    val reset : unit -> unit
    val updateTable : unit -> bool
    val tableSize : unit -> int
    val memberCtx :
      ((IntSyn.dctx * IntSyn.exp_) * IntSyn.dctx) -> IntSyn.dec_ option
  end


module SwMemoTable(SwMemoTable:sig
                                 module MemoTable : MEMOTABLE
                                 module MemoTableInst : MEMOTABLE
                               end) : MEMOTABLE =
  struct
    let rec callCheck args =
      begin match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.callCheck args
      | TableParam.Subsumption -> MemoTableInst.callCheck args end
    let rec insertIntoTree args =
      begin match !TableParam.strategy with
      | TableParam.Variant -> MemoTable.insertIntoTree args
      | TableParam.Subsumption -> MemoTableInst.insertIntoTree args end
  let rec answerCheck args =
    begin match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.answerCheck args
    | TableParam.Subsumption -> MemoTableInst.answerCheck args end
let rec reset () =
  begin match !TableParam.strategy with
  | TableParam.Variant -> MemoTable.reset ()
  | TableParam.Subsumption -> MemoTableInst.reset () end
let rec updateTable () =
  begin match !TableParam.strategy with
  | TableParam.Variant -> MemoTable.updateTable ()
  | TableParam.Subsumption -> MemoTableInst.updateTable () end
let rec tableSize () =
  begin match !TableParam.strategy with
  | TableParam.Variant -> MemoTable.tableSize ()
  | TableParam.Subsumption -> MemoTableInst.tableSize () end
let rec memberCtx args =
  begin match !TableParam.strategy with
  | TableParam.Subsumption -> MemoTableInst.memberCtx args
  | TableParam.Variant -> MemoTable.memberCtx args end end
