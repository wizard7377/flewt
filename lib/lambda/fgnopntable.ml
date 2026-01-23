module FgnOpnTable(FgnOpnTable:sig type nonrec arg type nonrec result end) :
  FGN_OPN =
  struct
    type nonrec csid = int
    type nonrec rep = exn
    type nonrec arg = arg
    type nonrec result = result
    type nonrec func = rep -> arg -> result
    type nonrec table = func array
    let rec initializeTable tbl =
      let exception CSfunNotInstalled of csid  in
        let maxCSid = 50 in
        let rec unimplemented csid =
          begin function | _ -> raise (CSfunNotInstalled csid) end in
        ((Array.tabulate ((maxCSid + 1), unimplemented))
          (*Global.maxCSid*))
    let (table : table) = initializeTable ()
    let rec install (csid, f) = Array.update (table, csid, f)
    let rec apply (csid, rep) = Array.sub (table, csid) rep end 