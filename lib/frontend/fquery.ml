
module type FQUERY  =
  sig
    module ExtQuery : EXTQUERY
    exception AbortQuery of string 
    val run : ExtQuery.query -> Paths.location -> unit
  end;;




module Fquery(Fquery:sig
                       module Global : GLOBAL
                       module Names : NAMES
                       module ReconQuery : RECON_QUERY
                       module Timers : TIMERS
                       module Print : PRINT
                     end) : FQUERY =
  struct
    module ExtQuery = ReconQuery
    exception AbortQuery of string 
    module I = IntSyn
    module T = Tomega
    module W = WorldSyn
    module P = Paths
    let rec evarInstToString (__Xs) =
      if (!Global.chatter) >= 3 then Print.evarInstToString __Xs else ""
    let rec expToString (GU) =
      if (!Global.chatter) >= 3 then Print.expToString GU else ""
    let rec lower __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (0, __G, __V) -> (__G, __V)
      | (n, __G, Pi ((__D, _), __V)) ->
          lower ((n - 1), (I.Decl (__G, __D)), __V)
    let rec run quy (Loc (fileName, r)) =
      let (__V, optName, __Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 3 then print "%fquery" else () in
      let _ = if (!Global.chatter) >= 3 then print " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing expToString (IntSyn.Null, __V)) ^
               ".\n")
        else () in
      let (k, __V1) = Abstract.abstractDecImp __V in
      let (__G, __V2) = lower (k, I.Null, __V1) in
      let a = I.targetFam __V2 in
      let __W = W.lookup a in
      let __V3 = Worldify.worldifyGoal (__G, __V2) in
      let _ = TypeCheck.typeCheck (__G, (__V3, (I.Uni I.Type))) in
      let __P = Converter.convertGoal ((T.embedCtx __G), __V3) in
      let __V = Timers.time Timers.delphin Opsem.evalPrg __P in
      ((print
          (((^) "Delphin: " TomegaPrint.prgToString (I.Null, __V)) ^ "\n"))
        (* optName = Some(X) or None, Xs = free variables in query excluding X *)
        (* times itself *)(* G |- V'' : type *))
  end ;;
