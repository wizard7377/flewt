
module type FQUERY  =
  sig
    module ExtQuery :
    ((EXTQUERY)(* fquery: Executing logic programs via functional interpretation *)
    (* Author: Carsten Schuermann *))
    exception AbortQuery of string 
    val run : (ExtQuery.query * Paths.location) -> unit
  end;;




module Fquery(Fquery:sig
                       module Global : GLOBAL
                       module Names : NAMES
                       module ReconQuery : RECON_QUERY
                       module Timers : TIMERS
                       module Print :
                       ((PRINT)(* fquery: Executing logic programs via functional interpretation *)
                       (* Author: Carsten Schuermann *))
                     end) : FQUERY =
  struct
    module ExtQuery = ReconQuery
    exception AbortQuery of string 
    module I = IntSyn
    module T = Tomega
    module W = WorldSyn
    module P = Paths
    let rec evarInstToString
      ((Xs)(* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *))
      = if (!Global.chatter) >= 3 then Print.evarInstToString Xs else ""
    let rec expToString
      ((GU)(* expToString (g, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *))
      = if (!Global.chatter) >= 3 then Print.expToString GU else ""
    let rec lower =
      function
      | (0, g, V) -> (g, V)
      | (n, g, Pi ((D, _), V)) -> lower ((n - 1), (I.Decl (g, D)), V)
    let rec run (quy, Loc (fileName, r)) =
      let (((V)(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)),
           optName, Xs)
        = ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let ((_)(* times itself *)) =
        if (!Global.chatter) >= 3 then print "%fquery" else () in
      let _ = if (!Global.chatter) >= 3 then print " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing expToString (IntSyn.Null, V)) ^
               ".\n")
        else () in
      let (k, V1) = Abstract.abstractDecImp V in
      let (g, V2) = lower (k, I.Null, V1) in
      let ((a)(* g |- V'' : type *)) = I.targetFam V2 in
      let W = W.lookup a in
      let V3 = Worldify.worldifyGoal (g, V2) in
      let _ = TypeCheck.typeCheck (g, (V3, (I.Uni I.Type))) in
      let P = Converter.convertGoal ((T.embedCtx g), V3) in
      let V = Timers.time Timers.delphin Opsem.evalPrg P in
      print (((^) "Delphin: " TomegaPrint.prgToString (I.Null, V)) ^ "\n")
  end ;;
