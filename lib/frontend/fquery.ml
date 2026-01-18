
(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)
module type FQUERY  =
  sig
    module ExtQuery : EXTQUERY
    exception AbortQuery of string 
    val run : (ExtQuery.query * Paths.location) -> unit
  end;;




(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)
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
    (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec evarInstToString (Xs) =
      if (!Global.chatter) >= 3 then Print.evarInstToString Xs else ""
    (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec expToString (GU) =
      if (!Global.chatter) >= 3 then Print.expToString GU else ""
    let rec lower =
      function
      | (0, G, V) -> (G, V)
      | (n, G, Pi ((D, _), V)) -> lower ((n - 1), (I.Decl (G, D)), V)
    let rec run (quy, Loc (fileName, r)) =
      let (V, optName, Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 3 then print "%fquery" else () in
      let _ = if (!Global.chatter) >= 3 then print " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing expToString (IntSyn.Null, V)) ^
               ".\n")
        else () in
      let (k, V1) = Abstract.abstractDecImp V in
      let (G, V2) = lower (k, I.Null, V1) in
      let a = I.targetFam V2 in
      let W = W.lookup a in
      let V3 = Worldify.worldifyGoal (G, V2) in
      let _ = TypeCheck.typeCheck (G, (V3, (I.Uni I.Type))) in
      let P = Converter.convertGoal ((T.embedCtx G), V3) in
      let V = Timers.time Timers.delphin Opsem.evalPrg P in
      ((print (((^) "Delphin: " TomegaPrint.prgToString (I.Null, V)) ^ "\n"))
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        (* times itself *)(* G |- V'' : type *))
  end ;;
