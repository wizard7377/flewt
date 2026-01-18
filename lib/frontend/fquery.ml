
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
    (* evarInstToString __Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec evarInstToString (__Xs) =
      if (!Global.chatter) >= 3 then Print.evarInstToString __Xs else ""
    (* expToString (__g, __u) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
    let rec expToString (GU) =
      if (!Global.chatter) >= 3 then Print.expToString GU else ""
    let rec lower =
      function
      | (0, __g, __v) -> (__g, __v)
      | (n, __g, Pi ((__d, _), __v)) -> lower ((n - 1), (I.Decl (__g, __d)), __v)
    let rec run (quy, Loc (fileName, r)) =
      let (__v, optName, __Xs) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
      let _ = if (!Global.chatter) >= 3 then print "%fquery" else () in
      let _ = if (!Global.chatter) >= 3 then print " " else () in
      let _ =
        if (!Global.chatter) >= 3
        then
          print
            ((Timers.time Timers.printing expToString (IntSyn.Null, __v)) ^
               ".\n")
        else () in
      let (k, V1) = Abstract.abstractDecImp __v in
      let (__g, V2) = lower (k, I.Null, V1) in
      let a = I.targetFam V2 in
      let W = W.lookup a in
      let V3 = Worldify.worldifyGoal (__g, V2) in
      let _ = TypeCheck.typeCheck (__g, (V3, (I.Uni I.Type))) in
      let P = Converter.convertGoal ((T.embedCtx __g), V3) in
      let __v = Timers.time Timers.delphin Opsem.evalPrg P in
      ((print (((^) "Delphin: " TomegaPrint.prgToString (I.Null, __v)) ^ "\n"))
        (* optName = Some(x) or None, __Xs = free variables in query excluding x *)
        (* times itself *)(* __g |- __v'' : type *))
  end ;;
