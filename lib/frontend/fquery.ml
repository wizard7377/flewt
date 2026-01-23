module type FQUERY  =
  sig
    module ExtQuery : EXTQUERY
    exception AbortQuery of string 
    val run : (ExtQuery.query * Paths.location) -> unit
  end


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
    let rec evarInstToString (xs_) =
      if !Global.chatter >= 3 then begin Print.evarInstToString xs_ end
      else begin "" end
  let rec expToString (GU) =
    if !Global.chatter >= 3 then begin Print.expToString GU end
    else begin "" end
let rec lower =
  begin function
  | (0, g_, v_) -> (g_, v_)
  | (n, g_, Pi ((d_, _), v_)) -> lower ((n - 1), (I.Decl (g_, d_)), v_) end
let rec run (quy, Loc (fileName, r)) =
  let (v_, optName, xs_) =
    ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r))) in
  let _ = if !Global.chatter >= 3 then begin print "%fquery" end
    else begin () end in
let _ = if !Global.chatter >= 3 then begin print " " end else begin () end in
let _ =
  if !Global.chatter >= 3
  then
    begin print
            ((Timers.time Timers.printing expToString (IntSyn.Null, v_)) ^
               ".\n") end
  else begin () end in
let (k, v1_) = Abstract.abstractDecImp v_ in
let (g_, v2_) = lower (k, I.Null, v1_) in
let a = I.targetFam v2_ in
let w_ = W.lookup a in
let v3_ = Worldify.worldifyGoal (g_, v2_) in
let _ = TypeCheck.typeCheck (g_, (v3_, (I.Uni I.Type))) in
let p_ = Converter.convertGoal ((T.embedCtx g_), v3_) in
let v_ = Timers.time Timers.delphin Opsem.evalPrg p_ in
((print (((^) "Delphin: " TomegaPrint.prgToString (I.Null, v_)) ^ "\n"))
(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
(* times itself *)(* G |- V'' : type *))
end
