
module F = FunSyn module I = IntSyn module S = StateSyn
let rec load file =
  match Twelf.Config.load (Twelf.Config.read file) with
  | Twelf.OK -> Twelf.OK
  | Twelf.ABORT -> raise Domain
let rec transformOrder' =
  function
  | (__g, Arg k) ->
      let k' = ((I.ctxLength __g) - k) + 1 in
      let Dec (_, __v) = I.ctxDec (__g, k') in
      S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__v, I.id))
  | (__g, Lex (__Os)) -> S.Lex (map (function | O -> transformOrder' (__g, O)) __Os)
  | (__g, Simul (__Os)) ->
      S.Simul (map (function | O -> transformOrder' (__g, O)) __Os)
let rec transformOrder =
  function
  | (__g, All (Prim (__d), F), __Os) ->
      S.All (__d, (transformOrder ((I.Decl (__g, __d)), F, __Os)))
  | (__g, And (__F1, __F2), (O)::__Os) ->
      S.And ((transformOrder (__g, __F1, [O])), (transformOrder (__g, __F2, __Os)))
  | (__g, Ex _, (O)::[]) -> transformOrder' (__g, O)
let rec select c = try Order.selLookup c with | _ -> Order.Lex []
let rec test (depth, names) =
  let a = map (function | x -> valOf (Names.nameLookup x)) names in
  let name = foldr (^) "" names in
  let _ = Names.varReset () in
  let F = RelFun.convertFor a in
  let __Os = map select a in
  let _ = Twelf.chatter := 5 in
  let _ = MTPi.reset () in
  let _ = MTPi.init (depth, (F, (transformOrder (I.Null, F, __Os)))) in
  let _ = raise Domain in
  let _ = MTPi.auto () in let _ = Twelf.chatter := 3 in ()
(* just for non-inductive types *)
let _ = Twelf.chatter := 3 let _ = FunNames.reset ()
(*
   Regression test for Mini-ML *)
(*  val _ = test ["tps"] *)
(* Regression test for compile *)
let _ = load "examples/arith/test.cfg" let _ = test (3, ["assoc"]);;
