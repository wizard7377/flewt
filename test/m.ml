
module F = FunSyn module I = IntSyn module S = StateSyn
let rec load file =
  match Twelf.Config.load (Twelf.Config.read file) with
  | Twelf.OK -> Twelf.OK
  | Twelf.ABORT -> raise Domain
let rec transformOrder' =
  function
  | (G, Arg k) ->
      let k' = ((I.ctxLength G) - k) + 1 in
      let Dec (_, V) = I.ctxDec (G, k') in
      S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (V, I.id))
  | (G, Lex (Os)) -> S.Lex (map (function | O -> transformOrder' (G, O)) Os)
  | (G, Simul (Os)) ->
      S.Simul (map (function | O -> transformOrder' (G, O)) Os)
let rec transformOrder =
  function
  | (G, All (Prim (D), F), Os) ->
      S.All (D, (transformOrder ((I.Decl (G, D)), F, Os)))
  | (G, And (F1, F2), (O)::Os) ->
      S.And ((transformOrder (G, F1, [O])), (transformOrder (G, F2, Os)))
  | (G, Ex _, (O)::[]) -> transformOrder' (G, O)
let rec select c = try Order.selLookup c with | _ -> Order.Lex []
let rec test (depth, names) =
  let a = map (function | x -> valOf (Names.nameLookup x)) names in
  let name = foldr (^) "" names in
  let _ = Names.varReset () in
  let F = RelFun.convertFor a in
  let Os = map select a in
  let _ = Twelf.chatter := 5 in
  let _ = MTPi.reset () in
  let _ = MTPi.init (depth, (F, (transformOrder (I.Null, F, Os)))) in
  let _ = raise Domain in
  let _ = MTPi.auto () in let _ = Twelf.chatter := 3 in ()
(* just for non-inductive types *)
let _ = Twelf.chatter := 3 let _ = FunNames.reset ()
(*
   Regression test for Mini-ML *)
(*  val _ = test ["tps"] *)
(* Regression test for compile *)
let _ = load "examples/arith/test.cfg" let _ = test (3, ["assoc"]);;
