
(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module type STATE  =
  sig
    exception Error of string 
    type __State =
      | State of (Tomega.__Worlds * Tomegas.__Dec IntSyn.__Ctx * Tomega.__Prg
      * Tomega.__For) 
      | StateLF of IntSyn.__Exp 
    type __Focus =
      | Focus of (Tomega.__Prg * Tomega.__Worlds) 
      | FocusLF of IntSyn.__Exp 
    (* focus EVar *)
    val init : (Tomega.__For * Tomega.__Worlds) -> __State
    val close : __State -> bool
    val collectT : Tomega.__Prg -> Tomega.__Prg list
    val collectLF : Tomega.__Prg -> IntSyn.__Exp list
    val collectLFSub : Tomega.__Sub -> IntSyn.__Exp list
  end;;




(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module State(State:sig module Formatter : FORMATTER end) : STATE =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module Formatter = Formatter
    type __State =
      | State of (Tomega.__Worlds * Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg
      * Tomega.__For) 
      | StateLF of IntSyn.__Exp 
    (* StateLF x, x is always lowered *)
    type __Focus =
      | Focus of (Tomega.__Prg * Tomega.__Worlds) 
      | FocusLF of IntSyn.__Exp 
    (* datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds
 *)
    (*  datatype SideCondition   we need some work here *)
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    let rec findPrg =
      function
      | Lam (_, P) -> findPrg P
      | New (P) -> findPrg P
      | Choose (P) -> findPrg P
      | PairExp (_, P) -> findPrg P
      | PairBlock (B, P) -> findPrg P
      | PairPrg (__P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | T.Unit -> []
      | Rec (_, P) -> findPrg P
      | Case (Cases (C)) -> findCases C
      | PClo (P, t) -> (@) (findPrg P) findSub t
      | Let (__d, __P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | LetPairExp (D1, D2, __P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | LetUnit (__P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | EVar (_, ref (None), _, _, _, _) as x -> [x]
      | EVar (_, ref (Some (P)), _, _, _, _) as x -> findPrg P
      | Const _ -> []
      | Var _ -> []
      | Redex (P, S) -> (@) (findPrg P) findSpine S
    let rec findCases =
      function | nil -> [] | (_, _, P)::C -> (@) (findPrg P) findCases C
    let rec findSub =
      function | Shift _ -> [] | Dot (F, t) -> (@) (findFront F) findSub t
    let rec findFront =
      function
      | Idx _ -> []
      | Prg (P) -> findPrg P
      | Exp _ -> []
      | Block _ -> []
      | T.Undef -> []
    let rec findSpine =
      function
      | T.Nil -> []
      | AppPrg (P, S) -> (@) (findPrg P) findSpine S
      | AppExp (_, S) -> findSpine S
      | AppBlock (_, S) -> findSpine S
    let rec findExp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((Psi, Lam (__d, P)), K) -> findExp ((I.Decl (Psi, __d)), P) K
      | ((Psi, New (P)), K) -> findExp (Psi, P) K
      | ((Psi, Choose (P)), K) -> findExp (Psi, P) K
      | ((Psi, PairExp (M, P)), K) ->
          findExp (Psi, P)
            (Abstract.collectEVars ((T.coerceCtx Psi), (M, I.id), K))
      | ((Psi, PairBlock (B, P)), K) -> findExp (Psi, P) K
      | ((Psi, PairPrg (__P1, __P2)), K) ->
          findExp (Psi, __P2) (findExp (Psi, __P1) K)
      | ((Psi, T.Unit), K) -> K
      | ((Psi, Rec (__d, P)), K) -> findExp (Psi, P) K
      | ((Psi, Case (Cases (C))), K) -> findExpCases (Psi, C) K
      | ((Psi, PClo (P, t)), K) -> findExpSub (Psi, t) (findExp (Psi, P) K)
      | ((Psi, Let (__d, __P1, __P2)), K) ->
          findExp ((I.Decl (Psi, __d)), __P2) (findExp (Psi, __P1) K)
      | ((Psi, LetPairExp (D1, D2, __P1, __P2)), K) ->
          findExp ((I.Decl ((I.Decl (Psi, (T.UDec D1))), D2)), __P2)
            (findExp (Psi, __P1) K)
      | ((Psi, LetUnit (__P1, __P2)), K) ->
          findExp (Psi, __P2) (findExp (Psi, __P1) K)
      | ((Psi, (EVar _ as x)), K) -> K
      | ((Psi, Const _), K) -> K
      | ((Psi, Var _), K) -> K
      | ((Psi, Redex (P, S)), K) -> findExpSpine (Psi, S) K
    let rec findExpSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((Psi, T.Nil), K) -> K
      | ((Psi, AppPrg (_, S)), K) -> findExpSpine (Psi, S) K
      | ((Psi, AppExp (M, S)), K) ->
          findExpSpine (Psi, S)
            (Abstract.collectEVars ((T.coerceCtx Psi), (M, I.id), K))
      | ((Psi, AppBlock (_, S)), K) -> findExpSpine (Psi, S) K
    let rec findExpCases arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((Psi, nil), K) -> K
      | ((Psi, (_, _, P)::C), K) ->
          findExpCases (Psi, C) (findExp (Psi, P) K)
    let rec findExpSub arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((Psi, Shift _), K) -> K
      | ((Psi, Dot (F, t)), K) ->
          findExpSub (Psi, t) (findExpFront (Psi, F) K)
    let rec findExpFront arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((Psi, Idx _), K) -> K
      | ((Psi, Prg (P)), K) -> findExp (Psi, P) K
      | ((Psi, Exp (M)), K) ->
          Abstract.collectEVars ((T.coerceCtx Psi), (M, I.id), K)
      | ((Psi, Block _), K) -> K
      | ((Psi, T.Undef), K) -> K
    let rec init (F, W) =
      let x = T.newEVar (I.Null, F) in State (W, I.Null, x, F)
    let rec close (State (W, _, P, _)) =
      match ((findPrg P), (findExp (I.Null, P) [])) with
      | (nil, nil) -> true__
      | _ -> false__
    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    (* by invariant: blocks don't contain free evars *)
    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    (* by invariant: Blocks don't contain free evars. *)
    (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    (* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)
    let close = close
    let init = init
    let collectT = findPrg
    let collectLF = function | P -> findExp (I.Null, P) []
    let collectLFSub = function | s -> findExpSub (I.Null, s) []
  end ;;
