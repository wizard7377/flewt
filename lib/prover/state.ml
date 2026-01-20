
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
    val init : Tomega.__For -> Tomega.__Worlds -> __State
    val close : __State -> bool
    val collectT : Tomega.__Prg -> Tomega.__Prg list
    val collectLF : Tomega.__Prg -> IntSyn.__Exp list
    val collectLFSub : Tomega.__Sub -> IntSyn.__Exp list
  end;;




module State(State:sig module Formatter : FORMATTER end) : STATE =
  struct
    module Formatter = Formatter
    type __State =
      | State of (Tomega.__Worlds * Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg
      * Tomega.__For) 
      | StateLF of IntSyn.__Exp 
    type __Focus =
      | Focus of (Tomega.__Prg * Tomega.__Worlds) 
      | FocusLF of IntSyn.__Exp 
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    let rec findPrg =
      function
      | Lam (_, __P) -> findPrg __P
      | New (__P) -> findPrg __P
      | Choose (__P) -> findPrg __P
      | PairExp (_, __P) -> findPrg __P
      | PairBlock (__B, __P) -> findPrg __P
      | PairPrg (__P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | T.Unit -> []
      | Rec (_, __P) -> findPrg __P
      | Case (Cases (__C)) -> findCases __C
      | PClo (__P, t) -> (@) (findPrg __P) findSub t
      | Let (__D, __P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | LetPairExp (__D1, __D2, __P1, __P2) ->
          (@) (findPrg __P1) findPrg __P2
      | LetUnit (__P1, __P2) -> (@) (findPrg __P1) findPrg __P2
      | EVar (_, { contents = None }, _, _, _, _) as X -> [__X]
      | EVar (_, { contents = Some (__P) }, _, _, _, _) as X -> findPrg __P
      | Const _ -> []
      | Var _ -> []
      | Redex (__P, __S) -> (@) (findPrg __P) findSpine __S
    let rec findCases =
      function
      | nil -> []
      | (_, _, __P)::__C -> (@) (findPrg __P) findCases __C
    let rec findSub =
      function
      | Shift _ -> []
      | Dot (__F, t) -> (@) (findFront __F) findSub t
    let rec findFront =
      function
      | Idx _ -> []
      | Prg (__P) -> findPrg __P
      | Exp _ -> []
      | Block _ -> []
      | T.Undef -> []
    let rec findSpine =
      function
      | T.Nil -> []
      | AppPrg (__P, __S) -> (@) (findPrg __P) findSpine __S
      | AppExp (_, __S) -> findSpine __S
      | AppBlock (_, __S) -> findSpine __S
    let rec findExp __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Psi, Lam (__D, __P), __K) -> findExp ((I.Decl (Psi, __D)), __P) __K
      | (Psi, New (__P), __K) -> findExp (Psi, __P) __K
      | (Psi, Choose (__P), __K) -> findExp (Psi, __P) __K
      | (Psi, PairExp (__M, __P), __K) ->
          findExp (Psi, __P)
            (Abstract.collectEVars ((T.coerceCtx Psi), (__M, I.id), __K))
      | (Psi, PairBlock (__B, __P), __K) -> findExp (Psi, __P) __K
      | (Psi, PairPrg (__P1, __P2), __K) ->
          findExp (Psi, __P2) (findExp (Psi, __P1) __K)
      | (Psi, T.Unit, __K) -> __K
      | (Psi, Rec (__D, __P), __K) -> findExp (Psi, __P) __K
      | (Psi, Case (Cases (__C)), __K) -> findExpCases (Psi, __C) __K
      | (Psi, PClo (__P, t), __K) ->
          findExpSub (Psi, t) (findExp (Psi, __P) __K)
      | (Psi, Let (__D, __P1, __P2), __K) ->
          findExp ((I.Decl (Psi, __D)), __P2) (findExp (Psi, __P1) __K)
      | (Psi, LetPairExp (__D1, __D2, __P1, __P2), __K) ->
          findExp ((I.Decl ((I.Decl (Psi, (T.UDec __D1))), __D2)), __P2)
            (findExp (Psi, __P1) __K)
      | (Psi, LetUnit (__P1, __P2), __K) ->
          findExp (Psi, __P2) (findExp (Psi, __P1) __K)
      | (Psi, (EVar _ as X), __K) -> __K
      | (Psi, Const _, __K) -> __K
      | (Psi, Var _, __K) -> __K
      | (Psi, Redex (__P, __S), __K) -> findExpSpine (Psi, __S) __K(* by invariant: Blocks don't contain free evars. *)
    let rec findExpSpine __3__ __4__ __5__ =
      match (__3__, __4__, __5__) with
      | (Psi, T.Nil, __K) -> __K
      | (Psi, AppPrg (_, __S), __K) -> findExpSpine (Psi, __S) __K
      | (Psi, AppExp (__M, __S), __K) ->
          findExpSpine (Psi, __S)
            (Abstract.collectEVars ((T.coerceCtx Psi), (__M, I.id), __K))
      | (Psi, AppBlock (_, __S), __K) -> findExpSpine (Psi, __S) __K
    let rec findExpCases __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (Psi, nil, __K) -> __K
      | (Psi, (_, _, __P)::__C, __K) ->
          findExpCases (Psi, __C) (findExp (Psi, __P) __K)
    let rec findExpSub __9__ __10__ __11__ =
      match (__9__, __10__, __11__) with
      | (Psi, Shift _, __K) -> __K
      | (Psi, Dot (__F, t), __K) ->
          findExpSub (Psi, t) (findExpFront (Psi, __F) __K)
    let rec findExpFront __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (Psi, Idx _, __K) -> __K
      | (Psi, Prg (__P), __K) -> findExp (Psi, __P) __K
      | (Psi, Exp (__M), __K) ->
          Abstract.collectEVars ((T.coerceCtx Psi), (__M, I.id), __K)
      | (Psi, Block _, __K) -> __K
      | (Psi, T.Undef, __K) -> __K
    let rec init (__F) (__W) =
      let __X = T.newEVar (I.Null, __F) in State (__W, I.Null, __X, __F)
    let rec close (State (__W, _, __P, _)) =
      match ((findPrg __P), (findExp (I.Null, __P) [])) with
      | (nil, nil) -> true
      | _ -> false
    let close = close
    let init = init
    let collectT = findPrg
    let collectLF (__P) = findExp (I.Null, __P) []
    let collectLFSub s = findExpSub (I.Null, s) []
  end ;;
