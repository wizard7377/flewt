module type STATE  =
  sig
    exception Error of string 
    type state_ =
      | State of (Tomega.worlds_ * Tomegas.dec_ IntSyn.ctx_ * Tomega.prg_ *
      Tomega.for_) 
      | StateLF of IntSyn.exp_ 
    type focus_ =
      | Focus of (Tomega.prg_ * Tomega.worlds_) 
      | FocusLF of IntSyn.exp_ 
    val init : (Tomega.for_ * Tomega.worlds_) -> state_
    val close : state_ -> bool
    val collectT : Tomega.prg_ -> Tomega.prg_ list
    val collectLF : Tomega.prg_ -> IntSyn.exp_ list
    val collectLFSub : Tomega.sub_ -> IntSyn.exp_ list
  end


module State(State:sig module Formatter : FORMATTER end) : STATE =
  struct
    module Formatter = Formatter
    type state_ =
      | State of (Tomega.worlds_ * Tomega.dec_ IntSyn.ctx_ * Tomega.prg_ *
      Tomega.for_) 
      | StateLF of IntSyn.exp_ 
    type focus_ =
      | Focus of (Tomega.prg_ * Tomega.worlds_) 
      | FocusLF of IntSyn.exp_ 
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    let rec findPrg =
      begin function
      | Lam (_, p_) -> findPrg p_
      | New (p_) -> findPrg p_
      | Choose (p_) -> findPrg p_
      | PairExp (_, p_) -> findPrg p_
      | PairBlock (b_, p_) -> findPrg p_
      | PairPrg (p1_, p2_) -> (@) (findPrg p1_) findPrg p2_
      | T.Unit -> []
      | Rec (_, p_) -> findPrg p_
      | Case (Cases (c_)) -> findCases c_
      | PClo (p_, t) -> (@) (findPrg p_) findSub t
      | Let (d_, p1_, p2_) -> (@) (findPrg p1_) findPrg p2_
      | LetPairExp (d1_, d2_, p1_, p2_) -> (@) (findPrg p1_) findPrg p2_
      | LetUnit (p1_, p2_) -> (@) (findPrg p1_) findPrg p2_
      | EVar (_, { contents = None }, _, _, _, _) as x_ -> [x_]
      | EVar (_, { contents = Some (p_) }, _, _, _, _) as x_ -> findPrg p_
      | Const _ -> []
      | Var _ -> []
      | Redex (p_, s_) -> (@) (findPrg p_) findSpine s_ end
    let rec findCases =
      begin function
      | [] -> []
      | (_, _, p_)::c_ -> (@) (findPrg p_) findCases c_ end
  let rec findSub =
    begin function
    | Shift _ -> []
    | Dot (f_, t) -> (@) (findFront f_) findSub t end
let rec findFront =
  begin function
  | Idx _ -> []
  | Prg (p_) -> findPrg p_
  | Exp _ -> []
  | Block _ -> []
  | T.Undef -> [] end
let rec findSpine =
  begin function
  | T.Nil -> []
  | AppPrg (p_, s_) -> (@) (findPrg p_) findSpine s_
  | AppExp (_, s_) -> findSpine s_
  | AppBlock (_, s_) -> findSpine s_ end
let rec findExp arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | ((Psi, Lam (d_, p_)), k_) -> findExp ((I.Decl (Psi, d_)), p_) k_
  | ((Psi, New (p_)), k_) -> findExp (Psi, p_) k_
  | ((Psi, Choose (p_)), k_) -> findExp (Psi, p_) k_
  | ((Psi, PairExp (m_, p_)), k_) ->
      findExp (Psi, p_)
        (Abstract.collectEVars ((T.coerceCtx Psi), (m_, I.id), k_))
  | ((Psi, PairBlock (b_, p_)), k_) -> findExp (Psi, p_) k_
  | ((Psi, PairPrg (p1_, p2_)), k_) ->
      findExp (Psi, p2_) (findExp (Psi, p1_) k_)
  | ((Psi, T.Unit), k_) -> k_
  | ((Psi, Rec (d_, p_)), k_) -> findExp (Psi, p_) k_
  | ((Psi, Case (Cases (c_))), k_) -> findExpCases (Psi, c_) k_
  | ((Psi, PClo (p_, t)), k_) -> findExpSub (Psi, t) (findExp (Psi, p_) k_)
  | ((Psi, Let (d_, p1_, p2_)), k_) ->
      findExp ((I.Decl (Psi, d_)), p2_) (findExp (Psi, p1_) k_)
  | ((Psi, LetPairExp (d1_, d2_, p1_, p2_)), k_) ->
      findExp ((I.Decl ((I.Decl (Psi, (T.UDec d1_))), d2_)), p2_)
        (findExp (Psi, p1_) k_)
  | ((Psi, LetUnit (p1_, p2_)), k_) ->
      findExp (Psi, p2_) (findExp (Psi, p1_) k_)
  | ((Psi, (EVar _ as x_)), k_) -> k_
  | ((Psi, Const _), k_) -> k_
  | ((Psi, Var _), k_) -> k_
  | ((Psi, Redex (p_, s_)), k_) -> findExpSpine (Psi, s_) k_ end(* by invariant: Blocks don't contain free evars. *)
let rec findExpSpine arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | ((Psi, T.Nil), k_) -> k_
  | ((Psi, AppPrg (_, s_)), k_) -> findExpSpine (Psi, s_) k_
  | ((Psi, AppExp (m_, s_)), k_) ->
      findExpSpine (Psi, s_)
        (Abstract.collectEVars ((T.coerceCtx Psi), (m_, I.id), k_))
  | ((Psi, AppBlock (_, s_)), k_) -> findExpSpine (Psi, s_) k_ end
let rec findExpCases arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | ((Psi, []), k_) -> k_
  | ((Psi, (_, _, p_)::c_), k_) ->
      findExpCases (Psi, c_) (findExp (Psi, p_) k_) end
let rec findExpSub arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | ((Psi, Shift _), k_) -> k_
  | ((Psi, Dot (f_, t)), k_) ->
      findExpSub (Psi, t) (findExpFront (Psi, f_) k_) end
let rec findExpFront arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | ((Psi, Idx _), k_) -> k_
  | ((Psi, Prg (p_)), k_) -> findExp (Psi, p_) k_
  | ((Psi, Exp (m_)), k_) ->
      Abstract.collectEVars ((T.coerceCtx Psi), (m_, I.id), k_)
  | ((Psi, Block _), k_) -> k_
  | ((Psi, T.Undef), k_) -> k_ end
let rec init (f_, w_) =
  let x_ = T.newEVar (I.Null, f_) in State (w_, I.Null, x_, f_)
let rec close (State (w_, _, p_, _)) =
  begin match ((findPrg p_), (findExp (I.Null, p_) [])) with
  | ([], []) -> true
  | _ -> false end
let close = close
let init = init
let collectT = findPrg
let collectLF = begin function | p_ -> findExp (I.Null, p_) [] end
let collectLFSub = begin function | s -> findExpSub (I.Null, s) [] end end
