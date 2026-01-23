module type FILL  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.focus_ -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end


module Fill(Fill:sig
                   module Data : DATA
                   module State' : STATE
                   module Abstract : ABSTRACT
                   module TypeCheck : TYPECHECK
                   module Search : SEARCH
                   module Whnf : WHNF
                   module Unify : UNIFY
                 end) : FILL =
  struct
    module State = State'
    exception Error of string 
    type operator_ =
      | FillWithConst of (IntSyn.exp_ * IntSyn.cid) 
      | FillWithBVar of (IntSyn.exp_ * int) 
    type nonrec operator = operator_
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
    let rec expand (FocusLF (EVar (r, g_, v_, _) as y_)) =
      let rec try_ =
        begin function
        | (((Root _, _) as vs_), fs_, o_) ->
            (begin try
                     CSManager.trail
                       (begin function
                        | () ->
                            (begin Unify.unify (g_, vs_, (v_, I.id));
                             o_ :: fs_ end) end)
        with | Unify _ -> fs_ end)
      | ((Pi ((Dec (_, v1_), _), v2_), s), fs_, o_) ->
          let x_ = I.newEVar (g_, (I.EClo (v1_, s))) in
          try_ ((v2_, (I.Dot ((I.Exp x_), s))), fs_, o_)
      | ((EClo (v_, s'), s), fs_, o_) ->
          try_ ((v_, (I.comp (s', s))), fs_, o_) end in
  let rec matchCtx =
    begin function
    | (I.Null, _, fs_) -> fs_
    | (Decl (g_, Dec (x, v_)), n, fs_) ->
        matchCtx
          (g_, (n + 1),
            (try_
               ((v_, (I.Shift (n + 1))), fs_, (FillWithBVar (y_, (n + 1))))))
    | (Decl (g_, NDec _), n, fs_) -> matchCtx (g_, (n + 1), fs_) end in
  let rec matchSig =
    begin function
    | ([], fs_) -> fs_
    | ((Const c)::l_, fs_) ->
        matchSig
          (l_,
            (try_ (((I.constType c), I.id), fs_, (FillWithConst (y_, c))))) end in
  ((matchCtx (g_, 0, (matchSig ((Index.lookup (I.targetFam v_)), []))))
    (* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *))
(* Y is lowered *)
let rec apply =
  begin function
  | FillWithBVar ((EVar (r, g_, v_, _) as y_), n) ->
      let rec doit =
        begin function
        | (((Root _, _) as vs_), k) ->
            (begin Unify.unify (g_, vs_, (v_, I.id)); k I.Nil end)
        | ((Pi ((Dec (_, v1_), _), v2_), s), k) ->
            let x_ = I.newEVar (g_, (I.EClo (v1_, s))) in
            doit
              ((v2_, (I.Dot ((I.Exp x_), s))),
                (begin function | s_ -> k (I.App (x_, s_)) end))
        | ((EClo (v_, t), s), k) -> doit ((v_, (I.comp (t, s))), k) end
  (* Unify must succeed *) in
let Dec (_, w_) = I.ctxDec (g_, n) in
((doit
    ((w_, I.id),
      (begin function
       | s_ ->
           Unify.unify (g_, (y_, I.id), ((I.Root ((I.BVar n), s_)), I.id)) end)))
  (* Invariant : G |- s : G'   G' |- V : type *))
| FillWithConst ((EVar (r, g0_, v_, _) as y_), c) ->
    let rec doit =
      begin function
      | (((Root _, _) as vs_), k) ->
          (begin Unify.unify (g0_, vs_, (v_, I.id)); k I.Nil end)
      | ((Pi ((Dec (_, v1_), _), v2_), s), k) ->
          let x_ = I.newEVar (g0_, (I.EClo (v1_, s))) in
          doit
            ((v2_, (I.Dot ((I.Exp x_), s))),
              (begin function | s_ -> k (I.App (x_, s_)) end)) end(* Unify must succeed *) in
let w_ = I.constType c in
doit
((w_, I.id),
  (begin function
   | s_ -> Unify.unify (g0_, (y_, I.id), ((I.Root ((I.Const c), s_)), I.id)) end)) end
(* Y is lowered *)
let rec menu =
  begin function
  | FillWithBVar ((EVar (_, g_, _, _) as x_), n) ->
      (begin match I.ctxLookup ((Names.ctxName g_), n) with
       | Dec (Some x, _) ->
           (((^) "Fill " Names.evarName (g_, x_)) ^ " with variable ") ^ x end)
  | FillWithConst ((EVar (_, g_, _, _) as x_), c) ->
      (^) (((^) "Fill " Names.evarName (g_, x_)) ^ " with constant ")
        IntSyn.conDecName (IntSyn.sgnLookup c) end(* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
let expand = expand
let apply = apply
let menu = menu end
