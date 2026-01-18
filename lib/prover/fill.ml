
(* Filling: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type FILL  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




(* Filling *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:08:33 2006 *)
module Fill(Fill:sig
                   module Data : DATA
                   module State' : STATE
                   module Abstract : ABSTRACT
                   module TypeCheck : TYPECHECK
                   module Search : SEARCH
                   module Whnf : WHNF
                   (*! structure IntSyn' : INTSYN !*)
                   (*! structure Tomega' : TOMEGA !*)
                   (*! sharing Tomega'.IntSyn = IntSyn' !*)
                   (*! sharing State'.IntSyn = IntSyn' !*)
                   (*! sharing State'.Tomega = Tomega' !*)
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   (*! sharing Abstract.Tomega = Tomega' !*)
                   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                   (*! sharing Search.IntSyn = IntSyn' !*)
                   (*! sharing Search.Tomega = Tomega' !*)
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   module Unify : UNIFY
                 end) : FILL =
  struct
    (*! sharing Unify.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
    exception Error of string 
    type __Operator =
      | FillWithConst of (IntSyn.__Exp * IntSyn.cid) 
      | FillWithBVar of (IntSyn.__Exp * int) 
    (* Representation Invariant:  FillWithBVar (x, n) :
           x is an evar GX |- x : VX
           GX |- n : W
           and VX and W are unifiable
       *)
    type nonrec operator = __Operator
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
    let rec expand (FocusLF (EVar (r, __g, __v, _) as y)) =
      let rec try__ =
        function
        | (((Root _, _) as __Vs), __Fs, O) ->
            (try
               CSManager.trail
                 (function | () -> (Unify.unify (__g, __Vs, (__v, I.id)); O :: __Fs))
             with | Unify _ -> __Fs)
        | ((Pi ((Dec (_, V1), _), V2), s), __Fs, O) ->
            let x = I.newEVar (__g, (I.EClo (V1, s))) in
            try__ ((V2, (I.Dot ((I.Exp x), s))), __Fs, O)
        | ((EClo (__v, s'), s), __Fs, O) -> try__ ((__v, (I.comp (s', s))), __Fs, O) in
      let rec matchCtx =
        function
        | (I.Null, _, __Fs) -> __Fs
        | (Decl (__g, Dec (x, __v)), n, __Fs) ->
            matchCtx
              (__g, (n + 1),
                (try__
                   ((__v, (I.Shift (n + 1))), __Fs, (FillWithBVar (y, (n + 1))))))
        | (Decl (__g, NDec _), n, __Fs) -> matchCtx (__g, (n + 1), __Fs) in
      let rec matchSig =
        function
        | (nil, __Fs) -> __Fs
        | ((Const c)::__l, __Fs) ->
            matchSig
              (__l,
                (try__ (((I.constType c), I.id), __Fs, (FillWithConst (y, c))))) in
      matchCtx (__g, 0, (matchSig ((Index.lookup (I.targetFam __v)), nil)))
    let rec apply =
      function
      | FillWithBVar ((EVar (r, __g, __v, _) as y), n) ->
          let rec doit =
            function
            | (((Root _, _) as __Vs), k) ->
                (Unify.unify (__g, __Vs, (__v, I.id)); k I.Nil)
            | ((Pi ((Dec (_, V1), _), V2), s), k) ->
                let x = I.newEVar (__g, (I.EClo (V1, s))) in
                doit
                  ((V2, (I.Dot ((I.Exp x), s))),
                    (function | S -> k (I.App (x, S))))
            | ((EClo (__v, t), s), k) -> doit ((__v, (I.comp (t, s))), k) in
          let Dec (_, W) = I.ctxDec (__g, n) in
          doit
            ((W, I.id),
              (function
               | S ->
                   Unify.unify
                     (__g, (y, I.id), ((I.Root ((I.BVar n), S)), I.id))))
      | FillWithConst ((EVar (r, G0, __v, _) as y), c) ->
          let rec doit =
            function
            | (((Root _, _) as __Vs), k) ->
                (Unify.unify (G0, __Vs, (__v, I.id)); k I.Nil)
            | ((Pi ((Dec (_, V1), _), V2), s), k) ->
                let x = I.newEVar (G0, (I.EClo (V1, s))) in
                doit
                  ((V2, (I.Dot ((I.Exp x), s))),
                    (function | S -> k (I.App (x, S)))) in
          let W = I.constType c in
          doit
            ((W, I.id),
              (function
               | S ->
                   Unify.unify
                     (G0, (y, I.id), ((I.Root ((I.Const c), S)), I.id))))
    let rec menu =
      function
      | FillWithBVar ((EVar (_, __g, _, _) as x), n) ->
          (match I.ctxLookup ((Names.ctxName __g), n) with
           | Dec (Some x, _) ->
               (((^) "Fill " Names.evarName (__g, x)) ^ " with variable ") ^ x)
      | FillWithConst ((EVar (_, __g, _, _) as x), c) ->
          (^) (((^) "Fill " Names.evarName (__g, x)) ^ " with constant ")
            IntSyn.conDecName (IntSyn.sgnLookup c)
    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
    (* y is lowered *)
    (* matchCtx (__g, n, __Fs) = __Fs'

           Invariant:
           If G0 = __g, __g' and |__g'| = n and __Fs a list of filling operators that
           satisfy the representation invariant, then __Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
    (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
    (* y is lowered *)
    (* Invariant : __g |- s : __g'   __g' |- __v : type *)
    (* Unify must succeed *)
    (* Unify must succeed *)
    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
