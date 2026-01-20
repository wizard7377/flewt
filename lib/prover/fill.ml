
module type FILL  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




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
    type __Operator =
      | FillWithConst of (IntSyn.__Exp * IntSyn.cid) 
      | FillWithBVar of (IntSyn.__Exp * int) 
    type nonrec operator = __Operator
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
    let rec expand (FocusLF (EVar (r, __G, __V, _) as Y)) =
      let rec try__ __0__ __1__ __2__ =
        match (__0__, __1__, __2__) with
        | (((Root _, _) as Vs), __Fs, __O) ->
            (try
               CSManager.trail
                 (fun () -> Unify.unify (__G, __Vs, (__V, I.id)); __O :: __Fs)
             with | Unify _ -> __Fs)
        | ((Pi ((Dec (_, __V1), _), __V2), s), __Fs, __O) ->
            let __X = I.newEVar (__G, (I.EClo (__V1, s))) in
            try__ ((__V2, (I.Dot ((I.Exp __X), s))), __Fs, __O)
        | ((EClo (__V, s'), s), __Fs, __O) ->
            try__ ((__V, (I.comp (s', s))), __Fs, __O) in
      let rec matchCtx __3__ __4__ __5__ =
        match (__3__, __4__, __5__) with
        | (I.Null, _, __Fs) -> __Fs
        | (Decl (__G, Dec (x, __V)), n, __Fs) ->
            matchCtx
              (__G, (n + 1),
                (try__
                   ((__V, (I.Shift (n + 1))), __Fs,
                     (FillWithBVar (__Y, (n + 1))))))
        | (Decl (__G, NDec _), n, __Fs) -> matchCtx (__G, (n + 1), __Fs) in
      let rec matchSig __6__ __7__ =
        match (__6__, __7__) with
        | (nil, __Fs) -> __Fs
        | ((Const c)::__L, __Fs) ->
            matchSig
              (__L,
                (try__
                   (((I.constType c), I.id), __Fs, (FillWithConst (__Y, c))))) in
      ((matchCtx (__G, 0, (matchSig ((Index.lookup (I.targetFam __V)), nil))))
        (* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *))
      (* Y is lowered *)
    let rec apply =
      function
      | FillWithBVar ((EVar (r, __G, __V, _) as Y), n) ->
          let rec doit __8__ __9__ =
            match (__8__, __9__) with
            | (((Root _, _) as Vs), k) ->
                (Unify.unify (__G, __Vs, (__V, I.id)); k I.Nil)
            | ((Pi ((Dec (_, __V1), _), __V2), s), k) ->
                let __X = I.newEVar (__G, (I.EClo (__V1, s))) in
                doit
                  ((__V2, (I.Dot ((I.Exp __X), s))),
                    (fun (__S) -> k (I.App (__X, __S))))
            | ((EClo (__V, t), s), k) -> doit ((__V, (I.comp (t, s))), k)
            (* Unify must succeed *) in
          let Dec (_, __W) = I.ctxDec (__G, n) in
          ((doit
              ((__W, I.id),
                (fun (__S) ->
                   Unify.unify
                     (__G, (__Y, I.id), ((I.Root ((I.BVar n), __S)), I.id)))))
            (* Invariant : G |- s : G'   G' |- V : type *))
      | FillWithConst ((EVar (r, __G0, __V, _) as Y), c) ->
          let rec doit __10__ __11__ =
            match (__10__, __11__) with
            | (((Root _, _) as Vs), k) ->
                (Unify.unify (__G0, __Vs, (__V, I.id)); k I.Nil)
            | ((Pi ((Dec (_, __V1), _), __V2), s), k) ->
                let __X = I.newEVar (__G0, (I.EClo (__V1, s))) in
                doit
                  ((__V2, (I.Dot ((I.Exp __X), s))),
                    (fun (__S) -> k (I.App (__X, __S))))(* Unify must succeed *) in
          let __W = I.constType c in
          doit
            ((__W, I.id),
              (fun (__S) ->
                 Unify.unify
                   (__G0, (__Y, I.id), ((I.Root ((I.Const c), __S)), I.id))))
      (* Y is lowered *)
    let rec menu =
      function
      | FillWithBVar ((EVar (_, __G, _, _) as X), n) ->
          (match I.ctxLookup ((Names.ctxName __G), n) with
           | Dec (Some x, _) ->
               (((^) "Fill " Names.evarName (__G, __X)) ^ " with variable ")
                 ^ x)
      | FillWithConst ((EVar (_, __G, _, _) as X), c) ->
          (^) (((^) "Fill " Names.evarName (__G, __X)) ^ " with constant ")
            IntSyn.conDecName (IntSyn.sgnLookup c)(* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
