
module type FILL  =
  sig
    module State :
    ((STATE)(* Filling: Version 1.4 *)(* Author: Carsten Schuermann *)
    (*! structure IntSyn : INTSYN !*)(*! structure Tomega : TOMEGA !*))
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
                   module Unify :
                   ((UNIFY)(* Filling *)(* Author: Carsten Schuermann *)
                   (* Date: Thu Mar 16 13:08:33 2006 *)
                   (*! structure IntSyn' : INTSYN !*)
                   (*! structure Tomega' : TOMEGA !*)
                   (*! sharing Tomega'.IntSyn = IntSyn' !*)
                   (*! sharing State'.IntSyn = IntSyn' !*)
                   (*! sharing State'.Tomega = Tomega' !*)
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   (*! sharing Abstract.Tomega = Tomega' !*)
                   (*! sharing TypeCheck.IntSyn = IntSyn' !*)(*! sharing Search.IntSyn = IntSyn' !*)
                   (*! sharing Search.Tomega = Tomega' !*)
                   (*! sharing Whnf.IntSyn = IntSyn' !*))
                 end) : FILL =
  struct
    module State =
      ((State')(*! sharing Unify.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure Tomega = Tomega' !*))
    exception Error of string 
    type __Operator =
      | FillWithConst of (IntSyn.__Exp * IntSyn.cid) 
      | FillWithBVar of
      (((IntSyn.__Exp)(* Representation Invariant:  FillWithConst (X, c) :
           X is an evar GX |- X : VX
           Sigma |- c : W
           and VX and W are unifiable
       *))
      * int) 
    type nonrec operator =
      ((__Operator)(* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *))
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
    let rec expand (FocusLF (EVar (r, G, V, _) as Y)) =
      let try__ =
        function
        | (((Root _, _) as Vs), Fs, O) ->
            (try
               CSManager.trail
                 (function | () -> (Unify.unify (G, Vs, (V, I.id)); O :: Fs))
             with | Unify _ -> Fs)
        | ((Pi ((Dec (_, V1), _), V2), s), Fs, O) ->
            let X = I.newEVar (G, (I.EClo (V1, s))) in
            try__ ((V2, (I.Dot ((I.Exp X), s))), Fs, O)
        | ((EClo (V, s'), s), Fs, O) -> try__ ((V, (I.comp (s', s))), Fs, O) in
      let matchCtx =
        function
        | (I.Null, _, Fs) -> Fs
        | (Decl (G, Dec (x, V)), n, Fs) ->
            matchCtx
              (G, (n + 1),
                (try__
                   ((V, (I.Shift (n + 1))), Fs, (FillWithBVar (Y, (n + 1))))))
        | (Decl (G, NDec _), n, Fs) -> matchCtx (G, (n + 1), Fs) in
      let matchSig =
        function
        | (nil, Fs) -> Fs
        | ((Const c)::L, Fs) ->
            matchSig
              (L,
                (try__ (((I.constType c), I.id), Fs, (FillWithConst (Y, c))))) in
      matchCtx (G, 0, (matchSig ((Index.lookup (I.targetFam V)), nil)))
    let rec apply =
      function
      | FillWithBVar ((EVar (r, G, V, _) as Y), n) ->
          let doit =
            function
            | (((Root _, _) as Vs), k) ->
                (Unify.unify (G, Vs, (V, I.id)); k I.Nil)
            | ((Pi ((Dec (_, V1), _), V2), s), k) ->
                let X = I.newEVar (G, (I.EClo (V1, s))) in
                doit
                  ((V2, (I.Dot ((I.Exp X), s))),
                    (function | S -> k (I.App (X, S))))
            | ((EClo (V, t), s), k) -> doit ((V, (I.comp (t, s))), k) in
          let Dec (_, W) = I.ctxDec (G, n) in
          doit
            ((W, I.id),
              (function
               | S ->
                   Unify.unify
                     (G, (Y, I.id), ((I.Root ((I.BVar n), S)), I.id))))
      | FillWithConst ((EVar (r, G0, V, _) as Y), c) ->
          let doit =
            function
            | (((Root _, _) as Vs), k) ->
                (Unify.unify (G0, Vs, (V, I.id)); k I.Nil)
            | ((Pi ((Dec (_, V1), _), V2), s), k) ->
                let X = I.newEVar (G0, (I.EClo (V1, s))) in
                doit
                  ((V2, (I.Dot ((I.Exp X), s))),
                    (function | S -> k (I.App (X, S)))) in
          let W = I.constType c in
          doit
            ((W, I.id),
              (function
               | S ->
                   Unify.unify
                     (G0, (Y, I.id), ((I.Root ((I.Const c), S)), I.id))))
    let rec menu =
      function
      | FillWithBVar ((EVar (_, G, _, _) as X), n) ->
          (match I.ctxLookup ((Names.ctxName G), n) with
           | Dec (SOME x, _) ->
               (((^) "Fill " Names.evarName (G, X)) ^ " with variable ") ^ x)
      | FillWithConst ((EVar (_, G, _, _) as X), c) ->
          (^) (((^) "Fill " Names.evarName (G, X)) ^ " with constant ")
            IntSyn.conDecName (IntSyn.sgnLookup c)
    let ((expand)(* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
      (* Y is lowered *)(* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
      (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
      (* Y is lowered *)(* Invariant : G |- s : G'   G' |- V : type *)
      (* Unify must succeed *)(* Unify must succeed *)
      (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
      (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *))
      = expand
    let apply = apply
    let menu = menu
  end ;;
