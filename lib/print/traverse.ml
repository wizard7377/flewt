
module type TRAVERSER  =
  sig
    type nonrec tp
    type nonrec obj
    type nonrec head
    type nonrec spine
    type nonrec dec
    type nonrec condec
    val atom : (head * spine) -> tp
    val arrow : (tp * tp) -> tp
    val pi : (dec * tp) -> tp
    val root : (head * spine * tp) -> obj
    val lam : (dec * obj) -> obj
    val bvar : string -> head
    val const : (string list * string) -> head
    val def : (string list * string) -> head
    val nils : spine
    val app : (obj * spine) -> spine
    val dec : (string * tp) -> dec
    val objdec : (string * tp) -> condec
  end
module type TRAVERSE  =
  sig
    module Traverser :
    ((TRAVERSER)(* Generic Traversal Intended for Language-Specific Printing *)
    (* Author: Frank Pfenning *)(* type kind *)
    (* propagate type to every root *)(* no evar, skonst, or fvar *)
    (* val famdec : string * kind -> condec *)(* val objdef : string * obj * tp -> condec *)
    (* val famdef : string * tp * kind -> condec *)(* val skodec : string * tp -> condec *)
    (* signature TRAVERSER *)(*! structure IntSyn : INTSYN !*))
    exception Error of string 
    val fromConDec : IntSyn.__ConDec -> Traverser.condec option
    val const : string -> Traverser.condec
  end;;




module Traverse(Traverse:sig
                           module Whnf : WHNF
                           module Names : NAMES
                           module Traverser' :
                           ((TRAVERSER)(*! structure IntSyn' : INTSYN !*)
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Names.IntSyn = IntSyn' !*))
                         end) : TRAVERSE =
  struct
    module Traverser =
      ((Traverser')(* shares types from Traverser' *)
      (*! structure IntSyn = IntSyn' !*))
    exception Error of string 
    module I = IntSyn
    module T = Traverser
    let rec inferConW =
      function
      | (g, BVar k') ->
          let Dec (_, V) = I.ctxDec (g, k') in Whnf.whnf (V, I.id)
      | (g, Const c) -> ((I.constType c), I.id)
      | (g, Def d) -> ((I.constType d), I.id)
    let rec fromHead =
      function
      | (g, BVar n) -> T.bvar (Names.bvarName (g, n))
      | (g, Const cid) ->
          let Qid (ids, id) = Names.constQid cid in T.const (ids, id)
      | (g, Def cid) ->
          let Qid (ids, id) = Names.constQid cid in T.def (ids, id)
      | _ -> raise (Error "Head not recognized")
    let rec impCon =
      function
      | Const cid -> I.constImp cid
      | Def cid -> I.constImp cid
      | _ -> 0
    let rec fromTpW =
      function
      | (g, (Root (C, S), s)) ->
          T.atom
            ((fromHead (g, C)),
              (fromSpine ((impCon C), g, (S, s), (inferConW (g, C)))))
      | (g, (Pi (((Dec (_, V1) as D), I.No), V2), s)) ->
          T.arrow
            ((fromTp (g, (V1, s))),
              (fromTp ((I.Decl (g, (I.decSub (D, s)))), (V2, (I.dot1 s)))))
      | (g, (Pi ((D, I.Maybe), V2), s)) ->
          let D' = Names.decUName (g, D) in
          T.pi
            ((fromDec (g, (D', s))),
              (fromTp ((I.Decl (g, (I.decSub (D', s)))), (V2, (I.dot1 s)))))
      | _ -> raise (Error "Type not recognized")
    let rec fromTp (g, Vs) = fromTpW (g, (Whnf.whnf Vs))
    let rec fromObjW =
      function
      | (g, (Root (C, S), s), (V, t)) ->
          T.root
            ((fromHead (g, C)),
              (fromSpine ((impCon C), g, (S, s), (inferConW (g, C)))),
              (fromTp (g, (V, t))))
      | (g, (Lam (D, U), s), (Pi (_, V), t)) ->
          let D' = Names.decUName (g, D) in
          T.lam
            ((fromDec (g, (D', s))),
              (fromObj
                 ((I.Decl (g, (I.decSub (D', s)))), (U, (I.dot1 s)),
                   (V, (I.dot1 t)))))
      | _ -> raise (Error "Object not recognized")
    let rec fromObj (g, Us, Vt) =
      fromObjW (g, (Whnf.whnf Us), (Whnf.whnf Vt))
    let rec fromSpine =
      function
      | (i, g, (I.Nil, s), Vt) -> T.nils
      | (i, g, (SClo (S, s'), s), Vt) ->
          fromSpine (i, g, (S, (I.comp (s', s))), Vt)
      | (i, g, (App (U, S), s), (Pi ((Dec (_, V1), _), V2), t)) ->
          if i > 0
          then
            fromSpine
              ((i - 1), g, (S, s),
                (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s))), t)))))
          else
            T.app
              ((fromObj (g, (U, s), (V1, t))),
                (fromSpine
                   (i, g, (S, s),
                     (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s))), t)))))))
    let rec fromDec (g, (Dec (SOME x, V), s)) =
      T.dec (x, (fromTp (g, (V, s))))
    let rec fromConDec =
      function
      | ConDec (c, parent, i, _, V, I.Type) ->
          SOME (T.objdec (c, (fromTp (I.Null, (V, I.id)))))
      | _ -> NONE
    let ((fromConDec)(* from typecheck.fun *)(* inferCon (g, C) = V'

     Invariant:
     If    g |- C : V
     and  (C  doesn't contain FVars)
     then  g' |- V' : L      (for some level L)
     and   g |- V = V' : L
     else exception Error is raised.
  *)
      (* no case for FVar, Skonst *)(* | fromHead (g, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
      (* | fromHead (g, FVar (name, _, _)) = T.fvar (name) *)(* see also: print.fun *)
      (*| imps (I.Skonst (cid)) = I.constImp (cid) *)
      (* see also: print.fun *)(*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)
      (* note: no case for EVars right now *)(* drop implicit arg *)
      (* NONE should not occur because of call to decName *)
      (*
    | fromDec (g, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (g, (V, s)))
    *)
      (* ignore a : K, d : A = M, b : K = A, and skolem constants *))
      = fromConDec
    let rec const name =
      let qid =
        match Names.stringToQid name with
        | NONE -> raise (Error ("Malformed qualified identifier " ^ name))
        | SOME qid -> qid in
      let cidOpt = Names.constLookup qid in
      let getConDec =
        function
        | NONE ->
            raise
              (Error ((^) "Undeclared identifier " Names.qidToString qid))
        | SOME cid -> IntSyn.sgnLookup cid in
      let conDec = getConDec cidOpt in
      let _ = Names.varReset IntSyn.Null in
      let result =
        function
        | NONE -> raise (Error "Wrong kind of declaration")
        | SOME r -> r in
      result (fromConDec conDec)
  end ;;
