
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
      | (G, BVar k') ->
          let Dec (_, V) = I.ctxDec (G, k') in Whnf.whnf (V, I.id)
      | (G, Const c) -> ((I.constType c), I.id)
      | (G, Def d) -> ((I.constType d), I.id)
    let rec fromHead =
      function
      | (G, BVar n) -> T.bvar (Names.bvarName (G, n))
      | (G, Const cid) ->
          let Qid (ids, id) = Names.constQid cid in T.const (ids, id)
      | (G, Def cid) ->
          let Qid (ids, id) = Names.constQid cid in T.def (ids, id)
      | _ -> raise (Error "Head not recognized")
    let rec impCon =
      function
      | Const cid -> I.constImp cid
      | Def cid -> I.constImp cid
      | _ -> 0
    let rec fromTpW =
      function
      | (G, (Root (C, S), s)) ->
          T.atom
            ((fromHead (G, C)),
              (fromSpine ((impCon C), G, (S, s), (inferConW (G, C)))))
      | (G, (Pi (((Dec (_, V1) as D), I.No), V2), s)) ->
          T.arrow
            ((fromTp (G, (V1, s))),
              (fromTp ((I.Decl (G, (I.decSub (D, s)))), (V2, (I.dot1 s)))))
      | (G, (Pi ((D, I.Maybe), V2), s)) ->
          let D' = Names.decUName (G, D) in
          T.pi
            ((fromDec (G, (D', s))),
              (fromTp ((I.Decl (G, (I.decSub (D', s)))), (V2, (I.dot1 s)))))
      | _ -> raise (Error "Type not recognized")
    let rec fromTp (G, Vs) = fromTpW (G, (Whnf.whnf Vs))
    let rec fromObjW =
      function
      | (G, (Root (C, S), s), (V, t)) ->
          T.root
            ((fromHead (G, C)),
              (fromSpine ((impCon C), G, (S, s), (inferConW (G, C)))),
              (fromTp (G, (V, t))))
      | (G, (Lam (D, U), s), (Pi (_, V), t)) ->
          let D' = Names.decUName (G, D) in
          T.lam
            ((fromDec (G, (D', s))),
              (fromObj
                 ((I.Decl (G, (I.decSub (D', s)))), (U, (I.dot1 s)),
                   (V, (I.dot1 t)))))
      | _ -> raise (Error "Object not recognized")
    let rec fromObj (G, Us, Vt) =
      fromObjW (G, (Whnf.whnf Us), (Whnf.whnf Vt))
    let rec fromSpine =
      function
      | (i, G, (I.Nil, s), Vt) -> T.nils
      | (i, G, (SClo (S, s'), s), Vt) ->
          fromSpine (i, G, (S, (I.comp (s', s))), Vt)
      | (i, G, (App (U, S), s), (Pi ((Dec (_, V1), _), V2), t)) ->
          if i > 0
          then
            fromSpine
              ((i - 1), G, (S, s),
                (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s))), t)))))
          else
            T.app
              ((fromObj (G, (U, s), (V1, t))),
                (fromSpine
                   (i, G, (S, s),
                     (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U, s))), t)))))))
    let rec fromDec (G, (Dec (SOME x, V), s)) =
      T.dec (x, (fromTp (G, (V, s))))
    let rec fromConDec =
      function
      | ConDec (c, parent, i, _, V, I.Type) ->
          SOME (T.objdec (c, (fromTp (I.Null, (V, I.id)))))
      | _ -> NONE
    let ((fromConDec)(* from typecheck.fun *)(* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *)
      (* no case for FVar, Skonst *)(* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
      (* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *)(* see also: print.fun *)
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
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (G, (V, s)))
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
