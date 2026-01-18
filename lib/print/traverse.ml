
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
(* Generic Traversal Intended for Language-Specific Printing *)
(* Author: Frank Pfenning *)
(* type kind *)
(* propagate type to every root *)
(* no evar, skonst, or fvar *)
(* val famdec : string * kind -> condec *)
(* val objdef : string * obj * tp -> condec *)
(* val famdef : string * tp * kind -> condec *)
(* val skodec : string * tp -> condec *)
(* signature TRAVERSER *)
module type TRAVERSE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    module Traverser : TRAVERSER
    exception Error of string 
    val fromConDec : IntSyn.__ConDec -> Traverser.condec option
    val const : string -> Traverser.condec
  end;;




module Traverse(Traverse:sig
                           (*! structure IntSyn' : INTSYN !*)
                           module Whnf : WHNF
                           module Names : NAMES
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Names.IntSyn = IntSyn' !*)
                           module Traverser' : TRAVERSER
                         end) : TRAVERSE =
  struct
    (* shares types from Traverser' *)
    (*! structure IntSyn = IntSyn' !*)
    module Traverser = Traverser'
    exception Error of string 
    module I = IntSyn
    module T = Traverser
    let rec inferConW =
      function
      | (__g, BVar k') ->
          let Dec (_, __v) = I.ctxDec (__g, k') in Whnf.whnf (__v, I.id)
      | (__g, Const c) -> ((I.constType c), I.id)
      | (__g, Def d) -> ((I.constType d), I.id)
    let rec fromHead =
      function
      | (__g, BVar n) -> T.bvar (Names.bvarName (__g, n))
      | (__g, Const cid) ->
          let Qid (ids, id) = Names.constQid cid in T.const (ids, id)
      | (__g, Def cid) ->
          let Qid (ids, id) = Names.constQid cid in T.def (ids, id)
      | _ -> raise (Error "Head not recognized")
    let rec impCon =
      function
      | Const cid -> I.constImp cid
      | Def cid -> I.constImp cid
      | _ -> 0
    let rec fromTpW =
      function
      | (__g, (Root (C, S), s)) ->
          T.atom
            ((fromHead (__g, C)),
              (fromSpine ((impCon C), __g, (S, s), (inferConW (__g, C)))))
      | (__g, (Pi (((Dec (_, V1) as __d), I.No), V2), s)) ->
          T.arrow
            ((fromTp (__g, (V1, s))),
              (fromTp ((I.Decl (__g, (I.decSub (__d, s)))), (V2, (I.dot1 s)))))
      | (__g, (Pi ((__d, I.Maybe), V2), s)) ->
          let __d' = Names.decUName (__g, __d) in
          T.pi
            ((fromDec (__g, (__d', s))),
              (fromTp ((I.Decl (__g, (I.decSub (__d', s)))), (V2, (I.dot1 s)))))
      | _ -> raise (Error "Type not recognized")
    let rec fromTp (__g, __Vs) = fromTpW (__g, (Whnf.whnf __Vs))
    let rec fromObjW =
      function
      | (__g, (Root (C, S), s), (__v, t)) ->
          T.root
            ((fromHead (__g, C)),
              (fromSpine ((impCon C), __g, (S, s), (inferConW (__g, C)))),
              (fromTp (__g, (__v, t))))
      | (__g, (Lam (__d, __u), s), (Pi (_, __v), t)) ->
          let __d' = Names.decUName (__g, __d) in
          T.lam
            ((fromDec (__g, (__d', s))),
              (fromObj
                 ((I.Decl (__g, (I.decSub (__d', s)))), (__u, (I.dot1 s)),
                   (__v, (I.dot1 t)))))
      | _ -> raise (Error "Object not recognized")
    let rec fromObj (__g, __Us, Vt) =
      fromObjW (__g, (Whnf.whnf __Us), (Whnf.whnf Vt))
    let rec fromSpine =
      function
      | (i, __g, (I.Nil, s), Vt) -> T.nils
      | (i, __g, (SClo (S, s'), s), Vt) ->
          fromSpine (i, __g, (S, (I.comp (s', s))), Vt)
      | (i, __g, (App (__u, S), s), (Pi ((Dec (_, V1), _), V2), t)) ->
          if i > 0
          then
            fromSpine
              ((i - 1), __g, (S, s),
                (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (__u, s))), t)))))
          else
            T.app
              ((fromObj (__g, (__u, s), (V1, t))),
                (fromSpine
                   (i, __g, (S, s),
                     (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (__u, s))), t)))))))
    let rec fromDec (__g, (Dec (Some x, __v), s)) =
      T.dec (x, (fromTp (__g, (__v, s))))
    let rec fromConDec =
      function
      | ConDec (c, parent, i, _, __v, I.Type) ->
          Some (T.objdec (c, (fromTp (I.Null, (__v, I.id)))))
      | _ -> None
    (* from typecheck.fun *)
    (* inferCon (__g, C) = __v'

     Invariant:
     If    __g |- C : __v
     and  (C  doesn't contain FVars)
     then  __g' |- __v' : __l      (for some level __l)
     and   __g |- __v = __v' : __l
     else exception Error is raised.
  *)
    (* no case for FVar, Skonst *)
    (* | fromHead (__g, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
    (* | fromHead (__g, FVar (name, _, _)) = T.fvar (name) *)
    (* see also: print.fun *)
    (*| imps (I.Skonst (cid)) = I.constImp (cid) *)
    (* see also: print.fun *)
    (*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (__u, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)
    (* note: no case for EVars right now *)
    (* drop implicit arg *)
    (* None should not occur because of call to decName *)
    (*
    | fromDec (__g, (I.Dec (None, __v), s)) =
        T.dec ("_", fromTp (__g, (__v, s)))
    *)
    (* ignore a : K, d : A = M, b : K = A, and skolem constants *)
    let fromConDec = fromConDec
    let rec const name =
      let qid =
        match Names.stringToQid name with
        | None -> raise (Error ("Malformed qualified identifier " ^ name))
        | Some qid -> qid in
      let cidOpt = Names.constLookup qid in
      let rec getConDec =
        function
        | None ->
            raise
              (Error ((^) "Undeclared identifier " Names.qidToString qid))
        | Some cid -> IntSyn.sgnLookup cid in
      let conDec = getConDec cidOpt in
      let _ = Names.varReset IntSyn.Null in
      let rec result =
        function
        | None -> raise (Error "Wrong kind of declaration")
        | Some r -> r in
      result (fromConDec conDec)
  end ;;
