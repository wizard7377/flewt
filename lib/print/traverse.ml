
module type TRAVERSER  =
  sig
    type nonrec tp
    type nonrec obj
    type nonrec head
    type nonrec spine
    type nonrec dec
    type nonrec condec
    val atom : head -> spine -> tp
    val arrow : tp -> tp -> tp
    val pi : dec -> tp -> tp
    val root : head -> spine -> tp -> obj
    val lam : dec -> obj -> obj
    val bvar : string -> head
    val const : string list -> string -> head
    val def : string list -> string -> head
    val nils : spine
    val app : obj -> spine -> spine
    val dec : string -> tp -> dec
    val objdec : string -> tp -> condec
  end
module type TRAVERSE  =
  sig
    module Traverser : TRAVERSER
    exception Error of string 
    val fromConDec : IntSyn.__ConDec -> Traverser.condec option
    val const : string -> Traverser.condec
  end;;




module Traverse(Traverse:sig
                           module Whnf : WHNF
                           module Names : NAMES
                           module Traverser' : TRAVERSER
                         end) : TRAVERSE =
  struct
    module Traverser = Traverser'
    exception Error of string 
    module I = IntSyn
    module T = Traverser
    let rec inferConW __0__ __1__ =
      match (__0__, __1__) with
      | (__G, BVar k') ->
          let Dec (_, __V) = I.ctxDec (__G, k') in Whnf.whnf (__V, I.id)
      | (__G, Const c) -> ((I.constType c), I.id)
      | (__G, Def d) -> ((I.constType d), I.id)
    let rec fromHead __2__ __3__ =
      match (__2__, __3__) with
      | (__G, BVar n) -> T.bvar (Names.bvarName (__G, n))
      | (__G, Const cid) ->
          let Qid (ids, id) = Names.constQid cid in T.const (ids, id)
      | (__G, Def cid) ->
          let Qid (ids, id) = Names.constQid cid in T.def (ids, id)
      | _ -> raise (Error "Head not recognized")(* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *)
      (* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
    let rec impCon =
      function
      | Const cid -> I.constImp cid
      | Def cid -> I.constImp cid
      | _ -> 0(*| imps (I.Skonst (cid)) = I.constImp (cid) *)
    let rec fromTpW __4__ __5__ =
      match (__4__, __5__) with
      | (__G, (Root (__C, __S), s)) ->
          T.atom
            ((fromHead (__G, __C)),
              (fromSpine
                 ((impCon __C), __G, (__S, s), (inferConW (__G, __C)))))
      | (__G, (Pi (((Dec (_, __V1) as D), I.No), __V2), s)) ->
          T.arrow
            ((fromTp (__G, (__V1, s))),
              (fromTp
                 ((I.Decl (__G, (I.decSub (__D, s)))), (__V2, (I.dot1 s)))))
      | (__G, (Pi ((__D, I.Maybe), __V2), s)) ->
          let __D' = Names.decUName (__G, __D) in
          T.pi
            ((fromDec (__G, (__D', s))),
              (fromTp
                 ((I.Decl (__G, (I.decSub (__D', s)))), (__V2, (I.dot1 s)))))
      | _ -> raise (Error "Type not recognized")
    let rec fromTp (__G) (__Vs) = fromTpW (__G, (Whnf.whnf __Vs))
    let rec fromObjW __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (__G, (Root (__C, __S), s), (__V, t)) ->
          T.root
            ((fromHead (__G, __C)),
              (fromSpine
                 ((impCon __C), __G, (__S, s), (inferConW (__G, __C)))),
              (fromTp (__G, (__V, t))))
      | (__G, (Lam (__D, __U), s), (Pi (_, __V), t)) ->
          let __D' = Names.decUName (__G, __D) in
          T.lam
            ((fromDec (__G, (__D', s))),
              (fromObj
                 ((I.Decl (__G, (I.decSub (__D', s)))), (__U, (I.dot1 s)),
                   (__V, (I.dot1 t)))))
      | _ -> raise (Error "Object not recognized")(* note: no case for EVars right now *)
    let rec fromObj (__G) (__Us) (Vt) =
      fromObjW (__G, (Whnf.whnf __Us), (Whnf.whnf Vt))
    let rec fromSpine __9__ __10__ __11__ __12__ =
      match (__9__, __10__, __11__, __12__) with
      | (i, __G, (I.Nil, s), Vt) -> T.nils
      | (i, __G, (SClo (__S, s'), s), Vt) ->
          fromSpine (i, __G, (__S, (I.comp (s', s))), Vt)
      | (i, __G, (App (__U, __S), s), (Pi ((Dec (_, __V1), _), __V2), t)) ->
          ((if i > 0
            then
              fromSpine
                ((i - 1), __G, (__S, s),
                  (Whnf.whnf (__V2, (I.Dot ((I.Exp (I.EClo (__U, s))), t)))))
            else
              T.app
                ((fromObj (__G, (__U, s), (__V1, t))),
                  (fromSpine
                     (i, __G, (__S, s),
                       (Whnf.whnf
                          (__V2, (I.Dot ((I.Exp (I.EClo (__U, s))), t))))))))
          (* drop implicit arg *))
    let rec fromDec (__G) (Dec (Some x, __V), s) =
      T.dec (x, (fromTp (__G, (__V, s))))
    let rec fromConDec =
      function
      | ConDec (c, parent, i, _, __V, I.Type) ->
          Some (T.objdec (c, (fromTp (I.Null, (__V, I.id)))))
      | _ -> NONE
    let fromConDec = fromConDec
    let rec const name =
      let qid =
        match Names.stringToQid name with
        | NONE -> raise (Error ("Malformed qualified identifier " ^ name))
        | Some qid -> qid in
      let cidOpt = Names.constLookup qid in
      let rec getConDec =
        function
        | NONE ->
            raise
              (Error ((^) "Undeclared identifier " Names.qidToString qid))
        | Some cid -> IntSyn.sgnLookup cid in
      let conDec = getConDec cidOpt in
      let _ = Names.varReset IntSyn.Null in
      let rec result =
        function
        | NONE -> raise (Error "Wrong kind of declaration")
        | Some r -> r in
      result (fromConDec conDec)
  end ;;
