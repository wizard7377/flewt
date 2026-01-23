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
    module Traverser : TRAVERSER
    exception Error of string 
    val fromConDec : IntSyn.conDec_ -> Traverser.condec option
    val const : string -> Traverser.condec
  end


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
    let rec inferConW =
      begin function
      | (g_, BVar k') ->
          let Dec (_, v_) = I.ctxDec (g_, k') in Whnf.whnf (v_, I.id)
      | (g_, Const c) -> ((I.constType c), I.id)
      | (g_, Def d) -> ((I.constType d), I.id) end
    let rec fromHead =
      begin function
      | (g_, BVar n) -> T.bvar (Names.bvarName (g_, n))
      | (g_, Const cid) ->
          let Qid (ids, id) = Names.constQid cid in T.const (ids, id)
      | (g_, Def cid) ->
          let Qid (ids, id) = Names.constQid cid in T.def (ids, id)
      | _ -> raise (Error "Head not recognized") end(* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *)
    (* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
  let rec impCon =
    begin function
    | Const cid -> I.constImp cid
    | Def cid -> I.constImp cid
    | _ -> 0 end(*| imps (I.Skonst (cid)) = I.constImp (cid) *)
let rec fromTpW =
  begin function
  | (g_, (Root (c_, s_), s)) ->
      T.atom
        ((fromHead (g_, c_)),
          (fromSpine ((impCon c_), g_, (s_, s), (inferConW (g_, c_)))))
  | (g_, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s)) ->
      T.arrow
        ((fromTp (g_, (v1_, s))),
          (fromTp ((I.Decl (g_, (I.decSub (d_, s)))), (v2_, (I.dot1 s)))))
  | (g_, (Pi ((d_, I.Maybe), v2_), s)) ->
      let d'_ = Names.decUName (g_, d_) in
      T.pi
        ((fromDec (g_, (d'_, s))),
          (fromTp ((I.Decl (g_, (I.decSub (d'_, s)))), (v2_, (I.dot1 s)))))
  | _ -> raise (Error "Type not recognized") end
let rec fromTp (g_, vs_) = fromTpW (g_, (Whnf.whnf vs_))
let rec fromObjW =
  begin function
  | (g_, (Root (c_, s_), s), (v_, t)) ->
      T.root
        ((fromHead (g_, c_)),
          (fromSpine ((impCon c_), g_, (s_, s), (inferConW (g_, c_)))),
          (fromTp (g_, (v_, t))))
  | (g_, (Lam (d_, u_), s), (Pi (_, v_), t)) ->
      let d'_ = Names.decUName (g_, d_) in
      T.lam
        ((fromDec (g_, (d'_, s))),
          (fromObj
             ((I.Decl (g_, (I.decSub (d'_, s)))), (u_, (I.dot1 s)),
               (v_, (I.dot1 t)))))
  | _ -> raise (Error "Object not recognized") end(* note: no case for EVars right now *)
let rec fromObj (g_, us_, Vt) =
  fromObjW (g_, (Whnf.whnf us_), (Whnf.whnf Vt))
let rec fromSpine =
  begin function
  | (i, g_, (I.Nil, s), Vt) -> T.nils
  | (i, g_, (SClo (s_, s'), s), Vt) ->
      fromSpine (i, g_, (s_, (I.comp (s', s))), Vt)
  | (i, g_, (App (u_, s_), s), (Pi ((Dec (_, v1_), _), v2_), t)) ->
      ((if i > 0
        then
          begin fromSpine
                  ((i - 1), g_, (s_, s),
                    (Whnf.whnf (v2_, (I.Dot ((I.Exp (I.EClo (u_, s))), t))))) end
      else begin
        T.app
          ((fromObj (g_, (u_, s), (v1_, t))),
            (fromSpine
               (i, g_, (s_, s),
                 (Whnf.whnf (v2_, (I.Dot ((I.Exp (I.EClo (u_, s))), t))))))) end)
  (* drop implicit arg *)) end
let rec fromDec (g_, (Dec (Some x, v_), s)) =
  T.dec (x, (fromTp (g_, (v_, s))))
let rec fromConDec =
  begin function
  | ConDec (c, parent, i, _, v_, I.Type) ->
      Some (T.objdec (c, (fromTp (I.Null, (v_, I.id)))))
  | _ -> None end
let fromConDec = fromConDec
let rec const name =
  let qid =
    begin match Names.stringToQid name with
    | None -> raise (Error ("Malformed qualified identifier " ^ name))
    | Some qid -> qid end in
let cidOpt = Names.constLookup qid in
let rec getConDec =
  begin function
  | None ->
      raise (Error ((^) "Undeclared identifier " Names.qidToString qid))
  | Some cid -> IntSyn.sgnLookup cid end in
let conDec = getConDec cidOpt in
let _ = Names.varReset IntSyn.Null in
let rec result =
  begin function
  | None -> raise (Error "Wrong kind of declaration")
  | Some r -> r end in
result (fromConDec conDec) end
