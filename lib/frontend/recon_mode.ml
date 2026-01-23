module type EXTMODES  =
  sig
    module ExtSyn : EXTSYN
    type nonrec mode
    val plus : Paths.region -> mode
    val star : Paths.region -> mode
    val minus : Paths.region -> mode
    val minus1 : Paths.region -> mode
    type nonrec modedec
    module Short :
    sig
      type nonrec mterm
      type nonrec mspine
      val mnil : Paths.region -> mspine
      val mapp : ((mode * string option) * mspine) -> mspine
      val mroot : (string list * string * Paths.region * mspine) -> mterm
      val toModedec : mterm -> modedec
    end
    module Full :
    sig
      type nonrec mterm
      val mroot : (ExtSyn.term * Paths.region) -> mterm
      val mpi : (mode * ExtSyn.dec * mterm) -> mterm
      val toModedec : mterm -> modedec
    end
  end
module type RECON_MODE  =
  sig
    include EXTMODES
    exception Error of string 
    val modeToMode :
      modedec -> ((IntSyn.cid * ModeSyn.modeSpine_) * Paths.region)
  end


module ReconMode(ReconMode:sig
                             module Global : GLOBAL
                             module Whnf : WHNF
                             module Names : NAMES
                             module ModePrint : MODEPRINT
                             module ModeDec : MODEDEC
                             module ReconTerm' : RECON_TERM
                           end) : RECON_MODE =
  struct
    module ExtSyn = ReconTerm'
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    module M = ModeSyn
    module I = IntSyn
    module T = ExtSyn
    module P = Paths
    type nonrec mode = (M.mode_ * P.region)
    let rec plus r = (M.Plus, r)
    let rec star r = (M.Star, r)
    let rec minus r = (M.Minus, r)
    let rec minus1 r = (M.Minus1, r)
    type nonrec modedec = ((I.cid * M.modeSpine_) * P.region)
    module Short =
      struct
        type nonrec mterm = ((I.cid * M.modeSpine_) * P.region)
        type nonrec mspine = (M.modeSpine_ * P.region)
        let rec mnil r = (M.Mnil, r)
        let rec mapp (((m, r1), name), (mS, r2)) =
          ((M.Mapp ((M.Marg (m, name)), mS)), (P.join (r1, r2)))
        let rec mroot (ids, id, r1, (mS, r2)) =
          let r = P.join (r1, r2) in
          let qid = Names.Qid (ids, id) in
          begin match Names.constLookup qid with
          | None ->
              error
                (r,
                  (((^) "Undeclared identifier " Names.qidToString
                      (valOf (Names.constUndef qid)))
                     ^ " in mode declaration"))
          | Some cid -> ((cid, (ModeDec.shortToFull (cid, mS, r))), r) end
        let rec toModedec nmS = nmS end
    module Full =
      struct
        type nonrec mterm =
          (T.dec I.ctx_ * M.mode_ I.ctx_) ->
            ((I.cid * M.modeSpine_) * P.region)
        let rec mpi ((m, _), d, t) (g, d_) =
          t ((I.Decl (g, d)), (I.Decl (d_, m)))
        let rec mroot (tm, r) (g, d_) =
          let JWithCtx (g_, JOf ((v_, _), _, _)) =
            T.recon (T.jwithctx (g, (T.jof (tm, (T.typ r))))) in
          let _ = T.checkErrors r in
          let rec convertSpine =
            begin function
            | I.Nil -> M.Mnil
            | App (u_, s_) ->
                let k =
                  begin try Whnf.etaContract u_
                  with
                  | Whnf.Eta ->
                      error
                        (r,
                          (("Argument " ^ (Print.expToString (g_, u_))) ^
                             " not a variable")) end in
              let Dec (name, _) = I.ctxLookup (g_, k) in
              let mode = I.ctxLookup (d_, k) in
              ((M.Mapp ((M.Marg (mode, name)), (convertSpine s_)))
                (* print U? -fp *)(* yes, print U. -gaw *)) end in
          let rec convertExp =
            begin function
            | Root (Const a, s_) -> (a, (convertSpine s_))
            | Root (Def d, s_) -> (d, (convertSpine s_))
            | _ -> error (r, "Call pattern not an atomic type") end(* error is signalled later in ModeDec.checkFull *) in
          let (a, mS) = convertExp (Whnf.normalize (v_, I.id)) in
          ((begin ModeDec.checkFull (a, mS, r); ((a, mS), r) end)
            (* convert term spine to mode spine *)(* Each argument must be contractible to variable *)
            (* convert root expression to head constant and mode spine *)
            (* convertExp (I.Root (I.Skonst _, S)) can't occur *))
  let rec toModedec t =
    let _ = Names.varReset I.Null in let t' = t (I.Null, I.Null) in t' end
let rec modeToMode (m, r) = (m, r)
type nonrec mode = mode
let plus = plus
let star = star
let minus = minus
let minus1 = minus1
type nonrec modedec = modedec
module Short = Short
module Full = Full
let modeToMode = modeToMode end
