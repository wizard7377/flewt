
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
    include
      ((EXTMODES)(* External Syntax of Mode Declarations *)
      (* Author: Carsten Schuermann *)(*! structure Paths : PATHS  !*)
      (* signature EXTMODES *)(*! structure ModeSyn : MODESYN !*))
    exception Error of string 
    val modeToMode :
      modedec -> ((IntSyn.cid * ModeSyn.__ModeSpine) * Paths.region)
  end;;




module ReconMode(ReconMode:sig
                             module Global : GLOBAL
                             module Whnf : WHNF
                             module Names : NAMES
                             module ModePrint : MODEPRINT
                             module ModeDec : MODEDEC
                             module ReconTerm' :
                             ((RECON_TERM)(* Reconstructing Mode Declarations *)
                             (* Author: Carsten Schuermann *)(*! structure ModeSyn' : MODESYN !*)
                             (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
                             (*! structure Paths' : PATHS !*)(*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                             (*! sharing ModePrint.ModeSyn = ModeSyn' !*))
                           end) : RECON_MODE =
  struct
    module ExtSyn =
      ((ReconTerm')(*! sharing ReconTerm'.IntSyn = ModeSyn'.IntSyn !*)
      (*! sharing ReconTerm'.Paths = Paths' !*)(*! structure ModeSyn = ModeSyn' !*))
    exception Error of
      ((string)(*! structure Paths = Paths' !*)) 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    module M = ModeSyn
    module I = IntSyn
    module T = ExtSyn
    module P = Paths
    type nonrec mode = (M.__Mode * P.region)
    let rec plus r = (M.Plus, r)
    let rec star r = (M.Star, r)
    let rec minus r = (M.Minus, r)
    let rec minus1 r = (M.Minus1, r)
    type nonrec modedec = ((I.cid * M.__ModeSpine) * P.region)
    module Short =
      struct
        type nonrec mterm = ((I.cid * M.__ModeSpine) * P.region)
        type nonrec mspine = (M.__ModeSpine * P.region)
        let rec mnil r = (M.Mnil, r)
        let rec mapp (((m, r1), name), (mS, r2)) =
          ((M.Mapp ((M.Marg (m, name)), mS)), (P.join (r1, r2)))
        let rec mroot (ids, id, r1, (mS, r2)) =
          let r = P.join (r1, r2) in
          let qid = Names.Qid (ids, id) in
          match Names.constLookup qid with
          | NONE ->
              error
                (r,
                  (((^) "Undeclared identifier " Names.qidToString
                      (valOf (Names.constUndef qid)))
                     ^ " in mode declaration"))
          | SOME cid -> ((cid, (ModeDec.shortToFull (cid, mS, r))), r)
        let rec toModedec nmS = nmS
      end
    module Full =
      struct
        type nonrec mterm =
          (T.dec I.__Ctx * M.__Mode I.__Ctx) ->
            ((I.cid * M.__ModeSpine) * P.region)
        let rec mpi ((m, _), d, t) (g, D) =
          t ((I.Decl (g, d)), (I.Decl (D, m)))
        let rec mroot (tm, r) (g, D) =
          let JWithCtx (g, JOf ((V, _), _, _)) =
            T.recon (T.jwithctx (g, (T.jof (tm, (T.typ r))))) in
          let _ = T.checkErrors r in
          let convertSpine =
            function
            | I.Nil -> M.Mnil
            | App (U, S) ->
                let k =
                  try Whnf.etaContract U
                  with
                  | Whnf.Eta ->
                      error
                        (r,
                          (("Argument " ^ (Print.expToString (g, U))) ^
                             " not a variable")) in
                let Dec (name, _) = I.ctxLookup (g, k) in
                let mode = I.ctxLookup (D, k) in
                M.Mapp ((M.Marg (mode, name)), (convertSpine S)) in
          let convertExp =
            function
            | Root (Const a, S) -> (a, (convertSpine S))
            | Root (Def d, S) -> (d, (convertSpine S))
            | _ -> error (r, "Call pattern not an atomic type") in
          let (a, mS) = convertExp (Whnf.normalize (V, I.id)) in
          ModeDec.checkFull (a, mS, r); ((a, mS), r)
        let rec toModedec t =
          let _ = Names.varReset I.Null in let t' = t (I.Null, I.Null) in t'
      end
    let rec modeToMode (m, r) = (m, r)
    type nonrec mode =
      ((mode)(* structure Full *)(* convertExp (I.Root (I.Skonst _, S)) can't occur *)
      (* error is signalled later in ModeDec.checkFull *)
      (* convert root expression to head constant and mode spine *)
      (* yes, print U. -gaw *)(* print U? -fp *)
      (* Each argument must be contractible to variable *)
      (* convert term spine to mode spine *)(* structure Short *))
    let plus = plus
    let star = star
    let minus = minus
    let minus1 = minus1
    type nonrec modedec = modedec
    module Short = Short
    module Full = Full
    let modeToMode = modeToMode
  end ;;
