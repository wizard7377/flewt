module type UNIQUE  =
  sig
    exception Error of string 
    val checkUnique : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
  end


module Unique(Unique:sig
                       module Global : GLOBAL
                       module Whnf : WHNF
                       module Abstract : ABSTRACT
                       module Unify : UNIFY
                       module Constraints : CONSTRAINTS
                       module UniqueTable : MODETABLE
                       module UniqueCheck : MODECHECK
                       module Index : INDEX
                       module Subordinate : SUBORDINATE
                       module WorldSyn : WORLDSYN
                       module Names : NAMES
                       module Print : PRINT
                       module TypeCheck : TYPECHECK
                       module Timers : TIMERS
                     end) : UNIQUE =
  struct
    exception Error of string 
    module I = IntSyn
    module M = ModeSyn
    module W = WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names
    module T = Tomega
    let rec chatter chlev f =
      if !Global.chatter >= chlev then begin print (f ()) end
      else begin () end
  let rec cName cid = N.qidToString (N.constQid cid)
  let rec pName =
    begin function
    | (cid, Some x) -> (((^) "#" cName cid) ^ "_") ^ x
    | (cid, None) -> ((^) "#" cName cid) ^ "_?" end
let rec instEVars =
  begin function
  | (g_, (Pi ((Dec (_, v1_), _), v2_), s)) ->
      let x1_ = I.newEVar (g_, (I.EClo (v1_, s))) in
      instEVars (g_, (v2_, (I.Dot ((I.Exp x1_), s))))
  | (g_, ((Root _, _) as vs_)) -> vs_ end
let rec createEVarSub =
  begin function
  | (g_, I.Null) -> I.Shift (I.ctxLength g_)
  | (g_, Decl (g'_, (Dec (_, v_) as d_))) ->
      let s = createEVarSub (g_, g'_) in
      let v'_ = I.EClo (v_, s) in
      let x_ = I.newEVar (g_, v'_) in I.Dot ((I.Exp x_), s) end
let rec unifiable (g_, (u_, s), (u'_, s')) =
  Unify.unifiable (g_, (u_, s), (u'_, s'))
let rec unifiableSpines =
  begin function
  | (g_, (I.Nil, s), (I.Nil, s'), M.Mnil) -> true
  | (g_, (App (u1_, s2_), s), (App (U1', S2'), s'), Mapp
     (Marg (M.Plus, _), ms2)) ->
      (unifiable (g_, (u1_, s), (U1', s'))) &&
        (unifiableSpines (g_, (s2_, s), (S2', s'), ms2))
  | (g_, (App (u1_, s2_), s), (App (U1', S2'), s'), Mapp
     (Marg (mode, _), ms2)) -> unifiableSpines (g_, (s2_, s), (S2', s'), ms2) end
(* skip output ( - ) or ignore ( * ) arguments *)
let rec unifiableRoots
  (g_, (Root (Const a, s_), s), (Root (Const a', s'_), s'), ms) =
  (a = a') && (unifiableSpines (g_, (s_, s), (s'_, s'), ms))
let rec checkNotUnifiableTypes (g_, vs_, vs'_, ms, (bx, by)) =
  begin chatter 6
          (begin function
           | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") pName by) ^ "\n" end);
  CSManager.trail
    (begin function
     | () ->
         if unifiableRoots (g_, vs_, vs'_, ms)
         then
           begin raise
                   (Error
                      (((^) (((^) "Blocks " pName bx) ^ " and ") pName by) ^
                         " overlap")) end
         else begin () end end) end
let rec checkDiffConstConst (Const cid, Const cid', ms) =
  let _ =
    chatter 6
      (begin function
       | () -> ((^) (((^) "?- " cName cid) ^ " ~ ") cName cid') ^ "\n" end) in
let vs_ = instEVars (I.Null, ((I.constType cid), I.id)) in
let vs'_ = instEVars (I.Null, ((I.constType cid'), I.id)) in
let _ =
  CSManager.trail
    (begin function
     | () ->
         if unifiableRoots (I.Null, vs_, vs'_, ms)
         then
           begin raise
                   (Error
                      (((^) (((^) "Constants " cName cid) ^ " and ") cName
                          cid')
                         ^ " overlap\n")) end
         else begin () end end) in
()
let rec checkUniqueConstConsts =
  begin function
  | (c, [], ms) -> ()
  | (c, c'::cs', ms) ->
      (begin checkDiffConstConst (c, c', ms);
       checkUniqueConstConsts (c, cs', ms) end) end
let rec checkUniqueConsts =
  begin function
  | ([], ms) -> ()
  | (c::cs, ms) ->
      (begin checkUniqueConstConsts (c, cs, ms); checkUniqueConsts (cs, ms) end) end
let rec checkDiffBlocksInternal =
  begin function
  | (g_, vs_, (t, []), (a, ms), bx) -> ()
  | (g_, (v_, s), (t, (Dec (yOpt, v'_) as d_)::piDecs), (a, ms), (b, xOpt))
      ->
      let a' = I.targetFam v'_ in
      let _ =
        if a = a'
        then
          begin checkNotUnifiableTypes
                  (g_, (v_, s), (instEVars (g_, (v'_, t))), ms,
                    ((b, xOpt), (b, yOpt))) end
        else begin () end in
    checkDiffBlocksInternal
      ((I.Decl (g_, d_)), (v_, (I.comp (s, I.shift))), ((I.dot1 t), piDecs),
        (a, ms), (b, xOpt)) end
let rec checkUniqueBlockInternal' =
  begin function
  | (g_, (t, []), (a, ms), b) -> ()
  | (g_, (t, (Dec (xOpt, v_) as d_)::piDecs), (a, ms), b) ->
      let a' = I.targetFam v_ in
      let _ =
        if a = a'
        then
          begin let (v'_, s) = instEVars (g_, (v_, t)) in
                checkDiffBlocksInternal
                  ((I.Decl (g_, d_)), (v'_, (I.comp (s, I.shift))),
                    ((I.dot1 t), piDecs), (a, ms), (b, xOpt)) end
        else begin () end in
    checkUniqueBlockInternal'
      ((I.Decl (g_, d_)), ((I.dot1 t), piDecs), (a, ms), b) end
let rec checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
  let t = createEVarSub (I.Null, Gsome) in
  ((checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b))
    (* . |- t : Gsome *))
let rec checkUniqueBlockConsts =
  begin function
  | (g_, vs_, [], ms, bx) -> ()
  | (g_, vs_, (Const cid)::cs, ms, bx) ->
      let _ =
        chatter 6
          (begin function
           | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") cName cid) ^ "\n" end) in
    let vs'_ = instEVars (g_, ((I.constType cid), I.id)) in
    let _ =
      CSManager.trail
        (begin function
         | () ->
             if unifiableRoots (g_, vs_, vs'_, ms)
             then
               begin raise
                       (Error
                          (((^) (((^) "Block " pName bx) ^ " and constant ")
                              cName cid)
                             ^ " overlap")) end
             else begin () end end) in
checkUniqueBlockConsts (g_, vs_, cs, ms, bx) end
let rec checkUniqueBlockBlock =
  begin function
  | (g_, vs_, (t, []), (a, ms), (bx, b')) -> ()
  | (g_, (v_, s), (t, (Dec (yOpt, v'_) as d_)::piDecs), (a, ms), (bx, b')) ->
      let a' = I.targetFam v'_ in
      let _ =
        if a = a'
        then
          begin checkNotUnifiableTypes
                  (g_, (v_, s), (instEVars (g_, (v'_, t))), ms,
                    (bx, (b', yOpt))) end
        else begin () end in
    checkUniqueBlockBlock
      ((I.Decl (g_, d_)), (v_, (I.comp (s, I.shift))), ((I.dot1 t), piDecs),
        (a, ms), (bx, b')) end
let rec checkUniqueBlockBlocks =
  begin function
  | (g_, vs_, [], (a, ms), bx) -> ()
  | (g_, vs_, b::bs, (a, ms), bx) ->
      let (Gsome, piDecs) = I.constBlock b in
      let t = createEVarSub (g_, Gsome) in
      let _ = checkUniqueBlockBlock (g_, vs_, (t, piDecs), (a, ms), (bx, b)) in
      checkUniqueBlockBlocks (g_, vs_, bs, (a, ms), bx) end
let rec checkUniqueBlock' =
  begin function
  | (g_, (t, []), bs, cs, (a, ms), b) -> ()
  | (g_, (t, (Dec (xOpt, v_) as d_)::piDecs), bs, cs, (a, ms), b) ->
      let a' = I.targetFam v_ in
      let _ =
        if a = a'
        then
          begin let (v'_, s) = instEVars (g_, (v_, t)) in
                let _ =
                  checkUniqueBlockBlocks
                    (g_, (v'_, s), bs, (a, ms), (b, xOpt)) in
                let _ =
                  checkUniqueBlockConsts (g_, (v'_, s), cs, ms, (b, xOpt)) in
                () end
        else begin () end in
    checkUniqueBlock'
      ((I.Decl (g_, d_)), ((I.dot1 t), piDecs), bs, cs, (a, ms), b) end
let rec checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) =
  let t = createEVarSub (I.Null, Gsome) in
  checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
let rec checkUniqueWorlds =
  begin function
  | ([], cs, (a, ms)) -> ()
  | (b::bs, cs, (a, ms)) ->
      (begin checkUniqueBlockInternal ((I.constBlock b), (a, ms), b);
       checkUniqueBlock ((I.constBlock b), (b :: bs), cs, (a, ms), b);
       checkUniqueWorlds (bs, cs, (a, ms)) end) end
let rec checkNoDef a =
  begin match I.sgnLookup a with
  | ConDef _ ->
      raise
        (Error
           (((^) "Uniqueness checking " cName a) ^
              ":\ntype family must not be defined."))
  | _ -> () end
let rec checkUnique (a, ms) =
  let _ =
    chatter 4
      (begin function
       | () -> ((^) "Uniqueness checking family " cName a) ^ "\n" end) in
let _ = checkNoDef a in
let _ =
  begin try Subordinate.checkNoDef a
  with
  | Error msg ->
      raise (Error ((((^) "Coverage checking " cName a) ^ ":\n") ^ msg)) end in
let cs = Index.lookup a in
let Worlds bs =
  ((begin try W.lookup a
    with
    | Error msg ->
        raise
          (Error
             ((^) (((^) "Uniqueness checking " cName a) ^
                     ":\nMissing world declaration for ")
                cName a)) end)
  (* worlds declarations for a *)) in
let _ =
  begin try checkUniqueConsts (cs, ms)
  with
  | Error msg ->
      raise (Error ((((^) "Uniqueness checking " cName a) ^ ":\n") ^ msg)) end in
let _ =
  begin try checkUniqueWorlds (bs, cs, (a, ms))
  with
  | Error msg ->
      raise (Error ((((^) "Uniqueness checking " cName a) ^ ":\n") ^ msg)) end in
let _ =
  chatter 5
    (begin function
     | () -> ((^) "Checking uniqueness modes for family " cName a) ^ "\n" end) in
let _ =
  begin try UniqueCheck.checkMode (a, ms)
  with
  | Error msg ->
      raise
        (Error ((((^) "Uniqueness mode checking " cName a) ^ ":\n") ^ msg)) end in
((())(* lookup constants defining a *)) end



module UniqueTable =
  (ModeTable)(struct module Table = IntRedBlackTree end)
module UniqueCheck =
  (ModeCheck)(struct
                     module ModeTable = UniqueTable
                     module Whnf = Whnf
                     module Index = Index
                     module Origins = Origins
                   end)
module Unique =
  (Unique)(struct
                  module Global = Global
                  module Whnf = Whnf
                  module Abstract = Abstract
                  module Unify = UnifyTrail
                  module Constraints = Constraints
                  module UniqueTable = UniqueTable
                  module UniqueCheck = UniqueCheck
                  module Index = Index
                  module Subordinate = Subordinate
                  module WorldSyn = WorldSyn
                  module Names = Names
                  module Print = Print
                  module TypeCheck = TypeCheck
                  module Timers = Timers
                end)