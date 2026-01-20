
module type UNIQUE  =
  sig
    exception Error of string 
    val checkUnique : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
  end;;




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
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec cName cid = N.qidToString (N.constQid cid)
    let rec pName __0__ __1__ =
      match (__0__, __1__) with
      | (cid, Some x) -> (((^) "#" cName cid) ^ "_") ^ x
      | (cid, NONE) -> ((^) "#" cName cid) ^ "_?"
    let rec instEVars __2__ __3__ =
      match (__2__, __3__) with
      | (__G, (Pi ((Dec (_, __V1), _), __V2), s)) ->
          let __X1 = I.newEVar (__G, (I.EClo (__V1, s))) in
          instEVars (__G, (__V2, (I.Dot ((I.Exp __X1), s))))
      | (__G, ((Root _, _) as Vs)) -> __Vs
    let rec createEVarSub __4__ __5__ =
      match (__4__, __5__) with
      | (__G, I.Null) -> I.Shift (I.ctxLength __G)
      | (__G, Decl (__G', (Dec (_, __V) as D))) ->
          let s = createEVarSub (__G, __G') in
          let __V' = I.EClo (__V, s) in
          let __X = I.newEVar (__G, __V') in I.Dot ((I.Exp __X), s)
    let rec unifiable (__G) (__U, s) (__U', s') =
      Unify.unifiable (__G, (__U, s), (__U', s'))
    let rec unifiableSpines __6__ __7__ __8__ __9__ =
      match (__6__, __7__, __8__, __9__) with
      | (__G, (I.Nil, s), (I.Nil, s'), M.Mnil) -> true__
      | (__G, (App (__U1, __S2), s), (App (U1', S2'), s'), Mapp
         (Marg (M.Plus, _), ms2)) ->
          (unifiable (__G, (__U1, s), (U1', s'))) &&
            (unifiableSpines (__G, (__S2, s), (S2', s'), ms2))
      | (__G, (App (__U1, __S2), s), (App (U1', S2'), s'), Mapp
         (Marg (mode, _), ms2)) ->
          unifiableSpines (__G, (__S2, s), (S2', s'), ms2)(* skip output ( - ) or ignore ( * ) arguments *)
    let rec unifiableRoots (__G) (Root (Const a, __S), s)
      (Root (Const a', __S'), s') ms =
      (a = a') && (unifiableSpines (__G, (__S, s), (__S', s'), ms))
    let rec checkNotUnifiableTypes (__G) (__Vs) (__Vs') ms (bx, by) =
      chatter 6
        (fun () -> ((^) (((^) "?- " pName bx) ^ " ~ ") pName by) ^ "\n");
      CSManager.trail
        (fun () ->
           if unifiableRoots (__G, __Vs, __Vs', ms)
           then
             raise
               (Error
                  (((^) (((^) "Blocks " pName bx) ^ " and ") pName by) ^
                     " overlap"))
           else ())
    let rec checkDiffConstConst (Const cid) (Const cid') ms =
      let _ =
        chatter 6
          (fun () -> ((^) (((^) "?- " cName cid) ^ " ~ ") cName cid') ^ "\n") in
      let __Vs = instEVars (I.Null, ((I.constType cid), I.id)) in
      let __Vs' = instEVars (I.Null, ((I.constType cid'), I.id)) in
      let _ =
        CSManager.trail
          (fun () ->
             if unifiableRoots (I.Null, __Vs, __Vs', ms)
             then
               raise
                 (Error
                    (((^) (((^) "Constants " cName cid) ^ " and ") cName cid')
                       ^ " overlap\n"))
             else ()) in
      ()
    let rec checkUniqueConstConsts __10__ __11__ __12__ =
      match (__10__, __11__, __12__) with
      | (c, nil, ms) -> ()
      | (c, c'::cs', ms) ->
          (checkDiffConstConst (c, c', ms);
           checkUniqueConstConsts (c, cs', ms))
    let rec checkUniqueConsts __13__ __14__ =
      match (__13__, __14__) with
      | (nil, ms) -> ()
      | (c::cs, ms) ->
          (checkUniqueConstConsts (c, cs, ms); checkUniqueConsts (cs, ms))
    let rec checkDiffBlocksInternal __15__ __16__ __17__ __18__ __19__ =
      match (__15__, __16__, __17__, __18__, __19__) with
      | (__G, __Vs, (t, nil), (a, ms), bx) -> ()
      | (__G, (__V, s), (t, (Dec (yOpt, __V') as D)::piDecs), (a, ms),
         (b, xOpt)) ->
          let a' = I.targetFam __V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (__G, (__V, s), (instEVars (__G, (__V', t))), ms,
                  ((b, xOpt), (b, yOpt)))
            else () in
          checkDiffBlocksInternal
            ((I.Decl (__G, __D)), (__V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
    let rec checkUniqueBlockInternal' __20__ __21__ __22__ __23__ =
      match (__20__, __21__, __22__, __23__) with
      | (__G, (t, nil), (a, ms), b) -> ()
      | (__G, (t, (Dec (xOpt, __V) as D)::piDecs), (a, ms), b) ->
          let a' = I.targetFam __V in
          let _ =
            if a = a'
            then
              let (__V', s) = instEVars (__G, (__V, t)) in
              checkDiffBlocksInternal
                ((I.Decl (__G, __D)), (__V', (I.comp (s, I.shift))),
                  ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
            else () in
          checkUniqueBlockInternal'
            ((I.Decl (__G, __D)), ((I.dot1 t), piDecs), (a, ms), b)
    let rec checkUniqueBlockInternal (Gsome, piDecs) (a, ms) b =
      let t = createEVarSub (I.Null, Gsome) in
      ((checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b))
        (* . |- t : Gsome *))
    let rec checkUniqueBlockConsts __24__ __25__ __26__ __27__ __28__ =
      match (__24__, __25__, __26__, __27__, __28__) with
      | (__G, __Vs, nil, ms, bx) -> ()
      | (__G, __Vs, (Const cid)::cs, ms, bx) ->
          let _ =
            chatter 6
              (fun () ->
                 ((^) (((^) "?- " pName bx) ^ " ~ ") cName cid) ^ "\n") in
          let __Vs' = instEVars (__G, ((I.constType cid), I.id)) in
          let _ =
            CSManager.trail
              (fun () ->
                 if unifiableRoots (__G, __Vs, __Vs', ms)
                 then
                   raise
                     (Error
                        (((^) (((^) "Block " pName bx) ^ " and constant ")
                            cName cid)
                           ^ " overlap"))
                 else ()) in
          checkUniqueBlockConsts (__G, __Vs, cs, ms, bx)
    let rec checkUniqueBlockBlock __29__ __30__ __31__ __32__ __33__ =
      match (__29__, __30__, __31__, __32__, __33__) with
      | (__G, __Vs, (t, nil), (a, ms), (bx, b')) -> ()
      | (__G, (__V, s), (t, (Dec (yOpt, __V') as D)::piDecs), (a, ms),
         (bx, b')) ->
          let a' = I.targetFam __V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (__G, (__V, s), (instEVars (__G, (__V', t))), ms,
                  (bx, (b', yOpt)))
            else () in
          checkUniqueBlockBlock
            ((I.Decl (__G, __D)), (__V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (bx, b'))
    let rec checkUniqueBlockBlocks __34__ __35__ __36__ __37__ __38__ =
      match (__34__, __35__, __36__, __37__, __38__) with
      | (__G, __Vs, nil, (a, ms), bx) -> ()
      | (__G, __Vs, b::bs, (a, ms), bx) ->
          let (Gsome, piDecs) = I.constBlock b in
          let t = createEVarSub (__G, Gsome) in
          let _ =
            checkUniqueBlockBlock (__G, __Vs, (t, piDecs), (a, ms), (bx, b)) in
          checkUniqueBlockBlocks (__G, __Vs, bs, (a, ms), bx)
    let rec checkUniqueBlock' __39__ __40__ __41__ __42__ __43__ __44__ =
      match (__39__, __40__, __41__, __42__, __43__, __44__) with
      | (__G, (t, nil), bs, cs, (a, ms), b) -> ()
      | (__G, (t, (Dec (xOpt, __V) as D)::piDecs), bs, cs, (a, ms), b) ->
          let a' = I.targetFam __V in
          let _ =
            if a = a'
            then
              let (__V', s) = instEVars (__G, (__V, t)) in
              let _ =
                checkUniqueBlockBlocks
                  (__G, (__V', s), bs, (a, ms), (b, xOpt)) in
              let _ =
                checkUniqueBlockConsts (__G, (__V', s), cs, ms, (b, xOpt)) in
              ()
            else () in
          checkUniqueBlock'
            ((I.Decl (__G, __D)), ((I.dot1 t), piDecs), bs, cs, (a, ms), b)
    let rec checkUniqueBlock (Gsome, piDecs) bs cs (a, ms) b =
      let t = createEVarSub (I.Null, Gsome) in
      checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
    let rec checkUniqueWorlds __45__ __46__ __47__ =
      match (__45__, __46__, __47__) with
      | (nil, cs, (a, ms)) -> ()
      | (b::bs, cs, (a, ms)) ->
          (checkUniqueBlockInternal ((I.constBlock b), (a, ms), b);
           checkUniqueBlock ((I.constBlock b), (b :: bs), cs, (a, ms), b);
           checkUniqueWorlds (bs, cs, (a, ms)))
    let rec checkNoDef a =
      match I.sgnLookup a with
      | ConDef _ ->
          raise
            (Error
               (((^) "Uniqueness checking " cName a) ^
                  ":\ntype family must not be defined."))
      | _ -> ()
    let rec checkUnique a ms =
      let _ =
        chatter 4
          (fun () -> ((^) "Uniqueness checking family " cName a) ^ "\n") in
      let _ = checkNoDef a in
      let _ =
        try Subordinate.checkNoDef a
        with
        | Error msg ->
            raise
              (Error ((((^) "Coverage checking " cName a) ^ ":\n") ^ msg)) in
      let cs = Index.lookup a in
      let Worlds bs =
        ((try W.lookup a
          with
          | Error msg ->
              raise
                (Error
                   ((^) (((^) "Uniqueness checking " cName a) ^
                           ":\nMissing world declaration for ")
                      cName a)))
        (* worlds declarations for a *)) in
      let _ =
        try checkUniqueConsts (cs, ms)
        with
        | Error msg ->
            raise
              (Error ((((^) "Uniqueness checking " cName a) ^ ":\n") ^ msg)) in
      let _ =
        try checkUniqueWorlds (bs, cs, (a, ms))
        with
        | Error msg ->
            raise
              (Error ((((^) "Uniqueness checking " cName a) ^ ":\n") ^ msg)) in
      let _ =
        chatter 5
          (fun () ->
             ((^) "Checking uniqueness modes for family " cName a) ^ "\n") in
      let _ =
        try UniqueCheck.checkMode (a, ms)
        with
        | Error msg ->
            raise
              (Error
                 ((((^) "Uniqueness mode checking " cName a) ^ ":\n") ^ msg)) in
      ((())(* lookup constants defining a *))
  end ;;




module UniqueTable =
  (Make_ModeTable)(struct module Table = IntRedBlackTree end)
module UniqueCheck =
  (Make_ModeCheck)(struct
                     module ModeTable = UniqueTable
                     module Whnf = Whnf
                     module Index = Index
                     module Origins = Origins
                   end)
module Unique =
  (Make_Unique)(struct
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
                end);;
