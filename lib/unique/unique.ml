
module type UNIQUE  =
  sig
    exception Error of
      ((string)(* Author: Frank Pfenning *)(* Uniqueness Checking *))
      
    val checkUnique : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
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
                       module Timers :
                       ((TIMERS)(* Uniqueness Checking *)
                       (* Author: Frank Pfenning *)(* must be trailing! *))
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
    let rec pName =
      function
      | (cid, SOME x) -> (((^) "#" cName cid) ^ "_") ^ x
      | (cid, NONE) -> ((^) "#" cName cid) ^ "_?"
    let rec instEVars =
      function
      | (g, (Pi ((Dec (_, V1), _), V2), s)) ->
          let X1 = I.newEVar (g, (I.EClo (V1, s))) in
          instEVars (g, (V2, (I.Dot ((I.Exp X1), s))))
      | (g, ((Root _, _) as Vs)) -> Vs
    let rec createEVarSub =
      function
      | (g, I.Null) -> I.Shift (I.ctxLength g)
      | (g, Decl (g', (Dec (_, V) as D))) ->
          let s = createEVarSub (g, g') in
          let V' = I.EClo (V, s) in
          let X = I.newEVar (g, V') in I.Dot ((I.Exp X), s)
    let rec unifiable (g, (U, s), (U', s')) =
      Unify.unifiable (g, (U, s), (U', s'))
    let rec unifiableSpines =
      function
      | (g, (I.Nil, s), (I.Nil, s'), M.Mnil) -> true__
      | (g, (App (u1, s2), s), (App (u1', s2'), s'), Mapp
         (Marg (M.Plus, _), ms2)) ->
          (unifiable (g, (u1, s), (u1', s'))) &&
            (unifiableSpines (g, (s2, s), (s2', s'), ms2))
      | (g, (App (u1, s2), s), (App (u1', s2'), s'), Mapp
         (Marg (mode, _), ms2)) ->
          unifiableSpines (g, (s2, s), (s2', s'), ms2)
    let rec unifiableRoots
      (g, (Root (Const a, S), s), (Root (Const a', S'), s'), ms) =
      (a = a') && (unifiableSpines (g, (S, s), (S', s'), ms))
    let rec checkNotUnifiableTypes (g, Vs, Vs', ms, (bx, by)) =
      chatter 6
        (function
         | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") pName by) ^ "\n");
      CSManager.trail
        (function
         | () ->
             if unifiableRoots (g, Vs, Vs', ms)
             then
               raise
                 (Error
                    (((^) (((^) "Blocks " pName bx) ^ " and ") pName by) ^
                       " overlap"))
             else ())
    let rec checkDiffConstConst (Const cid, Const cid', ms) =
      let _ =
        chatter 6
          (function
           | () -> ((^) (((^) "?- " cName cid) ^ " ~ ") cName cid') ^ "\n") in
      let Vs = instEVars (I.Null, ((I.constType cid), I.id)) in
      let Vs' = instEVars (I.Null, ((I.constType cid'), I.id)) in
      let _ =
        CSManager.trail
          (function
           | () ->
               if unifiableRoots (I.Null, Vs, Vs', ms)
               then
                 raise
                   (Error
                      (((^) (((^) "Constants " cName cid) ^ " and ") cName
                          cid')
                         ^ " overlap\n"))
               else ()) in
      ()
    let rec checkUniqueConstConsts =
      function
      | (c, nil, ms) -> ()
      | (c, c'::cs', ms) ->
          (checkDiffConstConst (c, c', ms);
           checkUniqueConstConsts (c, cs', ms))
    let rec checkUniqueConsts =
      function
      | (nil, ms) -> ()
      | (c::cs, ms) ->
          (checkUniqueConstConsts (c, cs, ms); checkUniqueConsts (cs, ms))
    let rec checkDiffBlocksInternal =
      function
      | (g, Vs, (t, nil), (a, ms), bx) -> ()
      | (g, (V, s), (t, (Dec (yOpt, V') as D)::piDecs), (a, ms), (b, xOpt))
          ->
          let a' = I.targetFam V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (g, (V, s), (instEVars (g, (V', t))), ms,
                  ((b, xOpt), (b, yOpt)))
            else () in
          checkDiffBlocksInternal
            ((I.Decl (g, D)), (V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
    let rec checkUniqueBlockInternal' =
      function
      | (g, (t, nil), (a, ms), b) -> ()
      | (g, (t, (Dec (xOpt, V) as D)::piDecs), (a, ms), b) ->
          let a' = I.targetFam V in
          let _ =
            if a = a'
            then
              let (V', s) = instEVars (g, (V, t)) in
              checkDiffBlocksInternal
                ((I.Decl (g, D)), (V', (I.comp (s, I.shift))),
                  ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
            else () in
          checkUniqueBlockInternal'
            ((I.Decl (g, D)), ((I.dot1 t), piDecs), (a, ms), b)
    let rec checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
      let t = createEVarSub (I.Null, Gsome) in
      checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)
    let rec checkUniqueBlockConsts =
      function
      | (g, Vs, nil, ms, bx) -> ()
      | (g, Vs, (Const cid)::cs, ms, bx) ->
          let _ =
            chatter 6
              (function
               | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") cName cid) ^ "\n") in
          let Vs' = instEVars (g, ((I.constType cid), I.id)) in
          let _ =
            CSManager.trail
              (function
               | () ->
                   if unifiableRoots (g, Vs, Vs', ms)
                   then
                     raise
                       (Error
                          (((^) (((^) "Block " pName bx) ^ " and constant ")
                              cName cid)
                             ^ " overlap"))
                   else ()) in
          checkUniqueBlockConsts (g, Vs, cs, ms, bx)
    let rec checkUniqueBlockBlock =
      function
      | (g, Vs, (t, nil), (a, ms), (bx, b')) -> ()
      | (g, (V, s), (t, (Dec (yOpt, V') as D)::piDecs), (a, ms), (bx, b')) ->
          let a' = I.targetFam V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (g, (V, s), (instEVars (g, (V', t))), ms, (bx, (b', yOpt)))
            else () in
          checkUniqueBlockBlock
            ((I.Decl (g, D)), (V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (bx, b'))
    let rec checkUniqueBlockBlocks =
      function
      | (g, Vs, nil, (a, ms), bx) -> ()
      | (g, Vs, b::bs, (a, ms), bx) ->
          let (Gsome, piDecs) = I.constBlock b in
          let t = createEVarSub (g, Gsome) in
          let _ =
            checkUniqueBlockBlock (g, Vs, (t, piDecs), (a, ms), (bx, b)) in
          checkUniqueBlockBlocks (g, Vs, bs, (a, ms), bx)
    let rec checkUniqueBlock' =
      function
      | (g, (t, nil), bs, cs, (a, ms), b) -> ()
      | (g, (t, (Dec (xOpt, V) as D)::piDecs), bs, cs, (a, ms), b) ->
          let a' = I.targetFam V in
          let _ =
            if a = a'
            then
              let (V', s) = instEVars (g, (V, t)) in
              let _ =
                checkUniqueBlockBlocks (g, (V', s), bs, (a, ms), (b, xOpt)) in
              let _ = checkUniqueBlockConsts (g, (V', s), cs, ms, (b, xOpt)) in
              ()
            else () in
          checkUniqueBlock'
            ((I.Decl (g, D)), ((I.dot1 t), piDecs), bs, cs, (a, ms), b)
    let rec checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) =
      let t = createEVarSub (I.Null, Gsome) in
      checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
    let rec checkUniqueWorlds =
      function
      | (nil, cs, (a, ms)) -> ()
      | (b::bs, cs, (a, ms)) ->
          (checkUniqueBlockInternal ((I.constBlock b), (a, ms), b);
           checkUniqueBlock ((I.constBlock b), (b :: bs), cs, (a, ms), b);
           checkUniqueWorlds (bs, cs, (a, ms)))
    let rec checkNoDef
      ((a)(*---------------------*)(* Auxiliary Functions *)
      (*---------------------*)(* instEVars (g, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where g |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
      (* generalized from ../cover/cover.fun *)(* createEVarSub (g, g') = s

       Invariant:
       If   g |- g' ctx
       then g |- s : g' and s instantiates each x:A with an EVar g |- X : A
    *)
      (* unifiable (g, (U, s), (U', s')) = true
       iff g |- U[s] = U'[s'] : V  (for some V)
       Effect: may instantiate EVars in all inputs
    *)
      (* unifiableSpines (g, (S, s), (S', s'), ms) = true
       iff g |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
      (* skip output ( - ) or ignore ( * ) arguments *)
      (* unifiableRoots (g, (a @ S, s), (a' @ S', s'), ms) = true
       iff g |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
      (*----------------------------*)(* Constant/Constant overlaps *)
      (*----------------------------*)(* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
      (* checkUniqueConstConsts (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
      (* checkUniqueConsts (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
      (*-----------------------------------------*)(* Block/Block and Block/Constant overlaps *)
      (*-----------------------------------------*)(* checkDiffBlocksInternal (g, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for a
    *)
      (* checkUniqueBlockInternal' (g, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)
      (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)
      (* . |- t : Gsome *)(* checkUniqueBlockConstants (g, (V, s), cs, ms, bx) = ()
       checks that V[s] = a@S[s] does not overlap with any constant in cs
       according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       Effect: raises Error(msg) otherwise
    *)
      (* checkUniqueBlockBlock (g, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for a in piDecs[t] according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)
      (* checkUniqueBlockBlocks (g, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for family a in any block in bs = [b1,...,bn] according to mode spine ms for a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)
      (* checkUniqueBlock' (g, (t, piDecs), bs, cs, (a, ms), b) = ()
       check that no declaration for family a in piDecs[t]
       overlaps with any declaration for a in bs or any constant in cs
       according to mode spine ms for a
       b is the block identifier in which piDecs occur for error messages
    *)
      (* checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) = ()
       see checkUniqueBlock'
    *)
      (* checkUniqueWorlds (bs, cs, (a, ms)) = ()
       checks if no declarations for a in bs overlap with other declarations
       for a in bs or any constant in cs according to mode spine ms
       Effect: raise Error(msg) otherwise
    *)
      (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *))
      =
      match I.sgnLookup a with
      | ConDef _ ->
          raise
            (Error
               (((^) "Uniqueness checking " cName a) ^
                  ":\ntype family must not be defined."))
      | _ -> ()
    let rec checkUnique
      (((a)(* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)),
       ms)
      =
      let _ =
        chatter 4
          (function
           | () -> ((^) "Uniqueness checking family " cName a) ^ "\n") in
      let _ = checkNoDef a in
      let _ =
        try Subordinate.checkNoDef a
        with
        | Error msg ->
            raise
              (Error ((((^) "Coverage checking " cName a) ^ ":\n") ^ msg)) in
      let cs = Index.lookup a in
      let Worlds ((bs)(* lookup constants defining a *)) =
        try W.lookup a
        with
        | Error msg ->
            raise
              (Error
                 ((^) (((^) "Uniqueness checking " ((cName)
                          (* worlds declarations for a *)) a)
                         ^ ":\nMissing world declaration for ")
                    cName a)) in
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
          (function
           | () ->
               ((^) "Checking uniqueness modes for family " cName a) ^ "\n") in
      let _ =
        try UniqueCheck.checkMode (a, ms)
        with
        | Error msg ->
            raise
              (Error
                 ((((^) "Uniqueness mode checking " cName a) ^ ":\n") ^ msg)) in
      ()
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
