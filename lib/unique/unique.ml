
(* Uniqueness Checking *)
(* Author: Frank Pfenning *)
module type UNIQUE  =
  sig
    exception Error of string 
    val checkUnique : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
  end;;




(* Uniqueness Checking *)
(* Author: Frank Pfenning *)
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
                       (* must be trailing! *)
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
    let rec pName =
      function
      | (cid, SOME x) -> (((^) "#" cName cid) ^ "_") ^ x
      | (cid, NONE) -> ((^) "#" cName cid) ^ "_?"
    let rec instEVars =
      function
      | (G, (Pi ((Dec (_, V1), _), V2), s)) ->
          let X1 = I.newEVar (G, (I.EClo (V1, s))) in
          instEVars (G, (V2, (I.Dot ((I.Exp X1), s))))
      | (G, ((Root _, _) as Vs)) -> Vs
    let rec createEVarSub =
      function
      | (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, Decl (G', (Dec (_, V) as D))) ->
          let s = createEVarSub (G, G') in
          let V' = I.EClo (V, s) in
          let X = I.newEVar (G, V') in I.Dot ((I.Exp X), s)
    let rec unifiable (G, (U, s), (U', s')) =
      Unify.unifiable (G, (U, s), (U', s'))
    let rec unifiableSpines =
      function
      | (G, (I.Nil, s), (I.Nil, s'), M.Mnil) -> true__
      | (G, (App (U1, S2), s), (App (U1', S2'), s'), Mapp
         (Marg (M.Plus, _), ms2)) ->
          (unifiable (G, (U1, s), (U1', s'))) &&
            (unifiableSpines (G, (S2, s), (S2', s'), ms2))
      | (G, (App (U1, S2), s), (App (U1', S2'), s'), Mapp
         (Marg (mode, _), ms2)) ->
          unifiableSpines (G, (S2, s), (S2', s'), ms2)
    let rec unifiableRoots
      (G, (Root (Const a, S), s), (Root (Const a', S'), s'), ms) =
      (a = a') && (unifiableSpines (G, (S, s), (S', s'), ms))
    let rec checkNotUnifiableTypes (G, Vs, Vs', ms, (bx, by)) =
      chatter 6
        (function
         | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") pName by) ^ "\n");
      CSManager.trail
        (function
         | () ->
             if unifiableRoots (G, Vs, Vs', ms)
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
      | (G, Vs, (t, nil), (a, ms), bx) -> ()
      | (G, (V, s), (t, (Dec (yOpt, V') as D)::piDecs), (a, ms), (b, xOpt))
          ->
          let a' = I.targetFam V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (G, (V, s), (instEVars (G, (V', t))), ms,
                  ((b, xOpt), (b, yOpt)))
            else () in
          checkDiffBlocksInternal
            ((I.Decl (G, D)), (V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
    let rec checkUniqueBlockInternal' =
      function
      | (G, (t, nil), (a, ms), b) -> ()
      | (G, (t, (Dec (xOpt, V) as D)::piDecs), (a, ms), b) ->
          let a' = I.targetFam V in
          let _ =
            if a = a'
            then
              let (V', s) = instEVars (G, (V, t)) in
              checkDiffBlocksInternal
                ((I.Decl (G, D)), (V', (I.comp (s, I.shift))),
                  ((I.dot1 t), piDecs), (a, ms), (b, xOpt))
            else () in
          checkUniqueBlockInternal'
            ((I.Decl (G, D)), ((I.dot1 t), piDecs), (a, ms), b)
    let rec checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
      let t = createEVarSub (I.Null, Gsome) in
      checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)
    let rec checkUniqueBlockConsts =
      function
      | (G, Vs, nil, ms, bx) -> ()
      | (G, Vs, (Const cid)::cs, ms, bx) ->
          let _ =
            chatter 6
              (function
               | () -> ((^) (((^) "?- " pName bx) ^ " ~ ") cName cid) ^ "\n") in
          let Vs' = instEVars (G, ((I.constType cid), I.id)) in
          let _ =
            CSManager.trail
              (function
               | () ->
                   if unifiableRoots (G, Vs, Vs', ms)
                   then
                     raise
                       (Error
                          (((^) (((^) "Block " pName bx) ^ " and constant ")
                              cName cid)
                             ^ " overlap"))
                   else ()) in
          checkUniqueBlockConsts (G, Vs, cs, ms, bx)
    let rec checkUniqueBlockBlock =
      function
      | (G, Vs, (t, nil), (a, ms), (bx, b')) -> ()
      | (G, (V, s), (t, (Dec (yOpt, V') as D)::piDecs), (a, ms), (bx, b')) ->
          let a' = I.targetFam V' in
          let _ =
            if a = a'
            then
              checkNotUnifiableTypes
                (G, (V, s), (instEVars (G, (V', t))), ms, (bx, (b', yOpt)))
            else () in
          checkUniqueBlockBlock
            ((I.Decl (G, D)), (V, (I.comp (s, I.shift))),
              ((I.dot1 t), piDecs), (a, ms), (bx, b'))
    let rec checkUniqueBlockBlocks =
      function
      | (G, Vs, nil, (a, ms), bx) -> ()
      | (G, Vs, b::bs, (a, ms), bx) ->
          let (Gsome, piDecs) = I.constBlock b in
          let t = createEVarSub (G, Gsome) in
          let _ =
            checkUniqueBlockBlock (G, Vs, (t, piDecs), (a, ms), (bx, b)) in
          checkUniqueBlockBlocks (G, Vs, bs, (a, ms), bx)
    let rec checkUniqueBlock' =
      function
      | (G, (t, nil), bs, cs, (a, ms), b) -> ()
      | (G, (t, (Dec (xOpt, V) as D)::piDecs), bs, cs, (a, ms), b) ->
          let a' = I.targetFam V in
          let _ =
            if a = a'
            then
              let (V', s) = instEVars (G, (V, t)) in
              let _ =
                checkUniqueBlockBlocks (G, (V', s), bs, (a, ms), (b, xOpt)) in
              let _ = checkUniqueBlockConsts (G, (V', s), cs, ms, (b, xOpt)) in
              ()
            else () in
          checkUniqueBlock'
            ((I.Decl (G, D)), ((I.dot1 t), piDecs), bs, cs, (a, ms), b)
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
    (*---------------------*)
    (* Auxiliary Functions *)
    (*---------------------*)
    (* instEVars (G, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where G |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
    (* generalized from ../cover/cover.fun *)
    (* createEVarSub (G, G') = s

       Invariant:
       If   G |- G' ctx
       then G |- s : G' and s instantiates each x:A with an EVar G |- X : A
    *)
    (* unifiable (G, (U, s), (U', s')) = true
       iff G |- U[s] = U'[s'] : V  (for some V)
       Effect: may instantiate EVars in all inputs
    *)
    (* unifiableSpines (G, (S, s), (S', s'), ms) = true
       iff G |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    (* skip output ( - ) or ignore ( * ) arguments *)
    (* unifiableRoots (G, (a @ S, s), (a' @ S', s'), ms) = true
       iff G |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    (*----------------------------*)
    (* Constant/Constant overlaps *)
    (*----------------------------*)
    (* checkNotUnifable (c, c', ms) = ()
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
    (*-----------------------------------------*)
    (* Block/Block and Block/Constant overlaps *)
    (*-----------------------------------------*)
    (* checkDiffBlocksInternal (G, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for a
    *)
    (* checkUniqueBlockInternal' (G, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)
    (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)
    (* . |- t : Gsome *)
    (* checkUniqueBlockConstants (G, (V, s), cs, ms, bx) = ()
       checks that V[s] = a@S[s] does not overlap with any constant in cs
       according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       Effect: raises Error(msg) otherwise
    *)
    (* checkUniqueBlockBlock (G, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for a in piDecs[t] according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)
    (* checkUniqueBlockBlocks (G, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for family a in any block in bs = [b1,...,bn] according to mode spine ms for a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)
    (* checkUniqueBlock' (G, (t, piDecs), bs, cs, (a, ms), b) = ()
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
    *)
    let rec checkNoDef a =
      match I.sgnLookup a with
      | ConDef _ ->
          raise
            (Error
               (((^) "Uniqueness checking " cName a) ^
                  ":\ntype family must not be defined."))
      | _ -> ()
    (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    let rec checkUnique (a, ms) =
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
