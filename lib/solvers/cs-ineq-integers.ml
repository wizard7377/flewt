
module CSIneqIntegers(CSIneqIntegers:sig
                                       module Integers : INTEGERS
                                       module Rationals : RATIONALS
                                       module Trail : TRAIL
                                       module Unify : UNIFY
                                       module SparseArray : SPARSE_ARRAY
                                       module SparseArray2 : SPARSE_ARRAY2
                                       module CSEqIntegers : CS_EQ_INTEGERS
                                       module Compat :
                                       ((COMPAT)(* Solver for linear inequations, based on branch & bound *)
                                       (* Author: Roberto Virga *)
                                       (*! structure IntSyn : INTSYN !*)
                                       (*! sharing Unify.IntSyn = IntSyn !*)
                                       (*! structure CSManager : CS_MANAGER !*)
                                       (*! sharing CSManager.IntSyn = IntSyn !*)
                                       (*! sharing CSEqIntegers.IntSyn = IntSyn !*)
                                       (*! sharing CSEqIntegers.CSManager = CSManager !*))
                                     end) =
  struct
    open IntSyn
    open Rationals
    open CSEqIntegers
    module CSM = CSManager
    module FX = CSM.Fixity
    module MS = ModeSyn
    module Array = SparseArray
    module Array2 = SparseArray2
    let zero_int = Integers.fromInt 0
    let one_int = Integers.fromInt 1
    let myID = (ref (-1) : cid ref)
    let geqID = (ref (-1) : cid ref)
    let rec geq (U, V) = Root ((Const (!geqID)), (App (U, (App (V, Nil)))))
    let rec geq0 (U) = geq (U, (constant zero_int))
    let geqAddID = (ref (-1) : cid ref)
    let rec geqAdd (U1, U2, V, W) =
      Root
        ((Const (!geqAddID)),
          (App (U1, (App (U2, (App (V, (App (W, Nil)))))))))
    let rec geqNConDec d =
      ConDec
        (((^) ((Integers.toString d) ^ ">=") Integers.toString zero_int),
          NONE, 0, Normal, (geq0 (constant d)), Type)
    let rec geqNExp d = Root ((FgnConst ((!myID), (geqNConDec d))), Nil)
    let rec parseGeqN string =
      let suffix = ">=" ^ (toString zero) in
      let stringLen = String.size string in
      let suffixLen = String.size suffix in
      let numLen = Int.(-) (stringLen, suffixLen) in
      if
        (Int.(>) (stringLen, suffixLen)) &&
          ((String.substring (string, numLen, suffixLen)) = suffix)
      then
        match Integers.fromString (String.substring (string, 0, numLen)) with
        | SOME d ->
            (if Integers.(>=) (d, zero_int)
             then SOME (geqNConDec d)
             else NONE)
        | NONE -> NONE
      else NONE
    type __Position =
      | Row of int 
      | Col of int 
    type __Owner =
      | Var of (IntSyn.dctx * __Mon) 
      | Exp of (IntSyn.dctx * __Sum) 
    type __Restriction =
      | Restr of (IntSyn.dctx * IntSyn.__Exp) 
    type nonrec label =
      <
        owner: __Owner  ;tag: int ref  ;restr: __Restriction option ref  ;
        dead: bool ref   > 
    type __Operation =
      | Insert of __Position 
      | Pivot of (int * int) 
      | Kill of __Position 
      | Restrict of __Position 
      | UpdateOwner of (__Position * __Owner * int ref) 
    type nonrec tableau =
      <
        rlabels: label Array.array  ;clabels: label Array.array  ;consts: 
                                                                    number
                                                                    Array.array
                                                                     ;
        coeffs: number Array2.array  ;nrows: int ref  ;ncols: int ref  ;
        trail: __Operation Trail.trail   > 
    exception MyFgnCnstrRep of int ref 
    exception Error 
    let a = 16807.0
    let m = 2147483647.0
    let seed = ref 1999.0
    let rec rand (min, size) =
      let nextrand () =
        let t = Real.( * ) (a, (!seed)) in
        (:=) seed Real.(-)
          (t, (Real.( * ) (m, (Real.fromInt (Real.floor (t / m))))));
        (/) (Real.(-) ((!seed), 1.0)) Real.(-) (m, 1.0) in
      Int.(+)
        (min, (Real.floor (Real.( * ) ((nextrand ()), (Real.fromInt size)))))
    let tableau =
      let l =
        {
          owner = (Exp (Null, (Sum (zero_int, nil))));
          tag = (ref 0);
          restr = (ref NONE);
          dead = (ref true__)
        } in
      ({
         rlabels = (Array.array l);
         clabels = (Array.array l);
         consts = (Array.array zero);
         coeffs = (Array2.array zero);
         nrows = (ref 0);
         ncols = (ref 0);
         trail = (Trail.trail ())
       } : tableau)
    let rec rlabel i = Array.sub (((fun r -> r.rlabels) tableau), i)
    let rec clabel j = Array.sub (((fun r -> r.clabels) tableau), j)
    let rec const i = Array.sub (((fun r -> r.consts) tableau), i)
    let rec coeff (i, j) = Array2.sub (((fun r -> r.coeffs) tableau), i, j)
    let rec nRows () = !((fun r -> r.nrows) tableau)
    let rec nCols () = !((fun r -> r.ncols) tableau)
    let rec incrNRows () =
      let old = nRows () in
      (:=) (((fun r -> r.nrows)) tableau) Int.(+) (old, 1); old
    let rec incrNCols () =
      let old = nCols () in
      (:=) (((fun r -> r.ncols)) tableau) Int.(+) (old, 1); old
    let rec decrNRows () =
      (:=) ((fun r -> r.nrows) tableau) Int.(-) ((nRows ()), 1)
    let rec decrNCols () =
      (:=) ((fun r -> r.ncols) tableau) Int.(-) ((nCols ()), 1)
    let rec incrArray (array, i, value) =
      Array.update (array, i, ((Array.sub (array, i)) + value))
    let rec incrArray2 (array, i, j, value) =
      Array2.update (array, i, j, ((Array2.sub (array, i, j)) + value))
    let rec incrArray2Row (array, i, (j, len), f) =
      Compat.Vector.mapi
        (function
         | (j, value) -> Array2.update (array, i, j, ((+) value f j)))
        (Array2.row (array, i, (j, len)))
    let rec incrArray2Col (array, j, (i, len), f) =
      Compat.Vector.mapi
        (function
         | (i, value) -> Array2.update (array, i, j, ((+) value f i)))
        (Array2.column (array, j, (i, len)))
    let rec clearArray2Row (array, i, (j, len)) =
      Compat.Vector.mapi
        (function | (j, value) -> Array2.update (array, i, j, zero))
        (Array2.row (array, i, (j, len)))
    let rec clearArray2Col (array, j, (i, len)) =
      Compat.Vector.mapi
        (function | (i, value) -> Array2.update (array, i, j, zero))
        (Array2.column (array, j, (i, len)))
    let rec label = function | Row i -> rlabel i | Col j -> clabel j
    let rec restriction (l : label) = !((fun r -> r.restr) l)
    let rec restricted (l : label) =
      match restriction l with | SOME _ -> true__ | NONE -> false__
    let rec dead (l : label) = !((fun r -> r.dead) l)
    let rec setOwnership (pos, owner, tag) =
      let old = label pos in
      let new__ =
        {
          owner;
          tag;
          restr = (ref (restriction old));
          dead = (ref (dead old))
        } in
      match pos with
      | Row i -> Array.update (((fun r -> r.rlabels) tableau), i, new__)
      | Col j -> Array.update (((fun r -> r.clabels) tableau), j, new__)
    let rec ownerContext = function | Var (G, mon) -> G | Exp (G, sum) -> G
    let rec ownerSum =
      function | Var (G, mon) -> Sum (zero_int, [mon]) | Exp (G, sum) -> sum
    let rec displayPos =
      function
      | Row row -> print (((^) "row " Int.toString row) ^ "\n")
      | Col col -> print (((^) "column " Int.toString col) ^ "\n")
    let rec displaySum =
      function
      | Sum (m, (Mon (n, _))::monL) ->
          (print (Integers.toString n);
           print " ? + ";
           displaySum (Sum (m, monL)))
      | Sum (m, nil) -> (print (Integers.toString m); print " >= 0\n")
    let rec display () =
      let printLabel (col, (l : label)) =
        print "\t";
        (match (fun r -> r.owner) l with
         | Var _ -> print "V"
         | Exp _ -> print "E");
        if restricted l then print ">" else print "*";
        if dead l then print "#" else print "" in
      let printRow (row, (l : label)) =
        let printCol (col, (d : number)) = print "\t"; print (toString d) in
        let vec =
          Array2.row (((fun r -> r.coeffs) tableau), row, (0, (nCols ()))) in
        (match (fun r -> r.owner) l with
         | Var _ -> print "V"
         | Exp _ -> print "E");
        if restricted l then print ">" else print "*";
        if dead l then print "#" else print "";
        print "\t";
        Compat.Vector.mapi printCol vec;
        print "\t";
        print (toString (const row));
        print "\n" in
      print "\t";
      Array.app printLabel (((fun r -> r.clabels) tableau), 0, (nCols ()));
      print "\n";
      Array.app printRow (((fun r -> r.rlabels) tableau), 0, (nRows ()));
      print "Columns:\n";
      Array.app
        (function
         | (_, (l : label)) -> displaySum (ownerSum ((fun r -> r.owner) l)))
        (((fun r -> r.clabels) tableau), 0, (nCols ()));
      print "Rows:\n";
      Array.app
        (function
         | (_, (l : label)) -> displaySum (ownerSum ((fun r -> r.owner) l)))
        (((fun r -> r.rlabels) tableau), 0, (nRows ()))
    let rec findMon mon =
      let exception Found of int  in
        let find (i, (l : label)) =
          match (fun r -> r.owner) l with
          | Var (G, mon') ->
              if compatibleMon (mon, mon') then raise (Found i) else ()
          | _ -> () in
        try
          Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
          (try
             Array.app find (((fun r -> r.rlabels) tableau), 0, (nRows ()));
             NONE
           with | Found i -> SOME (Row i))
        with | Found j -> SOME (Col j)
    let rec findTag t =
      let exception Found of int  in
        let find (i, (l : label)) =
          if ((fun r -> r.tag) l) = t then raise (Found i) else () in
        try
          Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
          (try
             Array.app find (((fun r -> r.rlabels) tableau), 0, (nRows ()));
             NONE
           with | Found i -> SOME (Row i))
        with | Found j -> SOME (Col j)
    let rec isConstant row =
      Array.foldl
        (function
         | (j, l, rest) -> ((dead l) || ((coeff (row, j)) = zero)) && rest)
        true__ (((fun r -> r.clabels) tableau), 0, (nCols ()))
    let rec isSubsumed row =
      let constRow = const row in
      let isSubsumedByRow () =
        let candidates =
          Array.foldl
            (function
             | (i, (l : label), rest) ->
                 if (i <> row) && ((not (dead l)) && ((const i) = constRow))
                 then i :: rest
                 else rest) nil
            (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
        let filter =
          function
          | (j, l, nil) -> nil
          | (j, (l : label), candidates) ->
              if not (dead l)
              then
                List.filter
                  (function | i -> (=) (coeff (i, j)) coeff (row, j))
                  candidates
              else candidates in
        match Array.foldl filter candidates
                (((fun r -> r.clabels) tableau), 0, (nCols ()))
        with
        | nil -> NONE
        | i::_ -> SOME i in
      let isSubsumedByCol () =
        if constRow = zero
        then
          let nonNull =
            Array.foldl
              (function
               | (j, (l : label), rest) ->
                   if not (dead l)
                   then
                     let value = coeff (row, j) in
                     (if value <> zero then (j, value) :: rest else rest)
                   else rest) nil
              (((fun r -> r.clabels) tableau), 0, (nCols ())) in
          match nonNull with
          | (j, value)::[] -> (if value = one then SOME j else NONE)
          | _ -> NONE
        else NONE in
      match isSubsumedByRow () with
      | SOME i -> SOME (Row i)
      | NONE ->
          (match isSubsumedByCol () with
           | SOME j -> SOME (Col j)
           | NONE -> NONE)
    let rec findPivot row =
      let compareScore =
        function
        | (SOME d, SOME d') -> compare (d, d')
        | (SOME d, NONE) -> LESS
        | (NONE, SOME d') -> GREATER
        | (NONE, NONE) -> EQUAL in
      let findPivotCol (j, (l : label), ((score, champs) as result)) =
        let value = coeff (row, j) in
        let findPivotRow sgn (i, (l : label), ((score, champs) as result)) =
          let value = coeff (i, j) in
          if
            (not (dead l)) &&
              ((i <> row) &&
                 ((restricted l) && (((fromInt sgn) * value) < zero)))
          then
            let score' = SOME (abs (( * ) (const i) inverse value)) in
            match compareScore (score, score') with
            | GREATER -> (score', [(i, j)])
            | EQUAL -> (score, ((i, j) :: champs))
            | LESS -> result
          else result in
        if
          (not (dead l)) &&
            ((value <> zero) && ((not (restricted l)) || (value > zero)))
        then
          let (score', champs') as result' =
            Array.foldl (findPivotRow (sign value)) (NONE, [(row, j)])
              (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
          match compareScore (score, score') with
          | GREATER -> result
          | EQUAL -> (score, (champs @ champs'))
          | LESS -> result'
        else result in
      match Array.foldl findPivotCol ((SOME zero), nil)
              (((fun r -> r.clabels) tableau), 0, (nCols ()))
      with
      | (_, nil) -> NONE
      | (_, champs) ->
          SOME (List.nth (champs, (rand (0, (List.length champs)))))
    let rec pivot (row, col) =
      let pCoeffInverse = inverse (coeff (row, col)) in
      let pRowVector =
        Array2.row (((fun r -> r.coeffs) tableau), row, (0, (nCols ()))) in
      let pRow j = Vector.sub (pRowVector, j) in
      let pColVector =
        Array2.column (((fun r -> r.coeffs) tableau), col, (0, (nRows ()))) in
      let pCol i = Vector.sub (pColVector, i) in
      let pConst = const row in
      let pRLabel = rlabel row in
      let pCLabel = clabel col in
      Array.modify
        (function
         | (i, value) ->
             if i = row
             then ~ (value * pCoeffInverse)
             else value - ((( * ) pConst pCol i) * pCoeffInverse))
        (((fun r -> r.consts) tableau), 0, (nRows ()));
      Array2.modify Array2.ColMajor
        (function
         | (i, j, value) ->
             (match ((i = row), (j = col)) with
              | (true__, true__) -> pCoeffInverse
              | (true__, false__) -> ~ (value * pCoeffInverse)
              | (false__, true__) -> value * pCoeffInverse
              | (false__, false__) ->
                  value - ((( * ) (pRow j) pCol i) * pCoeffInverse)))
        {
          base = ((fun r -> r.coeffs) tableau);
          row = 0;
          col = 0;
          nrows = (nRows ());
          ncols = (nCols ())
        };
      Array.update (((fun r -> r.rlabels) tableau), row, pCLabel);
      Array.update (((fun r -> r.clabels) tableau), col, pRLabel)
    let rec delayMon (Mon (n, UsL), cnstr) =
      List.app (function | Us -> Unify.delay (Us, cnstr)) UsL
    let rec unifyRestr (Restr (G, proof), proof') =
      if Unify.unifiable (G, (proof, id), (proof', id))
      then ()
      else raise Error
    let rec unifySum (G, sum, d) =
      if
        (Unify.unify (G, ((toExp sum), id), ((constant (floor d)), id));
         true__)
      then ()
      else raise Error
    type nonrec decomp = (number * (number * __Position) list)
    let rec unaryMinusDecomp (d, wposL) =
      ((~ d), (List.map (function | (d, pos) -> ((~ d), pos)) wposL))
    type __MaximizeResult =
      | Nonnegative of number 
      | Unbounded of int 
    type __BranchResult =
      | BranchSucceed of int option 
      | BranchFail 
      | BranchDivide of (int * __BranchResult * __BranchResult) 
    let rec decomposeSum (G, Sum (m, monL)) =
      let monToWPos (Mon (n, UsL) as mon) =
        match findMon mon with
        | SOME pos -> ((fromInteger n), pos)
        | NONE ->
            let new__ = incrNCols () in
            let l =
              {
                owner = (Var (G, (Mon (one_int, UsL))));
                tag = (ref 0);
                restr = (ref NONE);
                dead = (ref false__)
              } in
            (Trail.log (((fun r -> r.trail) tableau), (Insert (Col new__)));
             delayMon (mon, (ref (makeCnstr ((fun r -> r.tag) l))));
             Array.update (((fun r -> r.clabels) tableau), new__, l);
             ((fromInteger n), (Col new__))) in
      ((fromInteger m), (List.map monToWPos monL))
    let rec maximizeRow row =
      let value = const row in
      if value < zero
      then
        match findPivot row with
        | SOME (i, j) ->
            (if i <> row
             then
               (Trail.log (((fun r -> r.trail) tableau), (Pivot (i, j)));
                pivot (i, j);
                maximizeRow row)
             else Unbounded j)
        | NONE -> raise Error
      else Nonnegative value
    let rec insertDecomp (((d, wposL) as decomp), owner) =
      let new__ = incrNRows () in
      let insertWPos (d, pos) =
        match pos with
        | Row row ->
            (incrArray2Row
               (((fun r -> r.coeffs) tableau), new__, (0, (nCols ())),
                 (function | j -> ( * ) d coeff (row, j)));
             incrArray
               (((fun r -> r.consts) tableau), new__, (( * ) d const row)))
        | Col col ->
            incrArray2 (((fun r -> r.coeffs) tableau), new__, col, d) in
      List.app insertWPos wposL;
      incrArray (((fun r -> r.consts) tableau), new__, d);
      (match isSubsumed new__ with
       | SOME pos ->
           (clearArray2Row
              (((fun r -> r.coeffs) tableau), new__, (0, (nCols ())));
            Array.update (((fun r -> r.consts) tableau), new__, zero);
            decrNRows ();
            pos)
       | NONE ->
           (setOwnership ((Row new__), owner, (ref 0));
            (:=) (((fun r -> r.dead)) (label (Row new__))) isConstant new__;
            Trail.log (((fun r -> r.trail) tableau), (Insert (Row new__)));
            Row new__))
    let rec insert (G, Us) =
      let sum = fromExp Us in
      insertDecomp ((decomposeSum (G, sum)), (Exp (G, sum)))
    let rec restrict =
      function
      | ((Col col as pos), restr) ->
          let l = label pos in
          if dead l
          then (unifyRestr (restr, (geqNExp zero_int)); NONE)
          else
            (match restriction l with
             | SOME (Restr (_, proof')) -> (unifyRestr (restr, proof'); NONE)
             | NONE ->
                 let nonNull =
                   Array.foldl
                     (function
                      | (i, (l : label), rest) ->
                          if not (dead l)
                          then
                            let value = coeff (i, col) in
                            (if value <> zero then i :: rest else rest)
                          else rest) nil
                     (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
                 (match nonNull with
                  | row::_ ->
                      (Trail.log
                         (((fun r -> r.trail) tableau), (Pivot (row, col)));
                       pivot (row, col);
                       restrict ((Row row), restr))
                  | nil ->
                      (Trail.log
                         (((fun r -> r.trail) tableau), (Restrict (Col col)));
                       (:=) (((fun r -> r.restr)) (label (Col col))) SOME
                         restr;
                       NONE)))
      | ((Row row as pos), restr) ->
          let l = label pos in
          if dead l
          then (unifyRestr (restr, (geqNExp (floor (const row)))); NONE)
          else
            (match restriction l with
             | SOME (Restr (_, proof')) -> (unifyRestr (restr, proof'); NONE)
             | NONE ->
                 (match maximizeRow row with
                  | Unbounded col ->
                      (Trail.log
                         (((fun r -> r.trail) tableau), (Restrict (Row row)));
                       (:=) (((fun r -> r.restr))
                               (Array.sub
                                  (((fun r -> r.rlabels) tableau), row)))
                         SOME restr;
                       if (const row) < zero
                       then
                         (Trail.log
                            (((fun r -> r.trail) tableau),
                              (Pivot (row, col)));
                          pivot (row, col))
                       else ();
                       NONE)
                  | Nonnegative value ->
                      (Trail.log
                         (((fun r -> r.trail) tableau), (Restrict (Row row)));
                       (:=) (((fun r -> r.restr))
                               (Array.sub
                                  (((fun r -> r.rlabels) tableau), row)))
                         SOME restr;
                       SOME row)))
    let rec insertEqual (G, pos, sum) =
      let (m, wposL) = decomposeSum (G, sum) in
      let decomp' = (m, (((~ one), pos) :: wposL)) in
      let pos' = insertDecomp (decomp', (Exp (G, (Sum (zero_int, nil))))) in
      let decomp'' = unaryMinusDecomp decomp' in
      let tag'' =
        (fun r -> r.tag)
          (label (insertDecomp (decomp'', (Exp (G, (Sum (zero_int, nil))))))) in
      restrictBB (exploreBB (pos', (Restr (G, (geqNExp zero_int)))));
      (match findTag tag'' with
       | SOME pos'' ->
           restrictBB (exploreBB (pos'', (Restr (G, (geqNExp zero_int))))))
    let rec update (G, pos, sum) =
      let l = label pos in
      Trail.log
        (((fun r -> r.trail) tableau),
          (UpdateOwner (pos, ((fun r -> r.owner) l), ((fun r -> r.tag) l))));
      setOwnership (pos, (Exp (G, sum)), (ref 0));
      if dead l
      then
        (match pos with
         | Row row ->
             if isConstant row
             then unifySum (G, sum, (const row))
             else
               (match isSubsumed row with
                | SOME pos' -> update (G, pos', sum))
         | Col col -> unifySum (G, sum, zero))
      else
        (let isVar =
           function
           | Sum (m, (Mon (n, _) as mon)::[]) ->
               if (m = zero_int) && (n = one_int) then SOME mon else NONE
           | sum -> NONE in
         match isVar sum with
         | SOME mon ->
             (match findMon mon with
              | SOME _ -> insertEqual (G, pos, sum)
              | NONE ->
                  let tag = ref 0 in
                  (Trail.log
                     (((fun r -> r.trail) tableau),
                       (UpdateOwner
                          (pos, ((fun r -> r.owner) l), ((fun r -> r.tag) l))));
                   setOwnership (pos, (Var (G, mon)), tag);
                   delayMon (mon, (ref (makeCnstr tag)))))
         | NONE -> insertEqual (G, pos, sum))
    let rec insertRestrExp (l, UL) =
      match restriction l with
      | NONE -> UL
      | SOME (Restr (_, _)) ->
          let owner = (fun r -> r.owner) l in
          let G = ownerContext owner in
          let U = toExp (ownerSum owner) in (G, (geq0 U)) :: UL
    let rec restrictions pos =
      let member (x, l) = List.exists (function | y -> x = y) l in
      let test l = (restricted l) && (not (dead l)) in
      let reachable =
        function
        | ((Row row as pos)::candidates, tried, closure) ->
            if member (pos, tried)
            then reachable (candidates, tried, closure)
            else
              (let new_candidates =
                 Array.foldl
                   (function
                    | (col, _, candidates) ->
                        if (coeff (row, col)) <> zero
                        then (Col col) :: candidates
                        else candidates) nil
                   (((fun r -> r.clabels) tableau), 0, (nCols ())) in
               let closure' =
                 if test (label pos) then pos :: closure else closure in
               reachable
                 ((new_candidates @ candidates), (pos :: tried), closure'))
        | ((Col col as pos)::candidates, tried, closure) ->
            if member (pos, tried)
            then reachable (candidates, tried, closure)
            else
              (let candidates' =
                 Array.foldl
                   (function
                    | (row, _, candidates) ->
                        if (coeff (row, col)) <> zero
                        then (Row row) :: candidates
                        else candidates) nil
                   (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
               let closure' =
                 if test (label pos) then pos :: closure else closure in
               reachable
                 ((candidates' @ candidates), (pos :: tried), closure'))
        | (nil, _, closure) -> closure in
      let restrExp pos =
        let l = label pos in
        let owner = (fun r -> r.owner) l in
        let G = ownerContext owner in
        let U = toExp (ownerSum owner) in (G, (geq0 U)) in
      List.map restrExp (reachable ([pos], nil, nil))
    let rec toInternal tag () =
      match findTag tag with | NONE -> nil | SOME pos -> restrictions pos
    let rec awake tag () =
      try
        match findTag tag with
        | SOME pos ->
            let owner = (fun r -> r.owner) (label pos) in
            let G = ownerContext owner in
            let sum = normalize (ownerSum owner) in
            (update (G, pos, sum); true__)
        | NONE -> true__
      with | Error -> false__
    let rec simplify tag () =
      match toInternal tag () with | nil -> true__ | _::_ -> false__
    let rec makeCnstr tag = FgnCnstr ((!myID), (MyFgnCnstrRep tag))
    let rec isIntegral () =
      let exception Found of int  in
        let find (i, (l : label)) =
          if not (dead l)
          then
            (if (denominator (const i)) <> one_int
             then raise (Found i)
             else ())
          else () in
        try
          Array.app find (((fun r -> r.rlabels) tableau), 0, (nRows ()));
          NONE
        with | Found i -> SOME i
    let rec boundLower (G, decomp, d) =
      let W = newEVar (G, (number ())) in
      let proof = newEVar (G, (geq0 W)) in
      let (d', wPosL) = unaryMinusDecomp decomp in
      let pos =
        insertDecomp
          (((d' + d), wPosL), (Var (G, (Mon (one_int, [(W, id)]))))) in
      (pos, (Restr (G, proof)))
    let rec boundUpper (G, decomp, d) =
      let W = newEVar (G, (number ())) in
      let proof = newEVar (G, (geq0 W)) in
      let (d', wPosL) = decomp in
      let pos =
        insertDecomp
          (((d' - d), wPosL), (Var (G, (Mon (one_int, [(W, id)]))))) in
      (pos, (Restr (G, proof)))
    let rec exploreBB (pos, restr) =
      try
        let result = restrict (pos, restr) in
        match isIntegral () with
        | SOME row ->
            let value = const row in
            let decomp = (zero, [(one, (Row row))]) in
            let G = ownerContext ((fun r -> r.owner) (label (Row row))) in
            let lower = fromInteger (floor value) in
            let upper = fromInteger (ceiling value) in
            let left () = exploreBB (boundLower (G, decomp, lower)) in
            let right () = exploreBB (boundUpper (G, decomp, upper)) in
            (match ((CSM.trail left), (CSM.trail right)) with
             | (BranchFail, BranchFail) -> BranchFail
             | (resultL, resultR) -> BranchDivide (row, resultL, resultR))
        | NONE -> BranchSucceed result
      with | Error -> BranchFail
    let rec minimizeBB row =
      let zeroColumn (j, (l : label)) =
        let decomp = (zero, [(one, (Col j))]) in
        let G = ownerContext ((fun r -> r.owner) (label (Col j))) in
        let lower = ~ one in
        let upper = one in
        let left () = exploreBB (boundLower (G, decomp, lower)) in
        let right () = exploreBB (boundUpper (G, decomp, upper)) in
        if restricted l
        then (CSM.trail right) = BranchFail
        else
          ((CSM.trail left) = BranchFail) && ((CSM.trail right) = BranchFail) in
      let killColumn (j, (l : label)) =
        if
          (not (dead l)) &&
            (((coeff (row, j)) <> zero) && (zeroColumn (j, l)))
        then
          (Trail.log (((fun r -> r.trail) tableau), (Kill (Col j)));
           ((fun r -> r.dead) (Array.sub (((fun r -> r.clabels) tableau), j)))
             := true__;
           (match restriction l with
            | SOME restr -> unifyRestr (restr, (geqNExp zero_int))
            | NONE -> ());
           (match (fun r -> r.owner) l with
            | Var _ as owner ->
                unifySum ((ownerContext owner), (ownerSum owner), zero)
            | _ -> ()))
        else () in
      let killRow (i, (l : label)) =
        if not (dead l)
        then
          (if isConstant i
           then
             (if (denominator (const i)) = one_int then () else raise Error;
              Trail.log (((fun r -> r.trail) tableau), (Kill (Row i)));
              ((fun r -> r.dead)
                 (Array.sub (((fun r -> r.rlabels) tableau), i)))
                := true__;
              (match restriction l with
               | SOME restr ->
                   if (denominator (const i)) = one_int
                   then unifyRestr (restr, (geqNExp (floor (const i))))
                   else raise Error
               | NONE -> ());
              (match (fun r -> r.owner) l with
               | Var _ as owner ->
                   unifySum
                     ((ownerContext owner), (ownerSum owner), (const i))
               | _ -> ()))
           else
             (match isSubsumed i with
              | SOME pos' ->
                  let l' = label pos' in
                  (Trail.log (((fun r -> r.trail) tableau), (Kill (Row i)));
                   ((fun r -> r.dead)
                      (Array.sub (((fun r -> r.rlabels) tableau), i)))
                     := true__;
                   (match ((restriction l), (restriction l')) with
                    | (SOME restr, SOME (Restr (_, proof'))) ->
                        unifyRestr (restr, proof')
                    | (SOME _, NONE) ->
                        (Trail.log
                           (((fun r -> r.trail) tableau), (Restrict pos'));
                         (:=) (((fun r -> r.restr)) l') restriction l)
                    | (NONE, _) -> ()))
              | NONE -> ()))
        else () in
      Array.app killColumn (((fun r -> r.clabels) tableau), 0, (nCols ()));
      Array.app killRow (((fun r -> r.rlabels) tableau), 0, (nRows ()))
    let rec restrictBB result =
      match result with
      | BranchFail -> raise Error
      | BranchDivide (row, resultL, BranchFail) ->
          let value = fromInteger (floor (const row)) in
          let decomp = (zero, [(one, (Row row))]) in
          let G = ownerContext ((fun r -> r.owner) (label (Row row))) in
          let _ = restrict (boundLower (G, decomp, value)) in
          restrictBB resultL
      | BranchDivide (row, BranchFail, resultR) ->
          let value = fromInteger (ceiling (const row)) in
          let decomp = (zero, [(one, (Row row))]) in
          let G = ownerContext ((fun r -> r.owner) (label (Row row))) in
          let _ = restrict (boundUpper (G, decomp, value)) in
          restrictBB resultR
      | BranchSucceed result ->
          (match result with | SOME row -> minimizeBB row | NONE -> ())
      | _ -> ()
    let rec undo =
      function
      | Insert (Row row) ->
          (((fun r -> r.dead)
              (Array.sub (((fun r -> r.rlabels) tableau), row)))
             := true__;
           clearArray2Row
             (((fun r -> r.coeffs) tableau), row, (0, (nCols ())));
           Array.update (((fun r -> r.consts) tableau), row, zero);
           decrNRows ())
      | Insert (Col col) ->
          (((fun r -> r.dead)
              (Array.sub (((fun r -> r.clabels) tableau), col)))
             := true__;
           clearArray2Col
             (((fun r -> r.coeffs) tableau), col, (0, (nRows ())));
           decrNCols ())
      | Pivot (row, col) -> pivot (row, col)
      | Kill pos -> ((fun r -> r.dead) (label pos)) := false__
      | Restrict pos -> ((fun r -> r.restr) (label pos)) := NONE
      | UpdateOwner (pos, owner, tag) -> setOwnership (pos, owner, tag)
    let rec reset () =
      let l =
        {
          owner = (Exp (Null, (Sum (zero_int, nil))));
          tag = (ref 0);
          restr = (ref NONE);
          dead = (ref true__)
        } in
      Array.modify (function | _ -> l)
        (((fun r -> r.rlabels) tableau), 0, (nRows ()));
      Array.modify (function | _ -> l)
        (((fun r -> r.clabels) tableau), 0, (nCols ()));
      Array.modify (function | _ -> zero)
        (((fun r -> r.consts) tableau), 0, (nRows ()));
      Array2.modify Array2.RowMajor (function | _ -> zero)
        {
          base = ((fun r -> r.coeffs) tableau);
          row = 0;
          col = 0;
          nrows = (nRows ());
          ncols = (nCols ())
        };
      ((fun r -> r.nrows) tableau) := 0;
      ((fun r -> r.ncols) tableau) := 0;
      Trail.reset ((fun r -> r.trail) tableau)
    let rec mark () = Trail.mark ((fun r -> r.trail) tableau)
    let rec unwind () = Trail.unwind (((fun r -> r.trail) tableau), undo)
    let rec fst =
      function
      | (App (U1, _), s) -> (U1, s)
      | (SClo (S, s'), s) -> fst (S, (comp (s', s)))
    let rec snd =
      function
      | (App (U1, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, (comp (s', s)))
    let rec isConstantExp (U) =
      match fromExp (U, id) with | Sum (m, nil) -> SOME m | _ -> NONE
    let rec isZeroExp (U) =
      match isConstantExp U with | SOME d -> d = zero_int | NONE -> false__
    let rec solveGeq =
      function
      | (G, S, 0) ->
          let solveGeq0 (W) =
            match isConstantExp W with
            | SOME d ->
                if Integers.(>=) (d, zero_int)
                then geqNExp d
                else raise Error
            | NONE ->
                let proof = newEVar (G, (geq0 W)) in
                let _ =
                  restrictBB
                    (exploreBB ((insert (G, (W, id))), (Restr (G, proof)))) in
                proof in
          let U1 = EClo (fst (S, id)) in
          let U2 = EClo (snd (S, id)) in
          (try
             if isZeroExp U2
             then SOME (solveGeq0 U1)
             else
               (let W = minus (U1, U2) in
                let proof = solveGeq0 W in
                SOME (geqAdd (W, (constant zero_int), U2, proof)))
           with | Error -> NONE)
      | (G, S, n) -> NONE
    let rec pi (name, U, V) = Pi (((Dec ((SOME name), U)), Maybe), V)
    let rec arrow (U, V) = Pi (((Dec (NONE, U)), No), V)
    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          (csid,
            (function
             | MyFgnCnstrRep tag -> toInternal tag
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Awake.install
          (csid,
            (function
             | MyFgnCnstrRep tag -> awake tag
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Simplify.install
          (csid,
            (function
             | MyFgnCnstrRep tag -> simplify tag
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      ()
    let rec init (cs, installF) =
      myID := cs;
      (:=) geqID installF
        ((ConDec
            (">=", NONE, 0, (Constraint ((!myID), solveGeq)),
              (arrow ((number ()), (arrow ((number ()), (Uni Type))))), Kind)),
          (SOME (FX.Infix (FX.minPrec, FX.None))),
          [MS.Mapp
             ((MS.Marg (MS.Star, NONE)),
               (MS.Mapp ((MS.Marg (MS.Star, NONE)), MS.Mnil)))]);
      (:=) geqAddID installF
        ((ConDec
            ("+>=", NONE, 2, Normal,
              (pi
                 ("X", (number ()),
                   (pi
                      ("Y", (number ()),
                        (pi
                           ("Z", (number ()),
                             (arrow
                                ((geq
                                    ((Root ((BVar 3), Nil)),
                                      (Root ((BVar 2), Nil)))),
                                  (geq
                                     ((plus
                                         ((Root ((BVar 4), Nil)),
                                           (Root ((BVar 2), Nil)))),
                                       (plus
                                          ((Root ((BVar 3), Nil)),
                                            (Root ((BVar 2), Nil)))))))))))))),
              Type)), NONE, nil);
      installFgnCnstrOps ();
      ()
    let ((solver)(*! structure CSManager = CSManager !*)
      (* CSM.ModeSyn *)(* useful integer values *)
      (* solver ID of this solver *)(* constant IDs of the declared type constants *)
      (* constructors for the declared types *)(* specialized constructors for the declared types *)
      (* constant IDs of the declared object constants *)
      (* constructors for the declared objects *)(* constant declaration for the proof object d>=0 *)
      (* foreign constant for the proof object d>=0 *)
      (* parsing proof objects d>=0 *)(* Position of a tableau entry       *)
      (* Owner of an entry:                *)(*   - monomial                      *)
      (*   - sum                           *)(* Restriction: (proof object)       *)
      (*   Restr (G, U)                    *)(* owner of the row/column (if any)  *)
      (* tag: used to keep track of the    *)(* position of a tableau entry       *)
      (* restriction (if any)              *)(* has the row/column already been   *)
      (* solved?                           *)(* Undoable operations:              *)
      (* insert a new row/column           *)(* pivot on (i, j)                   *)
      (* mark the given position solved    *)(* restrict the given position       *)
      (* change the owner                  *)(* Tableau:                          *)
      (* row labels                        *)(* column labels                     *)
      (* constant terms                    *)(* variables coefficients            *)
      (* dimensions                        *)(* undo mechanism                    *)
      (* FgnCnstr representation *)(* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for i >= !nrows or j > !ncols, where "vacuous" is the vacuous label:
          #owner(vacuous) = Exp (Null, Sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *)
      (* little random generation routine taken from Paulson '91 *)
      (* create a new (empty) tableau *)(* i-th tableau row label *)
      (* j-th tableau column label *)(* i-th tableau constant term *)
      (* coefficient in row i, column j *)(* number of rows *)
      (* number of columns *)(* increase the number of rows, and return the index of the last row *)
      (* increase the number of columns, and return the index of the last column *)
      (* decrease the number of rows *)(* decrease the number of columns *)
      (* increase by the given amount the element i of the array *)
      (* increase by the given amount the element (i, j) of the array *)
      (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *)
      (* increase by f(i') all the elements (i', j), with i <= i' < i+len *)
      (* set the given row to zero *)(* set the given column to zero *)
      (* return the label at the given position (row or column) *)
      (* return the restriction on the given label *)
      (* is the given label is restricted? *)(* return true iff the given label has been solved *)
      (* set the ownership of the given position *)(* return the context of a owner *)
      (* return the owner as a sum *)(* debugging code - REMOVE *)
      (* debugging code - REMOVE *)(* debugging code - REMOVE *)
      (* find the given monomial in the tableau *)(* return the a position in the tableau of the tagged expression *)
      (* return true iff the given row is null at all the active columns *)
      (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *)
      (* the candidates are those (active) rows with the same constant
                       term *)
      (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)
      (* compute the list of non-null coefficients in the row *)
      (* find the coordinates of the pivot which gives the largest increase in
        const(row) *)
      (* extend Integers.compare to deal with NONE (= infinity) *)
      (* find the best pivot candidates for the given row *)
      (* find the best pivot candidates for the given row and column *)
      (* always choose the smallest *)(* always choose the largest *)
      (* choose one randomly to ensure fairness *)(* pivot the element at the given coordinates *)
      (* same row as the pivot *)(* any other row *)
      (* pivot *)(* same row as the pivot *)(* same column as the pivot *)
      (* any other row/column *)(* delay all terms of a monomial on the given constraint *)
      (* unify two restrictions *)(* unify a sum with a number *)
      (* decomposition of an expression as the weighted sum of tableau positions *)
      (* change sign to the given decomposition *)(* Result of maximization of a row:             *)
      (* nonnegative value c                          *)
      (* manifestly unbounded, pivoting on column col *)
      (* decompose a sum in whnf into a weighted sum of tableau positions *)
      (* maximize the given row by performing pivot operations.
       Return a term of type MaximizeResult *)
      (* the tableau is unbounded *)(* insert the given expression in the tableau, labelling it with owner *)
      (* add the decomposition to the newly created row *)
      (* is this row trivial? *)(* log the creation of this row *)
      (* return its position *)(* insert the given (unrestricted) expression in the tableau *)
      (* restrict the given row/column to be nonnegative *)
      (* compute the list of non-null row entries *)
      (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *)
      (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)
      (* it is an integer *)(* insert the equality Var(pos) = Us as two inequalities:
         Var(pos) - Us >= zero
         Us - Var(pos) >= zero
    *)
      (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *)
      (* update the tableau upon discovery that Var(pos) = sum *)
      (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
      (* analyze the given position to see exactly how to represent this
                 equality *)
      (* find out why it died *)(* row is dead because constant and equal to n *)
      (* row is dead because is subsumed by another *)
      (* column is dead because = 0 *)(* the nf is another variable *)
      (* recycle the current label *)(* insert the proof term used to restrict l (if any) at the beginning of UL *)
      (* returns the list of unsolved constraints associated with the given position *)
      (* returns the list of unsolved constraints associated with the given tag *)
      (* awake function for tableau constraints *)(* simplify function for tableau constraints *)
      (* create a foreign constraint for the given tag *)
      (* checks if the (primally and dually) feasible solution is an integral solution;
       returns NONE if it is, otherwise the coordinate of a non-integral component *)
      (* unbounded component *)(* bound the given expression below d *)
      (* bound the given expression above d *)(* explore the relaxed solution space looking for integer solutions *)
      (* minimize a tableau that has been determined non-minimal (but consistent) as a
       consequence of adding the given row
    *)
      (* check if the column is zero for all possible solutions *)
      (* equate the given column to zero if coeff(row, j) <> zero *)
      (* mark the column dead *)(* if restricted, instantiate the proof object to 0>=0 *)
      (* if owned by a monomial, unify it with zero *)
      (* find out if the given row has been made trivial by killing some columns *)
      (* row is now constant and equal to n = const(i) *)
      (* check if it is an integer *)(* mark the row dead *)
      (* if restricted, instantiate the proof object to n>=0 *)(* if owned by a monomial, unify it with n *)
      (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *)
      (* undo function for trailing tableau operations *)
      (* reset the internal status of the tableau *)
      (* trailing functions *)(* fst (S, s) = U1, the first argument in S[s] *)
      (* snd (S, s) = U2, the second argument in S[s] *)
      (* checks if the given foreign term can be simplified to a constant *)
      (* checks if the given foreign term can be simplified to zero *)
      (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *)
      (* constructors for higher-order types *)(* install the signature *))
      =
      ({
         name = "inequality/integers";
         keywords = "arithmetic,inequality";
         needs = ["Unify"; ((fun r -> r.name)) CSEqIntegers.solver];
         fgnConst = (SOME { parse = parseGeqN });
         init;
         reset;
         mark;
         unwind
       } : CSManager.solver)
  end;;
