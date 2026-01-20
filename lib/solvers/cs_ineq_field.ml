
module CSIneqField(CSIneqField:sig
                                 module OrderedField : ORDERED_FIELD
                                 module Trail : TRAIL
                                 module Unify : UNIFY
                                 module SparseArray : SPARSE_ARRAY
                                 module SparseArray2 : SPARSE_ARRAY2
                                 module CSEqField : CS_EQ_FIELD
                                 module Compat : COMPAT
                               end) : CS =
  struct
    open IntSyn
    open OrderedField
    open CSEqField
    module FX = CSManager.Fixity
    module MS = ModeSyn
    module Array = SparseArray
    module Array2 = SparseArray2
    let myID = (ref (-1) : cid ref)
    let gtID = (ref (-1) : cid ref)
    let geqID = (ref (-1) : cid ref)
    let rec gt (__U) (__V) =
      Root ((Const (!gtID)), (App (__U, (App (__V, Nil)))))
    let rec geq (__U) (__V) =
      Root ((Const (!geqID)), (App (__U, (App (__V, Nil)))))
    let rec gt0 (__U) = gt (__U, (constant zero))
    let rec geq0 (__U) = geq (__U, (constant zero))
    let gtAddID = (ref (-1) : cid ref)
    let geqAddID = (ref (-1) : cid ref)
    let gtGeqID = (ref (-1) : cid ref)
    let geq00ID = (ref (-1) : cid ref)
    let rec gtAdd (__U1) (__U2) (__V) (__W) =
      Root
        ((Const (!gtAddID)),
          (App (__U1, (App (__U2, (App (__V, (App (__W, Nil)))))))))
    let rec geqAdd (__U1) (__U2) (__V) (__W) =
      Root
        ((Const (!geqAddID)),
          (App (__U1, (App (__U2, (App (__V, (App (__W, Nil)))))))))
    let rec gtGeq (__U) (__V) (__W) =
      Root ((Const (!gtGeqID)), (App (__U, (App (__V, (App (__W, Nil)))))))
    let rec geq00 () = Root ((Const (!geq00ID)), Nil)
    let rec gtNConDec d =
      ConDec
        (((^) ((toString d) ^ ">") toString zero), None, 0, Normal,
          (gt0 (constant d)), Type)
    let rec gtNExp d = Root ((FgnConst ((!myID), (gtNConDec d))), Nil)
    let rec geqN0 d =
      if d = zero
      then geq00 ()
      else gtGeq ((constant d), (constant zero), (gtNExp d))
    let rec parseGtN string =
      let suffix = ">" ^ (toString zero) in
      let stringLen = String.size string in
      let suffixLen = String.size suffix in
      let numLen = Int.(-) (stringLen, suffixLen) in
      if
        (Int.(>) (stringLen, suffixLen)) &&
          ((String.substring (string, numLen, suffixLen)) = suffix)
      then
        match fromString (String.substring (string, 0, numLen)) with
        | Some d -> (if d > zero then Some (gtNConDec d) else None)
        | None -> None
      else None
    type __Position =
      | Row of int 
      | Col of int 
    type __Owner =
      | Var of (IntSyn.dctx * __Mon) 
      | Exp of (IntSyn.dctx * __Sum) 
    type __Restriction =
      | Restr of (IntSyn.dctx * IntSyn.__Exp * bool) 
    type nonrec label =
      <
        owner: __Owner
          (* restriction (if any)              *)(* position of a tableau entry       *)
          (* tag: used to keep track of the    *)(* owner of the row/column (if any)  *)
          ;tag: int ref  ;restr: __Restriction option ref  ;dead: bool ref  
        > 
    type __Operation =
      | Insert of __Position 
      | Pivot of (int * int) 
      | Kill of __Position 
      | Restrict of __Position 
      | UpdateOwner of (__Position * __Owner * int ref) 
    type nonrec tableau =
      <
        rlabels: label Array.array
          (* dimensions                        *)(* variables coefficients            *)
          (* constant terms                    *)(* column labels                     *)
          (* row labels                        *) ;clabels: 
                                                                    label
                                                                    Array.array
                                                                     ;
        consts: number Array.array  ;coeffs: number Array2.array  ;nrows: 
                                                                    int ref  ;
        ncols: int ref  ;trail: __Operation Trail.trail   > 
    exception MyFgnCnstrRep of int ref 
    exception Error 
    let a = 16807.0
    let m = 2147483647.0
    let seed = ref 1999.0
    let rec rand min size =
      let rec nextrand () =
        let t = Real.( * ) (a, (!seed)) in
        (:=) seed Real.(-)
          (t, (Real.( * ) (m, (Real.fromInt (Real.floor (t / m))))));
        (/) (Real.(-) ((!seed), 1.0)) Real.(-) (m, 1.0) in
      Int.(+)
        (min, (Real.floor (Real.( * ) ((nextrand ()), (Real.fromInt size)))))
    let tableau =
      let l =
        {
          owner = (Exp (Null, (Sum (zero, nil))));
          tag = (ref 0);
          restr = (ref None);
          dead = (ref true)
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
    let rec coeff i j = Array2.sub (((fun r -> r.coeffs) tableau), i, j)
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
    let rec incrArray array i value =
      Array.update (array, i, ((Array.sub (array, i)) + value))
    let rec incrArray2 array i j value =
      Array2.update (array, i, j, ((Array2.sub (array, i, j)) + value))
    let rec incrArray2Row array i (j, len) f =
      Compat.Vector.mapi
        (fun j -> fun value -> Array2.update (array, i, j, ((+) value f j)))
        (Array2.row (array, i, (j, len)))
    let rec incrArray2Col array j (i, len) f =
      Compat.Vector.mapi
        (fun i -> fun value -> Array2.update (array, i, j, ((+) value f i)))
        (Array2.column (array, j, (i, len)))
    let rec clearArray2Row array i (j, len) =
      Compat.Vector.mapi
        (fun j -> fun value -> Array2.update (array, i, j, zero))
        (Array2.row (array, i, (j, len)))
    let rec clearArray2Col array j (i, len) =
      Compat.Vector.mapi
        (fun i -> fun value -> Array2.update (array, i, j, zero))
        (Array2.column (array, j, (i, len)))
    let rec label = function | Row i -> rlabel i | Col j -> clabel j
    let rec restriction l = !((fun r -> r.restr) l)
    let rec restricted l =
      match restriction l with | Some _ -> true | None -> false
    let rec dead l = !((fun r -> r.dead) l)
    let rec setOwnership pos owner tag =
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
    let rec ownerContext =
      function | Var (__G, mon) -> __G | Exp (__G, sum) -> __G
    let rec ownerSum =
      function | Var (__G, mon) -> Sum (zero, [mon]) | Exp (__G, sum) -> sum
    let rec displayPos =
      function
      | Row row -> print (((^) "row " Int.toString row) ^ "\n")
      | Col col -> print (((^) "column " Int.toString col) ^ "\n")
    let rec displaySum =
      function
      | Sum (m, (Mon (n, _))::monL) ->
          (print (OrderedField.toString n);
           print " ? + ";
           displaySum (Sum (m, monL)))
      | Sum (m, nil) -> (print (OrderedField.toString m); print " >= 0\n")
    let rec display () =
      let rec printLabel col (l : label) =
        print "\t";
        (match (fun r -> r.owner) l with
         | Var _ -> print "V"
         | Exp _ -> print "E");
        if restricted l then print ">" else print "*";
        if dead l then print "#" else print "" in
      let rec printRow row (l : label) =
        let rec printCol col (d : number) = print "\t"; print (toString d) in
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
        (fun _ ->
           fun (l : label) -> displaySum (ownerSum ((fun r -> r.owner) l)))
        (((fun r -> r.clabels) tableau), 0, (nCols ()));
      print "Rows:\n";
      Array.app
        (fun _ ->
           fun (l : label) -> displaySum (ownerSum ((fun r -> r.owner) l)))
        (((fun r -> r.rlabels) tableau), 0, (nRows ()))
    let rec findMon mon =
      let exception Found of int  in
        let rec find i (l : label) =
          match (fun r -> r.owner) l with
          | Var (__G, mon') ->
              if compatibleMon (mon, mon') then raise (Found i) else ()
          | _ -> () in
        try
          Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
          (try
             Array.app find (((fun r -> r.rlabels) tableau), 0, (nRows ()));
             None
           with | Found i -> Some (Row i))
        with | Found j -> Some (Col j)
    let rec findTag t =
      let exception Found of int  in
        let rec find i (l : label) =
          if ((fun r -> r.tag) l) = t then raise (Found i) else () in
        try
          Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
          (try
             Array.app find (((fun r -> r.rlabels) tableau), 0, (nRows ()));
             None
           with | Found i -> Some (Row i))
        with | Found j -> Some (Col j)
    let rec isConstant row =
      Array.foldl
        (fun j ->
           fun l ->
             fun rest -> ((dead l) || ((coeff (row, j)) = zero)) && rest)
        true (((fun r -> r.clabels) tableau), 0, (nCols ()))
    let rec isSubsumed row =
      let constRow = const row in
      let rec isSubsumedByRow () =
        let candidates =
          Array.foldl
            (fun i ->
               fun (l : label) ->
                 fun rest ->
                   if
                     (i <> row) && ((not (dead l)) && ((const i) = constRow))
                   then i :: rest
                   else rest) nil
            (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
        let rec filter __0__ __1__ __2__ =
          match (__0__, __1__, __2__) with
          | (j, l, nil) -> nil
          | (j, (l : label), candidates) ->
              if not (dead l)
              then
                List.filter (fun i -> (=) (coeff (i, j)) coeff (row, j))
                  candidates
              else candidates in
        ((match Array.foldl filter candidates
                  (((fun r -> r.clabels) tableau), 0, (nCols ()))
          with
          | nil -> None
          | i::_ -> Some i)
          (* the candidates are those (active) rows with the same constant
                       term *)
          (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)) in
      let rec isSubsumedByCol () =
        if constRow = zero
        then
          let nonNull =
            Array.foldl
              (fun j ->
                 fun (l : label) ->
                   fun rest ->
                     if not (dead l)
                     then
                       let value = coeff (row, j) in
                       (if value <> zero then (j, value) :: rest else rest)
                     else rest) nil
              (((fun r -> r.clabels) tableau), 0, (nCols ())) in
          ((match nonNull with
            | (j, value)::[] -> (if value = one then Some j else None)
            | _ -> None)
            (* compute the list of non-null coefficients in the row *))
        else None in
      match isSubsumedByRow () with
      | Some i -> Some (Row i)
      | None ->
          (match isSubsumedByCol () with
           | Some j -> Some (Col j)
           | None -> None)
    let rec findPivot row =
      let rec compareScore __3__ __4__ =
        match (__3__, __4__) with
        | (Some d, Some d') -> compare (d, d')
        | (Some d, None) -> LESS
        | (None, Some d') -> GREATER
        | (None, None) -> EQUAL in
      let rec findPivotCol j (l : label) ((score, champs) as result) =
        let value = coeff (row, j) in
        let rec findPivotRow sgn i (l : label) ((score, champs) as result) =
          let value = coeff (i, j) in
          if
            (not (dead l)) &&
              ((i <> row) &&
                 ((restricted l) && (((fromInt sgn) * value) < zero)))
          then
            let score' = Some (abs (( * ) (const i) inverse value)) in
            ((match compareScore (score, score') with
              | GREATER -> (score', [(i, j)])
              | EQUAL -> (score, ((i, j) :: champs))
              | LESS -> result)
              (* always choose the smallest *))
          else result in
        ((if
            (not (dead l)) &&
              ((value <> zero) && ((not (restricted l)) || (value > zero)))
          then
            let (score', champs') as result' =
              Array.foldl (findPivotRow (sign value)) (None, [(row, j)])
                (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
            ((match compareScore (score, score') with
              | GREATER -> result
              | EQUAL -> (score, (champs @ champs'))
              | LESS -> result')
              (* always choose the largest *))
          else result)
          (* find the best pivot candidates for the given row and column *)) in
      ((match Array.foldl findPivotCol ((Some zero), nil)
                (((fun r -> r.clabels) tableau), 0, (nCols ()))
        with
        | (_, nil) -> None
        | (_, champs) ->
            Some (List.nth (champs, (rand (0, (List.length champs))))))
        (* choose one randomly to ensure fairness *)
        (* extend Field.compare to deal with None (= infinity) *)
        (* find the best pivot candidates for the given row *))
    let rec pivot row col =
      let pCoeffInverse = inverse (coeff (row, col)) in
      let pRowVector =
        Array2.row (((fun r -> r.coeffs) tableau), row, (0, (nCols ()))) in
      let rec pRow j = Vector.sub (pRowVector, j) in
      let pColVector =
        Array2.column (((fun r -> r.coeffs) tableau), col, (0, (nRows ()))) in
      let rec pCol i = Vector.sub (pColVector, i) in
      let pConst = const row in
      let pRLabel = rlabel row in
      let pCLabel = clabel col in
      Array.modify
        (fun i ->
           fun value ->
             ((if i = row
               then ~ (value * pCoeffInverse)
               else value - ((( * ) pConst pCol i) * pCoeffInverse))
             (* same row as the pivot *)(* any other row *)))
        (((fun r -> r.consts) tableau), 0, (nRows ()));
      Array2.modify Array2.ColMajor
        (fun i ->
           fun j ->
             fun value ->
               ((match ((i = row), (j = col)) with
                 | (true, true) -> pCoeffInverse
                 | (true, false) -> ~ (value * pCoeffInverse)
                 | (false, true) -> value * pCoeffInverse
                 | (false, false) ->
                     value - ((( * ) (pRow j) pCol i) * pCoeffInverse))
               (* pivot *)(* same row as the pivot *)
               (* same column as the pivot *)(* any other row/column *)))
        {
          base = ((fun r -> r.coeffs) tableau);
          row = 0;
          col = 0;
          nrows = (nRows ());
          ncols = (nCols ())
        };
      Array.update (((fun r -> r.rlabels) tableau), row, pCLabel);
      Array.update (((fun r -> r.clabels) tableau), col, pRLabel)
    type __MaximizeResult =
      | Positive 
      | Maximized of number 
      | Unbounded of int 
    let rec maximizeRow row =
      let value = const row in
      if value <= zero
      then
        match findPivot row with
        | Some (i, j) ->
            (if i <> row
             then
               (Trail.log (((fun r -> r.trail) tableau), (Pivot (i, j)));
                pivot (i, j);
                maximizeRow row)
             else Unbounded j)
        | None -> Maximized value
      else Positive
    let rec delayMon (Mon (n, UsL)) cnstr =
      List.app (fun (__Us) -> Unify.delay (__Us, cnstr)) UsL
    let rec unifyRestr (Restr (__G, proof, strict)) proof' =
      if Unify.unifiable (__G, (proof, id), (proof', id))
      then ()
      else raise Error
    let rec unifySum (__G) sum d =
      if Unify.unifiable (__G, ((toExp sum), id), ((constant d), id))
      then ()
      else raise Error
    type nonrec decomp = (number * (number * __Position) list)
    let rec unaryMinusDecomp d wposL =
      ((~ d), (List.map (fun d -> fun pos -> ((~ d), pos)) wposL))
    let rec decomposeSum (__G) (Sum (m, monL)) =
      let rec monToWPos (Mon (n, UsL) as mon) =
        match findMon mon with
        | Some pos -> (n, pos)
        | None ->
            let new__ = incrNCols () in
            let l =
              {
                owner = (Var (__G, (Mon (one, UsL))));
                tag = (ref 0);
                restr = (ref None);
                dead = (ref false)
              } in
            (Trail.log (((fun r -> r.trail) tableau), (Insert (Col new__)));
             delayMon (mon, (ref (makeCnstr ((fun r -> r.tag) l))));
             Array.update (((fun r -> r.clabels) tableau), new__, l);
             (n, (Col new__))) in
      (m, (List.map monToWPos monL))
    let rec insertDecomp ((d, wposL) as decomp) owner =
      let new__ = incrNRows () in
      let rec insertWPos d pos =
        match pos with
        | Row row ->
            (incrArray2Row
               (((fun r -> r.coeffs) tableau), new__, (0, (nCols ())),
                 (fun j -> ( * ) d coeff (row, j)));
             incrArray
               (((fun r -> r.consts) tableau), new__, (( * ) d const row)))
        | Col col ->
            incrArray2 (((fun r -> r.coeffs) tableau), new__, col, d) in
      ((List.app insertWPos wposL;
        incrArray (((fun r -> r.consts) tableau), new__, d);
        (match isSubsumed new__ with
         | Some pos ->
             (clearArray2Row
                (((fun r -> r.coeffs) tableau), new__, (0, (nCols ())));
              Array.update (((fun r -> r.consts) tableau), new__, zero);
              decrNRows ();
              pos)
         | None ->
             (((setOwnership ((Row new__), owner, (ref 0));
                (:=) (((fun r -> r.dead)) (label (Row new__))) isConstant
                  new__;
                Trail.log
                  (((fun r -> r.trail) tableau), (Insert (Row new__)));
                Row new__))
             (* log the creation of this row *)(* return its position *))))
        (* add the decomposition to the newly created row *)
        (* is this row trivial? *))
    let rec insert (__G) (__Us) =
      let sum = fromExp __Us in
      insertDecomp ((decomposeSum (__G, sum)), (Exp (__G, sum)))
    let rec minimize row =
      let rec killColumn j (l : label) =
        if (not (dead l)) && ((coeff (row, j)) <> zero)
        then
          (((Trail.log (((fun r -> r.trail) tableau), (Kill (Col j)));
             ((fun r -> r.dead)
                (Array.sub (((fun r -> r.clabels) tableau), j)))
               := true;
             (match restriction l with
              | Some restr -> unifyRestr (restr, (geq00 ()))
              | None -> ());
             (match (fun r -> r.owner) l with
              | Var _ as owner ->
                  unifySum ((ownerContext owner), (ownerSum owner), zero)
              | _ -> ())))
          (* mark the column dead *)(* if restricted, instantiate the proof object to 0>=0 *)
          (* if owned by a monomial, unify it with zero *))
        else () in
      let rec killRow i (l : label) =
        if not (dead l)
        then
          (((if isConstant i
             then
               (((Trail.log (((fun r -> r.trail) tableau), (Kill (Row i)));
                  ((fun r -> r.dead)
                     (Array.sub (((fun r -> r.rlabels) tableau), i)))
                    := true;
                  (match restriction l with
                   | Some restr -> unifyRestr (restr, (geqN0 (const i)))
                   | None -> ());
                  (match (fun r -> r.owner) l with
                   | Var _ as owner ->
                       unifySum
                         ((ownerContext owner), (ownerSum owner), (const i))
                   | _ -> ())))
               (* mark the row dead *)(* if restricted, instantiate the proof object to n>=0 *)
               (* if owned by a monomial, unify it with n *))
             else
               (match isSubsumed i with
                | Some pos' ->
                    let l' = label pos' in
                    (Trail.log (((fun r -> r.trail) tableau), (Kill (Row i)));
                     ((fun r -> r.dead)
                        (Array.sub (((fun r -> r.rlabels) tableau), i)))
                       := true;
                     (match ((restriction l), (restriction l')) with
                      | (Some restr, Some (Restr (_, proof', _))) ->
                          unifyRestr (restr, proof')
                      | (Some _, None) ->
                          (((Trail.log
                               (((fun r -> r.trail) tableau),
                                 (Restrict pos'));
                             (:=) (((fun r -> r.restr)) l') restriction l))
                          (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *))
                      | (None, _) -> ()))
                | None -> ())))
          (* row is now constant and equal to n = const(i) *))
        else () in
      ((Array.app killColumn (((fun r -> r.clabels) tableau), 0, (nCols ()));
        Array.app killRow (((fun r -> r.rlabels) tableau), 0, (nRows ())))
        (* equate the given column to zero if coeff(row, j) <> zero *)
        (* find out if the given row has been made trivial by killing some
               columns
            *))
    let rec restrict __5__ __6__ =
      match (__5__, __6__) with
      | ((Col col as pos), restr) ->
          let l = label pos in
          if dead l
          then unifyRestr (restr, (geq00 ()))
          else
            (match restriction l with
             | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
             | None ->
                 let nonNull =
                   Array.foldl
                     (fun i ->
                        fun (l : label) ->
                          fun rest ->
                            if not (dead l)
                            then
                              let value = coeff (i, col) in
                              (if value <> zero then i :: rest else rest)
                            else rest) nil
                     (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
                 (((match nonNull with
                    | row::_ ->
                        (((Trail.log
                             (((fun r -> r.trail) tableau),
                               (Pivot (row, col)));
                           pivot (row, col);
                           restrict ((Row row), restr)))
                        (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *))
                    | nil ->
                        (((Trail.log
                             (((fun r -> r.trail) tableau),
                               (Restrict (Col col)));
                           (:=) (((fun r -> r.restr)) (label (Col col))) Some
                             restr))
                        (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *))))
                   (* compute the list of non-null row entries *)))
      | ((Row row as pos), restr) ->
          let l = label pos in
          if dead l
          then unifyRestr (restr, (geqN0 (const row)))
          else
            (match restriction l with
             | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
             | None ->
                 (match maximizeRow row with
                  | Unbounded col ->
                      (Trail.log
                         (((fun r -> r.trail) tableau), (Restrict (Row row)));
                       (:=) (((fun r -> r.restr))
                               (Array.sub
                                  (((fun r -> r.rlabels) tableau), row)))
                         Some restr;
                       if (const row) < zero
                       then
                         (Trail.log
                            (((fun r -> r.trail) tableau),
                              (Pivot (row, col)));
                          pivot (row, col))
                       else ())
                  | Positive ->
                      (((Trail.log
                           (((fun r -> r.trail) tableau),
                             (Restrict (Row row)));
                         (:=) (((fun r -> r.restr))
                                 (Array.sub
                                    (((fun r -> r.rlabels) tableau), row)))
                           Some restr))
                      (* the tableau is satisfiable and minimal *))
                  | Maximized value ->
                      if value = zero
                      then
                        (((Trail.log
                             (((fun r -> r.trail) tableau),
                               (Restrict (Row row)));
                           (:=) (((fun r -> r.restr))
                                   (Array.sub
                                      (((fun r -> r.rlabels) tableau), row)))
                             Some restr;
                           minimize row))
                        (* the tableau is satisfiable but not minimal*))
                      else raise Error))
    let rec insertEqual (__G) pos sum =
      let (m, wposL) = decomposeSum (__G, sum) in
      let decomp' = (m, (((~ one), pos) :: wposL)) in
      let pos' = insertDecomp (decomp', (Exp (__G, (Sum (zero, nil))))) in
      let decomp'' = unaryMinusDecomp decomp' in
      let tag'' =
        (fun r -> r.tag)
          (label (insertDecomp (decomp'', (Exp (__G, (Sum (zero, nil))))))) in
      ((restrict (pos', (Restr (__G, (geq00 ()), false)));
        (match findTag tag'' with
         | Some pos'' -> restrict (pos'', (Restr (__G, (geq00 ()), false)))))
        (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *))
    let rec update (__G) pos sum =
      let l = label pos in
      ((Trail.log
          (((fun r -> r.trail) tableau),
            (UpdateOwner (pos, ((fun r -> r.owner) l), ((fun r -> r.tag) l))));
        setOwnership (pos, (Exp (__G, sum)), (ref 0));
        if dead l
        then
          (((match pos with
             | Row row ->
                 ((if isConstant row
                   then unifySum (__G, sum, (const row))
                   else
                     (match isSubsumed row with
                      | Some pos' -> update (__G, pos', sum)))
                 (* row is dead because constant and equal to n *)
                 (* row is dead because is subsumed by another *))
             | Col col -> unifySum (__G, sum, zero)))
          (* find out why it died *)(* column is dead because = 0 *))
        else
          (let rec isVar =
             function
             | Sum (m, (Mon (n, _) as mon)::[]) ->
                 if (m = zero) && (n = one) then Some mon else None
             | sum -> None in
           ((match isVar sum with
             | Some mon ->
                 (match findMon mon with
                  | Some _ -> insertEqual (__G, pos, sum)
                  | None ->
                      let tag = ref 0 in
                      (((Trail.log
                           (((fun r -> r.trail) tableau),
                             (UpdateOwner
                                (pos, ((fun r -> r.owner) l),
                                  ((fun r -> r.tag) l))));
                         setOwnership (pos, (Var (__G, mon)), tag);
                         delayMon (mon, (ref (makeCnstr tag)))))
                        (* recycle the current label *)))
             | None -> insertEqual (__G, pos, sum))
             (* the nf is another variable *))))
        (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
        (* analyze the given position to see exactly how to represent this
                 equality *))
    let rec restrictions pos =
      let rec member x l = List.exists (fun y -> x = y) l in
      let rec test l = (restricted l) && (not (dead l)) in
      let rec reachable __7__ __8__ __9__ =
        match (__7__, __8__, __9__) with
        | ((Row row as pos)::candidates, tried, closure) ->
            if member (pos, tried)
            then reachable (candidates, tried, closure)
            else
              (let new_candidates =
                 Array.foldl
                   (fun col ->
                      fun _ ->
                        fun candidates ->
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
                   (fun row ->
                      fun _ ->
                        fun candidates ->
                          if (coeff (row, col)) <> zero
                          then (Row row) :: candidates
                          else candidates) nil
                   (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
               let closure' =
                 if test (label pos) then pos :: closure else closure in
               reachable
                 ((candidates' @ candidates), (pos :: tried), closure'))
        | (nil, _, closure) -> closure in
      let rec restrExp pos =
        let l = label pos in
        let owner = (fun r -> r.owner) l in
        let __G = ownerContext owner in
        let __U = toExp (ownerSum owner) in
        match restriction (label pos) with
        | Some (Restr (_, _, true)) -> (__G, (gt0 __U))
        | _ -> (__G, (geq0 __U)) in
      List.map restrExp (reachable ([pos], nil, nil))
    let rec makeCnstr tag = FgnCnstr ((!myID), (MyFgnCnstrRep tag))
    let rec toInternal tag () =
      match findTag tag with | None -> nil | Some pos -> restrictions pos
    let rec awake tag () =
      try
        match findTag tag with
        | Some pos ->
            let owner = (fun r -> r.owner) (label pos) in
            let __G = ownerContext owner in
            let sum = normalize (ownerSum owner) in
            (update (__G, pos, sum); true)
        | None -> true
      with | Error -> false
    let rec simplify tag () =
      match toInternal tag () with | nil -> true | _::_ -> false
    let rec undo =
      function
      | Insert (Row row) ->
          (((fun r -> r.dead)
              (Array.sub (((fun r -> r.rlabels) tableau), row)))
             := true;
           clearArray2Row
             (((fun r -> r.coeffs) tableau), row, (0, (nCols ())));
           Array.update (((fun r -> r.consts) tableau), row, zero);
           decrNRows ())
      | Insert (Col col) ->
          (((fun r -> r.dead)
              (Array.sub (((fun r -> r.clabels) tableau), col)))
             := true;
           clearArray2Col
             (((fun r -> r.coeffs) tableau), col, (0, (nRows ())));
           decrNCols ())
      | Pivot (row, col) -> pivot (row, col)
      | Kill pos -> ((fun r -> r.dead) (label pos)) := false
      | Restrict pos -> ((fun r -> r.restr) (label pos)) := None
      | UpdateOwner (pos, owner, tag) -> setOwnership (pos, owner, tag)
    let rec reset () =
      let l =
        {
          owner = (Exp (Null, (Sum (zero, nil))));
          tag = (ref 0);
          restr = (ref None);
          dead = (ref true)
        } in
      Array.modify (fun _ -> l)
        (((fun r -> r.rlabels) tableau), 0, (nRows ()));
      Array.modify (fun _ -> l)
        (((fun r -> r.clabels) tableau), 0, (nCols ()));
      Array.modify (fun _ -> zero)
        (((fun r -> r.consts) tableau), 0, (nRows ()));
      Array2.modify Array2.RowMajor (fun _ -> zero)
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
    let rec fst __10__ __11__ =
      match (__10__, __11__) with
      | (App (__U1, _), s) -> (__U1, s)
      | (SClo (__S, s'), s) -> fst (__S, (comp (s', s)))
    let rec snd __12__ __13__ =
      match (__12__, __13__) with
      | (App (__U1, __S), s) -> fst (__S, s)
      | (SClo (__S, s'), s) -> snd (__S, (comp (s', s)))
    let rec isConstantExp (__U) =
      match fromExp (__U, id) with | Sum (m, nil) -> Some m | _ -> None
    let rec isZeroExp (__U) =
      match isConstantExp __U with | Some d -> d = zero | None -> false
    let rec solveGt __14__ __15__ __16__ =
      match (__14__, __15__, __16__) with
      | (__G, __S, 0) ->
          let rec solveGt0 (__W) =
            match isConstantExp __W with
            | Some d -> if d > zero then gtNExp d else raise Error
            | None ->
                let proof = newEVar (__G, (gt0 __W)) in
                let _ =
                  restrict
                    ((insert (__G, (__W, id))),
                      (Restr
                         (__G, (gtGeq (__W, (constant zero), proof)), true))) in
                proof in
          let __U1 = EClo (fst (__S, id)) in
          let __U2 = EClo (snd (__S, id)) in
          (try
             if isZeroExp __U2
             then Some (solveGt0 __U1)
             else
               (let __W = minus (__U1, __U2) in
                let proof = solveGt0 __W in
                Some (gtAdd (__W, (constant zero), __U2, proof)))
           with | Error -> None)
      | (__G, __S, n) -> None
    let rec solveGeq __17__ __18__ __19__ =
      match (__17__, __18__, __19__) with
      | (__G, __S, 0) ->
          let rec solveGeq0 (__W) =
            match isConstantExp __W with
            | Some d -> if d >= zero then geqN0 d else raise Error
            | None ->
                let proof = newEVar (__G, (geq0 __W)) in
                let _ =
                  restrict
                    ((insert (__G, (__W, id))),
                      (Restr (__G, proof, false))) in
                proof in
          let __U1 = EClo (fst (__S, id)) in
          let __U2 = EClo (snd (__S, id)) in
          (try
             if isZeroExp __U2
             then Some (solveGeq0 __U1)
             else
               (let __W = minus (__U1, __U2) in
                let proof = solveGeq0 __W in
                Some (geqAdd (__W, (constant zero), __U2, proof)))
           with | Error -> None)
      | (__G, __S, n) -> None
    let rec pi name (__U) (__V) = Pi (((Dec ((Some name), __U)), Maybe), __V)
    let rec arrow (__U) (__V) = Pi (((Dec (None, __U)), No), __V)
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
    let rec init cs installF =
      myID := cs;
      (:=) gtID installF
        ((ConDec
            (">", None, 0, (Constraint ((!myID), solveGt)),
              (arrow ((number ()), (arrow ((number ()), (Uni Type))))), Kind)),
          (Some (FX.Infix (FX.minPrec, FX.None))),
          [MS.Mapp
             ((MS.Marg (MS.Star, None)),
               (MS.Mapp ((MS.Marg (MS.Star, None)), MS.Mnil)))]);
      (:=) geqID installF
        ((ConDec
            (">=", None, 0, (Constraint ((!myID), solveGeq)),
              (arrow ((number ()), (arrow ((number ()), (Uni Type))))), Kind)),
          (Some (FX.Infix (FX.minPrec, FX.None))),
          [MS.Mapp
             ((MS.Marg (MS.Star, None)),
               (MS.Mapp ((MS.Marg (MS.Star, None)), MS.Mnil)))]);
      (:=) gtAddID installF
        ((ConDec
            ("+>", None, 2, Normal,
              (pi
                 ("X", (number ()),
                   (pi
                      ("Y", (number ()),
                        (pi
                           ("Z", (number ()),
                             (arrow
                                ((gt
                                    ((Root ((BVar 3), Nil)),
                                      (Root ((BVar 2), Nil)))),
                                  (gt
                                     ((plus
                                         ((Root ((BVar 4), Nil)),
                                           (Root ((BVar 2), Nil)))),
                                       (plus
                                          ((Root ((BVar 3), Nil)),
                                            (Root ((BVar 2), Nil)))))))))))))),
              Type)), None, nil);
      (:=) geqAddID installF
        ((ConDec
            ("+>=", None, 2, Normal,
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
              Type)), None, nil);
      (:=) gtGeqID installF
        ((ConDec
            (">>=", None, 2, Normal,
              (pi
                 ("X", (number ()),
                   (pi
                      ("Y", (number ()),
                        (arrow
                           ((gt
                               ((Root ((BVar 2), Nil)),
                                 (Root ((BVar 1), Nil)))),
                             (geq
                                ((Root ((BVar 3), Nil)),
                                  (Root ((BVar 2), Nil)))))))))), Type)),
          None, nil);
      (:=) geq00ID installF
        ((ConDec ("0>=0", None, 0, Normal, (geq0 (constant zero)), Type)),
          None, nil);
      installFgnCnstrOps ();
      ()
    let solver =
      ({
         name = (("inequality/" ^ OrderedField.name) ^ "s");
         keywords = "arithmetic,inequality";
         needs = ["Unify"; ((fun r -> r.name)) CSEqField.solver];
         fgnConst = (Some { parse = parseGtN });
         init;
         reset;
         mark;
         unwind
       } : CSManager.solver)
  end ;;
