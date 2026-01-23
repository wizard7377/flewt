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
    let rec gt (u_, v_) = Root ((Const !gtID), (App (u_, (App (v_, Nil)))))
    let rec geq (u_, v_) = Root ((Const !geqID), (App (u_, (App (v_, Nil)))))
    let rec gt0 (u_) = gt (u_, (constant zero))
    let rec geq0 (u_) = geq (u_, (constant zero))
    let gtAddID = (ref (-1) : cid ref)
    let geqAddID = (ref (-1) : cid ref)
    let gtGeqID = (ref (-1) : cid ref)
    let geq00ID = (ref (-1) : cid ref)
    let rec gtAdd (u1_, u2_, v_, w_) =
      Root
        ((Const !gtAddID),
          (App (u1_, (App (u2_, (App (v_, (App (w_, Nil)))))))))
    let rec geqAdd (u1_, u2_, v_, w_) =
      Root
        ((Const !geqAddID),
          (App (u1_, (App (u2_, (App (v_, (App (w_, Nil)))))))))
    let rec gtGeq (u_, v_, w_) =
      Root ((Const !gtGeqID), (App (u_, (App (v_, (App (w_, Nil)))))))
    let rec geq00 () = Root ((Const !geq00ID), Nil)
    let rec gtNConDec d =
      ConDec
        (((^) ((toString d) ^ ">") toString zero), None, 0, Normal,
          (gt0 (constant d)), Type)
    let rec gtNExp d = Root ((FgnConst (!myID, (gtNConDec d))), Nil)
    let rec geqN0 d = if d = zero then begin geq00 () end
      else begin gtGeq ((constant d), (constant zero), (gtNExp d)) end
  let rec parseGtN string =
    let suffix = ">" ^ (toString zero) in
    let stringLen = String.size string in
    let suffixLen = String.size suffix in
    let numLen = Int.(-) (stringLen, suffixLen) in
    if
      (Int.(>) (stringLen, suffixLen)) &&
        ((String.substring (string, numLen, suffixLen)) = suffix)
    then
      begin begin match fromString (String.substring (string, 0, numLen))
                  with
            | Some d -> (if d > zero then begin Some (gtNConDec d) end
                else begin None end)
    | None -> None end end else begin None end
type position_ =
  | Row of int 
  | Col of int 
type owner_ =
  | Var of (IntSyn.dctx * mon_) 
  | Exp of (IntSyn.dctx * sum_) 
type restriction_ =
  | Restr of (IntSyn.dctx * IntSyn.exp_ * bool) 
type nonrec label =
  <
    owner: owner_
      (* restriction (if any)              *)(* position of a tableau entry       *)
      (* tag: used to keep track of the    *)(* owner of the row/column (if any)  *)
      ;tag: int ref  ;restr: restriction_ option ref  ;dead: bool ref   > 
type operation_ =
  | Insert of position_ 
  | Pivot of (int * int) 
  | Kill of position_ 
  | Restrict of position_ 
  | UpdateOwner of (position_ * owner_ * int ref) 
type nonrec tableau =
  <
    rlabels: label Array.array
      (* dimensions                        *)(* variables coefficients            *)
      (* constant terms                    *)(* column labels                     *)
      (* row labels                        *) ;clabels: 
                                                                  label
                                                                    Array.array
                                                                   ;consts: 
                                                                    number
                                                                    Array.array
                                                                     ;
    coeffs: number Array2.array  ;nrows: int ref  ;ncols: int ref  ;trail: 
                                                                    operation_
                                                                    Trail.trail
                                                                      > 
exception MyFgnCnstrRep of int ref 
exception Error 
let a = 16807.0
let m = 2147483647.0
let seed = ref 1999.0
let rec rand (min, size) =
  let rec nextrand () =
    let t = Real.( * ) (a, !seed) in
    begin (:=) seed Real.(-)
            (t, (Real.( * ) (m, (Real.fromInt (Real.floor (t / m))))));
    (/) (Real.(-) (!seed, 1.0)) Real.(-) (m, 1.0) end in
Int.(+) (min, (Real.floor (Real.( * ) ((nextrand ()), (Real.fromInt size)))))
let tableau =
  let l =
    {
      owner = (Exp (Null, (Sum (zero, []))));
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
let rec coeff (i, j) = Array2.sub (((fun r -> r.coeffs) tableau), i, j)
let rec nRows () = !((fun r -> r.nrows) tableau)
let rec nCols () = !((fun r -> r.ncols) tableau)
let rec incrNRows () =
  let old = nRows () in
  begin (:=) (((fun r -> r.nrows)) tableau) Int.(+) (old, 1); old end
let rec incrNCols () =
  let old = nCols () in
  begin (:=) (((fun r -> r.ncols)) tableau) Int.(+) (old, 1); old end
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
    (begin function
     | (j, value) -> Array2.update (array, i, j, ((+) value f j)) end)
  (Array2.row (array, i, (j, len)))
let rec incrArray2Col (array, j, (i, len), f) =
  Compat.Vector.mapi
    (begin function
     | (i, value) -> Array2.update (array, i, j, ((+) value f i)) end)
  (Array2.column (array, j, (i, len)))
let rec clearArray2Row (array, i, (j, len)) =
  Compat.Vector.mapi
    (begin function | (j, value) -> Array2.update (array, i, j, zero) end)
  (Array2.row (array, i, (j, len)))
let rec clearArray2Col (array, j, (i, len)) =
  Compat.Vector.mapi
    (begin function | (i, value) -> Array2.update (array, i, j, zero) end)
  (Array2.column (array, j, (i, len)))
let rec label = begin function | Row i -> rlabel i | Col j -> clabel j end
let rec restriction (l : label) = !((fun r -> r.restr) l)
let rec restricted (l : label) =
  begin match restriction l with | Some _ -> true | None -> false end
let rec dead (l : label) = !((fun r -> r.dead) l)
let rec setOwnership (pos, owner, tag) =
  let old = label pos in
  let new_ =
    { owner; tag; restr = (ref (restriction old)); dead = (ref (dead old)) } in
  begin match pos with
  | Row i -> Array.update (((fun r -> r.rlabels) tableau), i, new_)
  | Col j -> Array.update (((fun r -> r.clabels) tableau), j, new_) end
let rec ownerContext =
  begin function | Var (g_, mon) -> g_ | Exp (g_, sum) -> g_ end
let rec ownerSum =
  begin function | Var (g_, mon) -> Sum (zero, [mon]) | Exp (g_, sum) -> sum end
let rec displayPos =
  begin function
  | Row row -> print (((^) "row " Int.toString row) ^ "\n")
  | Col col -> print (((^) "column " Int.toString col) ^ "\n") end
let rec displaySum =
  begin function
  | Sum (m, (Mon (n, _))::monL) ->
      (begin print (OrderedField.toString n);
       print " ? + ";
       displaySum (Sum (m, monL)) end)
  | Sum (m, []) ->
      (begin print (OrderedField.toString m); print " >= 0\n" end) end
let rec display () =
  let rec printLabel (col, (l : label)) =
    begin print "\t";
    (begin match (fun r -> r.owner) l with
     | Var _ -> print "V"
     | Exp _ -> print "E" end);
    if restricted l then begin print ">" end else begin print "*" end;
  if dead l then begin print "#" end else begin print "" end end in
let rec printRow (row, (l : label)) =
let rec printCol (col, (d : number)) =
  begin print "\t"; print (toString d) end in
let vec = Array2.row (((fun r -> r.coeffs) tableau), row, (0, (nCols ()))) in
begin (begin match (fun r -> r.owner) l with
     | Var _ -> print "V"
     | Exp _ -> print "E" end);
if restricted l then begin print ">" end else begin print "*" end;
if dead l then begin print "#" end else begin print "" end; print "\t";
Compat.Vector.mapi printCol vec; print "\t"; print (toString (const row));
print "\n" end in
begin print "\t";
Array.app printLabel (((fun r -> r.clabels) tableau), 0, (nCols ()));
print "\n";
Array.app printRow (((fun r -> r.rlabels) tableau), 0, (nRows ()));
print "Columns:\n";
Array.app
(begin function
 | (_, (l : label)) -> displaySum (ownerSum ((fun r -> r.owner) l)) end)
(((fun r -> r.clabels) tableau), 0, (nCols ())); print "Rows:\n";
Array.app
  (begin function
   | (_, (l : label)) -> displaySum (ownerSum ((fun r -> r.owner) l)) end)
(((fun r -> r.rlabels) tableau), 0, (nRows ())) end
let rec findMon mon =
  let exception Found of int  in
    let rec find (i, (l : label)) =
      begin match (fun r -> r.owner) l with
      | Var (g_, mon') ->
          if compatibleMon (mon, mon') then begin raise (Found i) end
          else begin () end
      | _ -> () end in
begin try
        begin Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
        (begin try
                 begin Array.app find
                         (((fun r -> r.rlabels) tableau), 0, (nRows ()));
                 None end
        with | Found i -> Some (Row i) end) end
with | Found j -> Some (Col j) end
let rec findTag t =
  let exception Found of int  in
    let rec find (i, (l : label)) =
      if ((fun r -> r.tag) l) = t then begin raise (Found i) end
      else begin () end in
begin try
        begin Array.app find (((fun r -> r.clabels) tableau), 0, (nCols ()));
        (begin try
                 begin Array.app find
                         (((fun r -> r.rlabels) tableau), 0, (nRows ()));
                 None end
        with | Found i -> Some (Row i) end) end
with | Found j -> Some (Col j) end
let rec isConstant row =
  Array.foldl
    (begin function
     | (j, l, rest) -> ((dead l) || ((coeff (row, j)) = zero)) && rest end)
  true (((fun r -> r.clabels) tableau), 0, (nCols ()))
let rec isSubsumed row =
  let constRow = const row in
  let rec isSubsumedByRow () =
    let candidates =
      Array.foldl
        (begin function
         | (i, (l : label), rest) ->
             if (i <> row) && ((not (dead l)) && ((const i) = constRow))
             then begin i :: rest end else begin rest end end)
    [] (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
  let rec filter =
    begin function
    | (j, l, []) -> []
    | (j, (l : label), candidates) ->
        if not (dead l)
        then
          begin List.filter
                  (begin function | i -> (=) (coeff (i, j)) coeff (row, j) end)
          candidates end
    else begin candidates end end in
((begin match Array.foldl filter candidates
              (((fun r -> r.clabels) tableau), 0, (nCols ()))
      with
| [] -> None
| i::_ -> Some i end)
(* the candidates are those (active) rows with the same constant
                       term *)
(* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)) in
let rec isSubsumedByCol () =
if constRow = zero
then
  begin let nonNull =
          Array.foldl
            (begin function
             | (j, (l : label), rest) ->
                 if not (dead l)
                 then
                   begin let value = coeff (row, j) in
                         (if value <> zero then begin (j, value) :: rest end
                           else begin rest end) end else begin rest end end)
[] (((fun r -> r.clabels) tableau), 0, (nCols ())) in
((begin match nonNull with
| (j, value)::[] -> (if value = one then begin Some j end else begin None end)
| _ -> None end)
(* compute the list of non-null coefficients in the row *)) end
else begin None end in
begin match isSubsumedByRow () with
| Some i -> Some (Row i)
| None ->
  (begin match isSubsumedByCol () with
   | Some j -> Some (Col j)
   | None -> None end) end
let rec findPivot row =
  let rec compareScore =
    begin function
    | (Some d, Some d') -> compare (d, d')
    | (Some d, None) -> LESS
    | (None, Some d') -> GREATER
    | (None, None) -> EQUAL end in
let rec findPivotCol (j, (l : label), ((score, champs) as result)) =
  let value = coeff (row, j) in
  let rec findPivotRow sgn (i, (l : label), ((score, champs) as result)) =
    let value = coeff (i, j) in
    if
      (not (dead l)) &&
        ((i <> row) && ((restricted l) && (((fromInt sgn) * value) < zero)))
    then
      begin let score' = Some (abs (( * ) (const i) inverse value)) in
            ((begin match compareScore (score, score') with
              | GREATER -> (score', [(i, j)])
              | EQUAL -> (score, ((i, j) :: champs))
              | LESS -> result end)
      (* always choose the smallest *)) end
    else begin result end in
((if
    (not (dead l)) &&
      ((value <> zero) && ((not (restricted l)) || (value > zero)))
  then
    begin let (score', champs') as result' =
            Array.foldl (findPivotRow (sign value)) (None, [(row, j)])
              (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
          ((begin match compareScore (score, score') with
            | GREATER -> result
            | EQUAL -> (score, (champs @ champs'))
            | LESS -> result' end)
    (* always choose the largest *)) end
  else begin result end)
(* find the best pivot candidates for the given row and column *)) in
((begin match Array.foldl findPivotCol ((Some zero), [])
              (((fun r -> r.clabels) tableau), 0, (nCols ()))
      with
| (_, []) -> None
| (_, champs) -> Some (List.nth (champs, (rand (0, (List.length champs))))) end)
(* choose one randomly to ensure fairness *)(* extend Field.compare to deal with NONE (= infinity) *)
(* find the best pivot candidates for the given row *))
let rec pivot (row, col) =
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
  begin Array.modify
          (begin function
           | (i, value) ->
               ((if i = row then begin - (value * pCoeffInverse) end
               else begin value - ((( * ) pConst pCol i) * pCoeffInverse) end)
          (* same row as the pivot *)(* any other row *)) end)
    (((fun r -> r.consts) tableau), 0, (nRows ()));
    Array2.modify Array2.ColMajor
      (begin function
       | (i, j, value) ->
           (((begin match ((i = row), (j = col)) with
              | (true, true) -> pCoeffInverse
              | (true, false) -> - (value * pCoeffInverse)
              | (false, true) -> value * pCoeffInverse
              | (false, false) ->
                  value - ((( * ) (pRow j) pCol i) * pCoeffInverse) end))
       (* pivot *)(* same row as the pivot *)(* same column as the pivot *)
       (* any other row/column *)) end)
    {
      base = ((fun r -> r.coeffs) tableau);
      row = 0;
      col = 0;
      nrows = (nRows ());
      ncols = (nCols ())
    }; Array.update (((fun r -> r.rlabels) tableau), row, pCLabel);
    Array.update (((fun r -> r.clabels) tableau), col, pRLabel) end
type maximizeResult_ =
  | Positive 
  | Maximized of number 
  | Unbounded of int 
let rec maximizeRow row =
  let value = const row in
  if value <= zero
  then
    begin begin match findPivot row with
          | Some (i, j) ->
              (if i <> row
               then
                 begin (begin Trail.log
                                (((fun r -> r.trail) tableau),
                                  (Pivot (i, j)));
                        pivot (i, j);
                        maximizeRow row end) end
          else begin Unbounded j end)
    | None -> Maximized value end end
else begin Positive end
let rec delayMon (Mon (n, UsL), cnstr) =
  List.app (begin function | us_ -> Unify.delay (us_, cnstr) end) UsL
let rec unifyRestr (Restr (g_, proof, strict), proof') =
  if Unify.unifiable (g_, (proof, id), (proof', id)) then begin () end
  else begin raise Error end
let rec unifySum (g_, sum, d) =
  if Unify.unifiable (g_, ((toExp sum), id), ((constant d), id))
  then begin () end else begin raise Error end
type nonrec decomp = (number * (number * position_) list)
let rec unaryMinusDecomp (d, wposL) =
  ((- d), (List.map (begin function | (d, pos) -> ((- d), pos) end) wposL))
let rec decomposeSum (g_, Sum (m, monL)) =
  let rec monToWPos (Mon (n, UsL) as mon) =
    begin match findMon mon with
    | Some pos -> (n, pos)
    | None ->
        let new_ = incrNCols () in
        let l =
          {
            owner = (Var (g_, (Mon (one, UsL))));
            tag = (ref 0);
            restr = (ref None);
            dead = (ref false)
          } in
        (begin Trail.log (((fun r -> r.trail) tableau), (Insert (Col new_)));
         delayMon (mon, (ref (makeCnstr ((fun r -> r.tag) l))));
         Array.update (((fun r -> r.clabels) tableau), new_, l);
         (n, (Col new_)) end) end in
(m, (List.map monToWPos monL))
let rec insertDecomp (((d, wposL) as decomp), owner) =
  let new_ = incrNRows () in
  let rec insertWPos (d, pos) =
    begin match pos with
    | Row row ->
        (begin incrArray2Row
                 (((fun r -> r.coeffs) tableau), new_, (0, (nCols ())),
                   (begin function | j -> ( * ) d coeff (row, j) end));
        incrArray (((fun r -> r.consts) tableau), new_, (( * ) d const row)) end)
    | Col col -> incrArray2 (((fun r -> r.coeffs) tableau), new_, col, d) end in
((begin List.app insertWPos wposL;
  incrArray (((fun r -> r.consts) tableau), new_, d);
  (begin match isSubsumed new_ with
   | Some pos ->
       (begin clearArray2Row
                (((fun r -> r.coeffs) tableau), new_, (0, (nCols ())));
        Array.update (((fun r -> r.consts) tableau), new_, zero);
        decrNRows ();
        pos end)
  | None ->
      (((begin setOwnership ((Row new_), owner, (ref 0));
         (:=) (((fun r -> r.dead)) (label (Row new_))) isConstant new_;
         Trail.log (((fun r -> r.trail) tableau), (Insert (Row new_)));
         Row new_ end))
  (* log the creation of this row *)(* return its position *)) end) end)
(* add the decomposition to the newly created row *)
(* is this row trivial? *))
let rec insert (g_, us_) =
  let sum = fromExp us_ in
  insertDecomp ((decomposeSum (g_, sum)), (Exp (g_, sum)))
let rec minimize row =
  let rec killColumn (j, (l : label)) =
    if (not (dead l)) && ((coeff (row, j)) <> zero)
    then
      begin (((begin Trail.log (((fun r -> r.trail) tableau), (Kill (Col j)));
               ((fun r -> r.dead)
                  (Array.sub (((fun r -> r.clabels) tableau), j)))
                 := true;
               (begin match restriction l with
                | Some restr -> unifyRestr (restr, (geq00 ()))
                | None -> () end);
      (begin match (fun r -> r.owner) l with
       | Var _ as owner ->
           unifySum ((ownerContext owner), (ownerSum owner), zero)
       | _ -> () end) end))
    (* mark the column dead *)(* if restricted, instantiate the proof object to 0>=0 *)
    (* if owned by a monomial, unify it with zero *)) end
  else begin () end in
let rec killRow (i, (l : label)) =
if not (dead l)
then
  begin (((if isConstant i
           then
             begin (((begin Trail.log
                              (((fun r -> r.trail) tableau), (Kill (Row i)));
                      ((fun r -> r.dead)
                         (Array.sub (((fun r -> r.rlabels) tableau), i)))
                        := true;
                      (begin match restriction l with
                       | Some restr -> unifyRestr (restr, (geqN0 (const i)))
                       | None -> () end);
             (begin match (fun r -> r.owner) l with
              | Var _ as owner ->
                  unifySum
                    ((ownerContext owner), (ownerSum owner), (const i))
              | _ -> () end) end))
(* mark the row dead *)(* if restricted, instantiate the proof object to n>=0 *)
(* if owned by a monomial, unify it with n *)) end
else begin
  (begin match isSubsumed i with
   | Some pos' ->
       let l' = label pos' in
       (begin Trail.log (((fun r -> r.trail) tableau), (Kill (Row i)));
        ((fun r -> r.dead) (Array.sub (((fun r -> r.rlabels) tableau), i)))
          := true;
        (begin match ((restriction l), (restriction l')) with
         | (Some restr, Some (Restr (_, proof', _))) ->
             unifyRestr (restr, proof')
         | (Some _, None) ->
             (((begin Trail.log
                        (((fun r -> r.trail) tableau), (Restrict pos'));
                (:=) (((fun r -> r.restr)) l') restriction l end))
         (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *))
        | (None, _) -> () end) end) | None -> () end) end))
(* row is now constant and equal to n = const(i) *)) end
else begin () end in
((begin Array.app killColumn (((fun r -> r.clabels) tableau), 0, (nCols ()));
Array.app killRow (((fun r -> r.rlabels) tableau), 0, (nRows ())) end)
(* equate the given column to zero if coeff(row, j) <> zero *)(* find out if the given row has been made trivial by killing some
               columns
            *))
let rec restrict =
  begin function
  | ((Col col as pos), restr) ->
      let l = label pos in
      if dead l then begin unifyRestr (restr, (geq00 ())) end
        else begin
          (begin match restriction l with
           | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
           | None ->
               let nonNull =
                 Array.foldl
                   (begin function
                    | (i, (l : label), rest) ->
                        if not (dead l)
                        then
                          begin let value = coeff (i, col) in
                                (if value <> zero then begin i :: rest end
                                  else begin rest end) end
                   else begin rest end end)
          [] (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
    (((begin match nonNull with
       | row::_ ->
           (((begin Trail.log
                      (((fun r -> r.trail) tableau), (Pivot (row, col)));
              pivot (row, col);
              restrict ((Row row), restr) end))
       (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *))
      | [] ->
          (((begin Trail.log
                     (((fun r -> r.trail) tableau), (Restrict (Col col)));
             (:=) (((fun r -> r.restr)) (label (Col col))) Some restr end))
      (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)) end))
  (* compute the list of non-null row entries *)) end) end
| ((Row row as pos), restr) ->
    let l = label pos in
    if dead l then begin unifyRestr (restr, (geqN0 (const row))) end
      else begin
        (begin match restriction l with
         | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
         | None ->
             (begin match maximizeRow row with
              | Unbounded col ->
                  (begin Trail.log
                           (((fun r -> r.trail) tableau),
                             (Restrict (Row row)));
                   (:=) (((fun r -> r.restr))
                           (Array.sub (((fun r -> r.rlabels) tableau), row)))
                     Some restr;
                   if (const row) < zero
                   then
                     begin (begin Trail.log
                                    (((fun r -> r.trail) tableau),
                                      (Pivot (row, col)));
                            pivot (row, col) end) end
                  else begin () end end)
      | Positive ->
          (((begin Trail.log
                     (((fun r -> r.trail) tableau), (Restrict (Row row)));
             (:=) (((fun r -> r.restr))
                     (Array.sub (((fun r -> r.rlabels) tableau), row)))
               Some restr end))
      (* the tableau is satisfiable and minimal *))
    | Maximized value ->
        if value = zero
        then
          begin (((begin Trail.log
                           (((fun r -> r.trail) tableau),
                             (Restrict (Row row)));
                   (:=) (((fun r -> r.restr))
                           (Array.sub (((fun r -> r.rlabels) tableau), row)))
                     Some restr;
                   minimize row end))
        (* the tableau is satisfiable but not minimal*)) end
    else begin raise Error end end) end) end end
let rec insertEqual (g_, pos, sum) =
  let (m, wposL) = decomposeSum (g_, sum) in
  let decomp' = (m, (((- one), pos) :: wposL)) in
  let pos' = insertDecomp (decomp', (Exp (g_, (Sum (zero, []))))) in
  let decomp'' = unaryMinusDecomp decomp' in
  let tag'' =
    (fun r -> r.tag)
      (label (insertDecomp (decomp'', (Exp (g_, (Sum (zero, []))))))) in
  ((begin restrict (pos', (Restr (g_, (geq00 ()), false)));
    (begin match findTag tag'' with
     | Some pos'' -> restrict (pos'', (Restr (g_, (geq00 ()), false))) end) end)
    (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *))
let rec update (g_, pos, sum) =
  let l = label pos in
  ((begin Trail.log
            (((fun r -> r.trail) tableau),
              (UpdateOwner
                 (pos, ((fun r -> r.owner) l), ((fun r -> r.tag) l))));
    setOwnership (pos, (Exp (g_, sum)), (ref 0));
    if dead l
    then
      begin (((begin match pos with
               | Row row ->
                   ((if isConstant row
                     then begin unifySum (g_, sum, (const row)) end
                   else begin
                     (begin match isSubsumed row with
                      | Some pos' -> update (g_, pos', sum) end) end)
    (* row is dead because constant and equal to n *)
    (* row is dead because is subsumed by another *))
    | Col col -> unifySum (g_, sum, zero) end))
  (* find out why it died *)(* column is dead because = 0 *)) end
else begin
  (let rec isVar =
     begin function
     | Sum (m, (Mon (n, _) as mon)::[]) ->
         if (m = zero) && (n = one) then begin Some mon end
         else begin None end
     | sum -> None end in
((begin match isVar sum with
| Some mon ->
    (begin match findMon mon with
     | Some _ -> insertEqual (g_, pos, sum)
     | None ->
         let tag = ref 0 in
         (((begin Trail.log
                    (((fun r -> r.trail) tableau),
                      (UpdateOwner
                         (pos, ((fun r -> r.owner) l), ((fun r -> r.tag) l))));
            setOwnership (pos, (Var (g_, mon)), tag);
            delayMon (mon, (ref (makeCnstr tag))) end))
         (* recycle the current label *)) end)
| None -> insertEqual (g_, pos, sum) end)
(* the nf is another variable *))) end end)
(* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
(* analyze the given position to see exactly how to represent this
                 equality *))
let rec restrictions pos =
  let rec member (x, l) = List.exists (begin function | y -> x = y end) l in
let rec test l = (restricted l) && (not (dead l)) in
let rec reachable =
  begin function
  | ((Row row as pos)::candidates, tried, closure) ->
      if member (pos, tried)
      then begin reachable (candidates, tried, closure) end
      else begin
        (let new_candidates =
           Array.foldl
             (begin function
              | (col, _, candidates) ->
                  if (coeff (row, col)) <> zero
                  then begin (Col col) :: candidates end
                  else begin candidates end end)
        [] (((fun r -> r.clabels) tableau), 0, (nCols ())) in
let closure' = if test (label pos) then begin pos :: closure end
  else begin closure end in
reachable ((new_candidates @ candidates), (pos :: tried), closure')) end
| ((Col col as pos)::candidates, tried, closure) ->
    if member (pos, tried)
    then begin reachable (candidates, tried, closure) end
    else begin
      (let candidates' =
         Array.foldl
           (begin function
            | (row, _, candidates) ->
                if (coeff (row, col)) <> zero
                then begin (Row row) :: candidates end
                else begin candidates end end)
      [] (((fun r -> r.rlabels) tableau), 0, (nRows ())) in
let closure' = if test (label pos) then begin pos :: closure end
else begin closure end in
reachable ((candidates' @ candidates), (pos :: tried), closure')) end
| ([], _, closure) -> closure end in
let rec restrExp pos =
let l = label pos in
let owner = (fun r -> r.owner) l in
let g_ = ownerContext owner in
let u_ = toExp (ownerSum owner) in
begin match restriction (label pos) with
| Some (Restr (_, _, true)) -> (g_, (gt0 u_))
| _ -> (g_, (geq0 u_)) end in
List.map restrExp (reachable ([pos], [], []))
let rec makeCnstr tag = FgnCnstr (!myID, (MyFgnCnstrRep tag))
let rec toInternal tag () =
  begin match findTag tag with | None -> [] | Some pos -> restrictions pos end
let rec awake tag () =
  begin try
          begin match findTag tag with
          | Some pos ->
              let owner = (fun r -> r.owner) (label pos) in
              let g_ = ownerContext owner in
              let sum = normalize (ownerSum owner) in
              (begin update (g_, pos, sum); true end)
          | None -> true end
  with | Error -> false end
let rec simplify tag () =
  begin match toInternal tag () with | [] -> true | _::_ -> false end
let rec undo =
  begin function
  | Insert (Row row) ->
      (begin ((fun r -> r.dead)
                (Array.sub (((fun r -> r.rlabels) tableau), row)))
               := true;
       clearArray2Row (((fun r -> r.coeffs) tableau), row, (0, (nCols ())));
       Array.update (((fun r -> r.consts) tableau), row, zero);
       decrNRows () end)
  | Insert (Col col) ->
      (begin ((fun r -> r.dead)
                (Array.sub (((fun r -> r.clabels) tableau), col)))
               := true;
       clearArray2Col (((fun r -> r.coeffs) tableau), col, (0, (nRows ())));
       decrNCols () end)
  | Pivot (row, col) -> pivot (row, col)
  | Kill pos -> ((fun r -> r.dead) (label pos)) := false
  | Restrict pos -> ((fun r -> r.restr) (label pos)) := None
  | UpdateOwner (pos, owner, tag) -> setOwnership (pos, owner, tag) end
let rec reset () =
  let l =
    {
      owner = (Exp (Null, (Sum (zero, []))));
      tag = (ref 0);
      restr = (ref None);
      dead = (ref true)
    } in
  begin Array.modify (begin function | _ -> l end)
  (((fun r -> r.rlabels) tableau), 0, (nRows ()));
    Array.modify (begin function | _ -> l end)
    (((fun r -> r.clabels) tableau), 0, (nCols ()));
  Array.modify (begin function | _ -> zero end)
  (((fun r -> r.consts) tableau), 0, (nRows ()));
  Array2.modify Array2.RowMajor (begin function | _ -> zero end)
  {
    base = ((fun r -> r.coeffs) tableau);
    row = 0;
    col = 0;
    nrows = (nRows ());
    ncols = (nCols ())
  }; ((fun r -> r.nrows) tableau) := 0; ((fun r -> r.ncols) tableau) := 0;
Trail.reset ((fun r -> r.trail) tableau) end
let rec mark () = Trail.mark ((fun r -> r.trail) tableau)
let rec unwind () = Trail.unwind (((fun r -> r.trail) tableau), undo)
let rec fst =
  begin function
  | (App (u1_, _), s) -> (u1_, s)
  | (SClo (s_, s'), s) -> fst (s_, (comp (s', s))) end
let rec snd =
  begin function
  | (App (u1_, s_), s) -> fst (s_, s)
  | (SClo (s_, s'), s) -> snd (s_, (comp (s', s))) end
let rec isConstantExp (u_) =
  begin match fromExp (u_, id) with | Sum (m, []) -> Some m | _ -> None end
let rec isZeroExp (u_) =
  begin match isConstantExp u_ with | Some d -> d = zero | None -> false end
let rec solveGt =
  begin function
  | (g_, s_, 0) ->
      let rec solveGt0 (w_) =
        begin match isConstantExp w_ with
        | Some d -> if d > zero then begin gtNExp d end
            else begin raise Error end
        | None ->
            let proof = newEVar (g_, (gt0 w_)) in
            let _ =
              restrict
                ((insert (g_, (w_, id))),
                  (Restr (g_, (gtGeq (w_, (constant zero), proof)), true))) in
            proof end in
let u1_ = EClo (fst (s_, id)) in
let u2_ = EClo (snd (s_, id)) in
(begin try
         if isZeroExp u2_ then begin Some (solveGt0 u1_) end
         else begin
           (let w_ = minus (u1_, u2_) in
            let proof = solveGt0 w_ in
            Some (gtAdd (w_, (constant zero), u2_, proof))) end
  with | Error -> None end)
| (g_, s_, n) -> None end
let rec solveGeq =
  begin function
  | (g_, s_, 0) ->
      let rec solveGeq0 (w_) =
        begin match isConstantExp w_ with
        | Some d -> if d >= zero then begin geqN0 d end
            else begin raise Error end
        | None ->
            let proof = newEVar (g_, (geq0 w_)) in
            let _ =
              restrict ((insert (g_, (w_, id))), (Restr (g_, proof, false))) in
            proof end in
let u1_ = EClo (fst (s_, id)) in
let u2_ = EClo (snd (s_, id)) in
(begin try
         if isZeroExp u2_ then begin Some (solveGeq0 u1_) end
         else begin
           (let w_ = minus (u1_, u2_) in
            let proof = solveGeq0 w_ in
            Some (geqAdd (w_, (constant zero), u2_, proof))) end
  with | Error -> None end)
| (g_, s_, n) -> None end
let rec pi (name, u_, v_) = Pi (((Dec ((Some name), u_)), Maybe), v_)
let rec arrow (u_, v_) = Pi (((Dec (None, u_)), No), v_)
let rec installFgnCnstrOps () =
  let csid = !myID in
  let _ =
    FgnCnstrStd.ToInternal.install
      (csid,
        (begin function
         | MyFgnCnstrRep tag -> toInternal tag
         | fc -> raise (UnexpectedFgnCnstr fc) end)) in
  let _ =
    FgnCnstrStd.Awake.install
      (csid,
        (begin function
         | MyFgnCnstrRep tag -> awake tag
         | fc -> raise (UnexpectedFgnCnstr fc) end)) in
  let _ =
    FgnCnstrStd.Simplify.install
      (csid,
        (begin function
         | MyFgnCnstrRep tag -> simplify tag
         | fc -> raise (UnexpectedFgnCnstr fc) end)) in
  ()
let rec init (cs, installF) =
  begin myID := cs;
  (:=) gtID installF
    ((ConDec
        (">", None, 0, (Constraint (!myID, solveGt)),
          (arrow ((number ()), (arrow ((number ()), (Uni Type))))), Kind)),
      (Some (FX.Infix (FX.minPrec, FX.None))),
      [MS.Mapp
         ((MS.Marg (MS.Star, None)),
           (MS.Mapp ((MS.Marg (MS.Star, None)), MS.Mnil)))]);
  (:=) geqID installF
    ((ConDec
        (">=", None, 0, (Constraint (!myID, solveGeq)),
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
          Type)), None, []);
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
          Type)), None, []);
  (:=) gtGeqID installF
    ((ConDec
        (">>=", None, 2, Normal,
          (pi
             ("X", (number ()),
               (pi
                  ("Y", (number ()),
                    (arrow
                       ((gt ((Root ((BVar 2), Nil)), (Root ((BVar 1), Nil)))),
                         (geq
                            ((Root ((BVar 3), Nil)), (Root ((BVar 2), Nil)))))))))),
          Type)), None, []);
  (:=) geq00ID installF
    ((ConDec ("0>=0", None, 0, Normal, (geq0 (constant zero)), Type)), None,
      []);
  installFgnCnstrOps ();
  () end
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
   } : CSManager.solver) end
