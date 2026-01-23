module type CPRINT  =
  sig
    val goalToString : string -> (IntSyn.dctx * CompSyn.goal_) -> string
    val clauseToString : string -> (IntSyn.dctx * CompSyn.resGoal_) -> string
    val sProgToString : unit -> string
    val dProgToString : CompSyn.dProg_ -> string
    val subgoalsToString :
      string -> (IntSyn.dctx * CompSyn.conjunction_) -> string
  end


module CPrint(CPrint:sig
                       module Print : PRINT
                       module Formatter : FORMATTER
                       module Names : NAMES
                     end) : CPRINT =
  struct
    open CompSyn
    let rec compose =
      begin function
      | (IntSyn.Null, g_) -> g_
      | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose (g_, g'_)), d_) end
    let rec goalToString arg__0 arg__1 =
      begin match (arg__0, arg__1) with
      | (t, (g_, Atom p)) ->
          ((^) (t ^ "SOLVE   ") Print.expToString (g_, p)) ^ "\n"
      | (t, (g_, Impl (p, a_, _, g))) ->
          ((^) ((((^) (t ^ "ASSUME  ") Print.expToString (g_, a_)) ^ "\n") ^
                  (clauseToString (t ^ "\t") (g_, p)))
             goalToString t ((IntSyn.Decl (g_, (IntSyn.Dec (None, a_)))), g))
            ^ "\n"
      | (t, (g_, All (d_, g))) ->
          let d'_ = Names.decLUName (g_, d_) in
          ((^) (((^) (t ^ "ALL     ") Formatter.makestring_fmt
                   (Print.formatDec (g_, d'_)))
                  ^ "\n")
             goalToString t ((IntSyn.Decl (g_, d'_)), g))
            ^ "\n" end
  let rec auxToString arg__2 arg__3 =
    begin match (arg__2, arg__3) with
    | (t, (g_, Trivial)) -> ""
    | (t, (g_, UnifyEq (g'_, p1, n_, ga))) ->
        (^) (((^) (((^) (t ^ "UNIFYEqn  ") Print.expToString
                      ((compose (g'_, g_)), p1))
                     ^ " = ")
                Print.expToString ((compose (g'_, g_)), n_))
               ^ "\n")
          auxToString t (g_, ga) end
let rec clauseToString arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (t, (g_, Eq p)) ->
      ((^) (t ^ "UNIFY   ") Print.expToString (g_, p)) ^ "\n"
  | (t, (g_, Assign (p, ga))) ->
      (((t ^ "ASSIGN  ") ^
          (begin try Print.expToString (g_, p) with | _ -> "<exc>" end))
        ^ "\n")
      ^ (auxToString t (g_, ga))
  | (t, (g_, And (r, a_, g))) ->
      (^) (clauseToString t ((IntSyn.Decl (g_, (IntSyn.Dec (None, a_)))), r))
        goalToString t (g_, g)
  | (t, (g_, In (r, a_, g))) ->
      let d_ = Names.decEName (g_, (IntSyn.Dec (None, a_))) in
      (^) (((^) (((clauseToString t ((IntSyn.Decl (g_, d_)), r)) ^ t) ^
                   "META    ")
              Print.decToString (g_, d_))
             ^ "\n")
        goalToString t (g_, g)
  | (t, (g_, Exists (d_, r))) ->
      let d'_ = Names.decEName (g_, d_) in
      (^) (((t ^ "EXISTS  ") ^
              (begin try Print.decToString (g_, d'_) with | _ -> "<exc>" end))
        ^ "\n") clauseToString t ((IntSyn.Decl (g_, d'_)), r)
  | (t, (g_, Axists ((ADec (Some n, d) as d_), r))) ->
      let d'_ = Names.decEName (g_, d_) in
      (^) (((t ^ "EXISTS'  ") ^
              (begin try Print.decToString (g_, d'_) with | _ -> "<exc>" end))
        ^ "\n") clauseToString t ((IntSyn.Decl (g_, d'_)), r) end
let rec subgoalsToString arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (t, (g_, True)) -> t ^ "True "
  | (t, (g_, Conjunct (Goal, a_, Sg))) ->
      (^) (((^) t goalToString t
              ((IntSyn.Decl (g_, (IntSyn.Dec (None, a_)))), Goal))
             ^ " and ")
        subgoalsToString t (g_, Sg) end
let rec conDecToString =
  begin function
  | (c, SClause r) ->
      let _ = Names.varReset IntSyn.Null in
      let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
      let l = String.size name in
      (name ^ (if l > 6 then begin ":\n" end else begin ":" end)) ^
        ((clauseToString "\t" (IntSyn.Null, r)) ^ "\n")
  | (c, Void) -> (Print.conDecToString (IntSyn.sgnLookup c)) ^ "\n\n" end
let rec sProgToString () =
  let (size, _) = IntSyn.sgnSize () in
  let rec ts cid =
    if cid < size
    then
      begin (^) (conDecToString (cid, (CompSyn.sProgLookup cid))) ts
              (cid + 1) end
    else begin "" end in
ts 0
let rec dProgToString =
  begin function
  | DProg (IntSyn.Null, IntSyn.Null) -> ""
  | DProg (Decl (g_, Dec (Some x, _)), Decl (dPool, Dec (r, _, _))) ->
      (^) ((((dProgToString (DProg (g_, dPool))) ^ "\nClause    ") ^ x) ^
             ":\n")
        clauseToString "\t" (g_, r)
  | DProg (Decl (g_, Dec (Some x, a_)), Decl (dPool, CompSyn.Parameter)) ->
      (^) ((((dProgToString (DProg (g_, dPool))) ^ "\nParameter ") ^ x) ^
             ":\t")
        Print.expToString (g_, a_) end end
