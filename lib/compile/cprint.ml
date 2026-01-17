
module type CPRINT  =
  sig
    val goalToString :
      string ->
        (IntSyn.dctx * CompSyn.__Goal) ->
          ((string)(*! structure CompSyn : COMPSYN !*)
          (*! structure IntSyn : INTSYN !*)(* Author: Iliano Cervesato *)
          (* Printer for Compiled Syntax *))
    val clauseToString :
      string -> (IntSyn.dctx * CompSyn.__ResGoal) -> string
    val sProgToString : unit -> string
    val dProgToString : CompSyn.__DProg -> string
    val subgoalsToString :
      string -> (IntSyn.dctx * CompSyn.__Conjunction) -> string
  end;;




module CPrint(CPrint:sig
                       module Print : PRINT
                       module Formatter : FORMATTER
                       module Names :
                       ((NAMES)(* Printer for Compiled Syntax *)
                       (* Author: Iliano Cervesato *)
                       (*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       (*! sharing Print.IntSyn = IntSyn' !*))
                     end) : CPRINT =
  struct
    open CompSyn
    let rec compose =
      function
      | (((IntSyn.Null)(*! sharing Names.IntSyn = IntSyn' !*)(*! structure IntSyn = IntSyn' !*)
         (*! structure CompSyn = CompSyn' !*)), g) -> g
      | (Decl (g, D), g') -> IntSyn.Decl ((compose (g, g')), D)
    let rec goalToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* goalToString (g, g) where g |- g  goal *)),
         (g, Atom p)) ->
          ((^) (t ^ "SOLVE   ") Print.expToString (g, p)) ^ "\n"
      | (t, (g, Impl (p, A, _, g))) ->
          ((^) ((((^) (t ^ "ASSUME  ") Print.expToString (g, A)) ^ "\n") ^
                  (clauseToString (t ^ "\t") (g, p)))
             goalToString t ((IntSyn.Decl (g, (IntSyn.Dec (NONE, A)))), g))
            ^ "\n"
      | (t, (g, All (D, g))) ->
          let D' = Names.decLUName (g, D) in
          ((^) (((^) (t ^ "ALL     ") Formatter.makestring_fmt
                   (Print.formatDec (g, D')))
                  ^ "\n")
             goalToString t ((IntSyn.Decl (g, D')), g))
            ^ "\n"
    let rec auxToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* auxToString (g, r) where g |- r auxgoal *)),
         (g, Trivial)) -> ""
      | (t, (g, UnifyEq (g', p1, N, ga))) ->
          (^) (((^) (((^) (t ^ "UNIFYEqn  ") Print.expToString
                        ((compose (g', g)), p1))
                       ^ " = ")
                  Print.expToString ((compose (g', g)), N))
                 ^ "\n")
            auxToString t (g, ga)
    let rec clauseToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* clauseToString (g, r) where g |- r  resgoal *)),
         (g, Eq p)) -> ((^) (t ^ "UNIFY   ") Print.expToString (g, p)) ^ "\n"
      | (t, (g, Assign (p, ga))) ->
          (((t ^ "ASSIGN  ") ^
              (try Print.expToString (g, p) with | _ -> "<exc>"))
             ^ "\n")
            ^ (auxToString t (g, ga))
      | (t, (g, And (r, A, g))) ->
          (^) (clauseToString t
                 ((IntSyn.Decl (g, (IntSyn.Dec (NONE, A)))), r))
            goalToString t (g, g)
      | (t, (g, In (r, A, g))) ->
          let D = Names.decEName (g, (IntSyn.Dec (NONE, A))) in
          (^) (((^) (((clauseToString t ((IntSyn.Decl (g, D)), r)) ^ t) ^
                       "META    ")
                  Print.decToString (g, D))
                 ^ "\n")
            goalToString t (g, g)
      | (t, (g, Exists (D, r))) ->
          let D' = Names.decEName (g, D) in
          (^) (((t ^ "EXISTS  ") ^
                  (try Print.decToString (g, D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (g, D')), r)
      | (t, (g, Axists ((ADec (SOME n, d) as D), r))) ->
          let D' = Names.decEName (g, D) in
          (^) (((t ^ "EXISTS'  ") ^
                  (try Print.decToString (g, D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (g, D')), r)
    let rec subgoalsToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (g, True)) -> t ^ "True "
      | (t, (g, Conjunct (Goal, A, Sg))) ->
          (^) (((^) t goalToString t
                  ((IntSyn.Decl (g, (IntSyn.Dec (NONE, A)))), Goal))
                 ^ " and ")
            subgoalsToString t (g, Sg)
    let rec conDecToString =
      function
      | (((c)(* conDecToString (c, clause) printed representation of static clause *)),
         SClause r) ->
          let _ = Names.varReset IntSyn.Null in
          let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
          let l = String.size name in
          (name ^ (if l > 6 then ":\n" else ":")) ^
            ((clauseToString "\t" (IntSyn.Null, r)) ^ "\n")
      | (c, Void) -> (Print.conDecToString (IntSyn.sgnLookup c)) ^ "\n\n"
    let rec sProgToString
      ((())(* sProgToString () = printed representation of static program *))
      =
      let (size, _) = IntSyn.sgnSize () in
      let ts cid =
        if cid < size
        then
          (^) (conDecToString (cid, (CompSyn.sProgLookup cid))) ts (cid + 1)
        else "" in
      ts 0
    let rec dProgToString =
      function
      | DProg
          (((IntSyn.Null)(* dProgToString (g, dProg) = printed representation of dynamic program *)),
           IntSyn.Null)
          -> ""
      | DProg (Decl (g, Dec (SOME x, _)), Decl (dPool, Dec (r, _, _))) ->
          (^) ((((dProgToString (DProg (g, dPool))) ^ "\nClause    ") ^ x) ^
                 ":\n")
            clauseToString "\t" (g, r)
      | DProg (Decl (g, Dec (SOME x, A)), Decl (dPool, CompSyn.Parameter)) ->
          (^) ((((dProgToString (DProg (g, dPool))) ^ "\nParameter ") ^ x) ^
                 ":\t")
            Print.expToString (g, A)
  end ;;
