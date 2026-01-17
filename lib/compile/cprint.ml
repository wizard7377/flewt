
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
         (*! structure CompSyn = CompSyn' !*)), G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose (G, G')), D)
    let rec goalToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* goalToString (G, g) where G |- g  goal *)),
         (G, Atom p)) ->
          ((^) (t ^ "SOLVE   ") Print.expToString (G, p)) ^ "\n"
      | (t, (G, Impl (p, A, _, g))) ->
          ((^) ((((^) (t ^ "ASSUME  ") Print.expToString (G, A)) ^ "\n") ^
                  (clauseToString (t ^ "\t") (G, p)))
             goalToString t ((IntSyn.Decl (G, (IntSyn.Dec (NONE, A)))), g))
            ^ "\n"
      | (t, (G, All (D, g))) ->
          let D' = Names.decLUName (G, D) in
          ((^) (((^) (t ^ "ALL     ") Formatter.makestring_fmt
                   (Print.formatDec (G, D')))
                  ^ "\n")
             goalToString t ((IntSyn.Decl (G, D')), g))
            ^ "\n"
    let rec auxToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* auxToString (G, r) where G |- r auxgoal *)),
         (G, Trivial)) -> ""
      | (t, (G, UnifyEq (G', p1, N, ga))) ->
          (^) (((^) (((^) (t ^ "UNIFYEqn  ") Print.expToString
                        ((compose (G', G)), p1))
                       ^ " = ")
                  Print.expToString ((compose (G', G)), N))
                 ^ "\n")
            auxToString t (G, ga)
    let rec clauseToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((t)(* clauseToString (G, r) where G |- r  resgoal *)),
         (G, Eq p)) -> ((^) (t ^ "UNIFY   ") Print.expToString (G, p)) ^ "\n"
      | (t, (G, Assign (p, ga))) ->
          (((t ^ "ASSIGN  ") ^
              (try Print.expToString (G, p) with | _ -> "<exc>"))
             ^ "\n")
            ^ (auxToString t (G, ga))
      | (t, (G, And (r, A, g))) ->
          (^) (clauseToString t
                 ((IntSyn.Decl (G, (IntSyn.Dec (NONE, A)))), r))
            goalToString t (G, g)
      | (t, (G, In (r, A, g))) ->
          let D = Names.decEName (G, (IntSyn.Dec (NONE, A))) in
          (^) (((^) (((clauseToString t ((IntSyn.Decl (G, D)), r)) ^ t) ^
                       "META    ")
                  Print.decToString (G, D))
                 ^ "\n")
            goalToString t (G, g)
      | (t, (G, Exists (D, r))) ->
          let D' = Names.decEName (G, D) in
          (^) (((t ^ "EXISTS  ") ^
                  (try Print.decToString (G, D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (G, D')), r)
      | (t, (G, Axists ((ADec (SOME n, d) as D), r))) ->
          let D' = Names.decEName (G, D) in
          (^) (((t ^ "EXISTS'  ") ^
                  (try Print.decToString (G, D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (G, D')), r)
    let rec subgoalsToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (G, True)) -> t ^ "True "
      | (t, (G, Conjunct (Goal, A, Sg))) ->
          (^) (((^) t goalToString t
                  ((IntSyn.Decl (G, (IntSyn.Dec (NONE, A)))), Goal))
                 ^ " and ")
            subgoalsToString t (G, Sg)
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
          (((IntSyn.Null)(* dProgToString (G, dProg) = printed representation of dynamic program *)),
           IntSyn.Null)
          -> ""
      | DProg (Decl (G, Dec (SOME x, _)), Decl (dPool, Dec (r, _, _))) ->
          (^) ((((dProgToString (DProg (G, dPool))) ^ "\nClause    ") ^ x) ^
                 ":\n")
            clauseToString "\t" (G, r)
      | DProg (Decl (G, Dec (SOME x, A)), Decl (dPool, CompSyn.Parameter)) ->
          (^) ((((dProgToString (DProg (G, dPool))) ^ "\nParameter ") ^ x) ^
                 ":\t")
            Print.expToString (G, A)
  end ;;
