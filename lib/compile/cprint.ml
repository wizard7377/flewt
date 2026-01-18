
(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
module type CPRINT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    val goalToString : string -> (IntSyn.dctx * CompSyn.__Goal) -> string
    val clauseToString :
      string -> (IntSyn.dctx * CompSyn.__ResGoal) -> string
    val sProgToString : unit -> string
    val dProgToString : CompSyn.__DProg -> string
    val subgoalsToString :
      string -> (IntSyn.dctx * CompSyn.__Conjunction) -> string
  end;;




(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
module CPrint(CPrint:sig
                       (*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       module Print : PRINT
                       module Formatter : FORMATTER
                       (*! sharing Print.IntSyn = IntSyn' !*)
                       module Names : NAMES
                     end) : CPRINT =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    open CompSyn
    let rec compose =
      function
      | (IntSyn.Null, __g) -> __g
      | (Decl (__g, __d), __g') -> IntSyn.Decl ((compose (__g, __g')), __d)
    (* goalToString (__g, g) where __g |- g  goal *)
    let rec goalToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (__g, Atom p)) ->
          ((^) (t ^ "SOLVE   ") Print.expToString (__g, p)) ^ "\n"
      | (t, (__g, Impl (p, A, _, g))) ->
          ((^) ((((^) (t ^ "ASSUME  ") Print.expToString (__g, A)) ^ "\n") ^
                  (clauseToString (t ^ "\t") (__g, p)))
             goalToString t ((IntSyn.Decl (__g, (IntSyn.Dec (None, A)))), g))
            ^ "\n"
      | (t, (__g, All (__d, g))) ->
          let __d' = Names.decLUName (__g, __d) in
          ((^) (((^) (t ^ "ALL     ") Formatter.makestring_fmt
                   (Print.formatDec (__g, __d')))
                  ^ "\n")
             goalToString t ((IntSyn.Decl (__g, __d')), g))
            ^ "\n"
    let rec auxToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (__g, Trivial)) -> ""
      | (t, (__g, UnifyEq (__g', p1, N, ga))) ->
          (^) (((^) (((^) (t ^ "UNIFYEqn  ") Print.expToString
                        ((compose (__g', __g)), p1))
                       ^ " = ")
                  Print.expToString ((compose (__g', __g)), N))
                 ^ "\n")
            auxToString t (__g, ga)
    let rec clauseToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (__g, Eq p)) ->
          ((^) (t ^ "UNIFY   ") Print.expToString (__g, p)) ^ "\n"
      | (t, (__g, Assign (p, ga))) ->
          (((t ^ "ASSIGN  ") ^
              (try Print.expToString (__g, p) with | _ -> "<exc>"))
             ^ "\n")
            ^ (auxToString t (__g, ga))
      | (t, (__g, And (r, A, g))) ->
          (^) (clauseToString t
                 ((IntSyn.Decl (__g, (IntSyn.Dec (None, A)))), r))
            goalToString t (__g, g)
      | (t, (__g, In (r, A, g))) ->
          let __d = Names.decEName (__g, (IntSyn.Dec (None, A))) in
          (^) (((^) (((clauseToString t ((IntSyn.Decl (__g, __d)), r)) ^ t) ^
                       "META    ")
                  Print.decToString (__g, __d))
                 ^ "\n")
            goalToString t (__g, g)
      | (t, (__g, Exists (__d, r))) ->
          let __d' = Names.decEName (__g, __d) in
          (^) (((t ^ "EXISTS  ") ^
                  (try Print.decToString (__g, __d') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (__g, __d')), r)
      | (t, (__g, Axists ((ADec (Some n, d) as __d), r))) ->
          let __d' = Names.decEName (__g, __d) in
          (^) (((t ^ "EXISTS'  ") ^
                  (try Print.decToString (__g, __d') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (__g, __d')), r)
    let rec subgoalsToString arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (t, (__g, True)) -> t ^ "True "
      | (t, (__g, Conjunct (Goal, A, Sg))) ->
          (^) (((^) t goalToString t
                  ((IntSyn.Decl (__g, (IntSyn.Dec (None, A)))), Goal))
                 ^ " and ")
            subgoalsToString t (__g, Sg)
    (* conDecToString (c, clause) printed representation of static clause *)
    let rec conDecToString =
      function
      | (c, SClause r) ->
          let _ = Names.varReset IntSyn.Null in
          let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
          let l = String.size name in
          (name ^ (if l > 6 then ":\n" else ":")) ^
            ((clauseToString "\t" (IntSyn.Null, r)) ^ "\n")
      | (c, Void) -> (Print.conDecToString (IntSyn.sgnLookup c)) ^ "\n\n"
    (* sProgToString () = printed representation of static program *)
    let rec sProgToString () =
      let (size, _) = IntSyn.sgnSize () in
      let rec ts cid =
        if cid < size
        then
          (^) (conDecToString (cid, (CompSyn.sProgLookup cid))) ts (cid + 1)
        else "" in
      ts 0
    (* dProgToString (__g, dProg) = printed representation of dynamic program *)
    let rec dProgToString =
      function
      | DProg (IntSyn.Null, IntSyn.Null) -> ""
      | DProg (Decl (__g, Dec (Some x, _)), Decl (dPool, Dec (r, _, _))) ->
          (^) ((((dProgToString (DProg (__g, dPool))) ^ "\nClause    ") ^ x) ^
                 ":\n")
            clauseToString "\t" (__g, r)
      | DProg (Decl (__g, Dec (Some x, A)), Decl (dPool, CompSyn.Parameter)) ->
          (^) ((((dProgToString (DProg (__g, dPool))) ^ "\nParameter ") ^ x) ^
                 ":\t")
            Print.expToString (__g, A)
  end ;;
