
module type CPRINT  =
  sig
    val goalToString : string -> IntSyn.dctx -> CompSyn.__Goal -> string
    val clauseToString : string -> IntSyn.dctx -> CompSyn.__ResGoal -> string
    val sProgToString : unit -> string
    val dProgToString : CompSyn.__DProg -> string
    val subgoalsToString :
      string -> IntSyn.dctx -> CompSyn.__Conjunction -> string
  end;;




module CPrint(CPrint:sig
                       module Print : PRINT
                       module Formatter : FORMATTER
                       module Names : NAMES
                     end) : CPRINT =
  struct
    open CompSyn
    let rec compose __0__ __1__ =
      match (__0__, __1__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose (__G, __G')), __D)
    let rec goalToString __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (t, __G, Atom p) ->
          ((^) (t ^ "SOLVE   ") Print.expToString (__G, p)) ^ "\n"
      | (t, __G, Impl (p, __A, _, g)) ->
          ((^) ((((^) (t ^ "ASSUME  ") Print.expToString (__G, __A)) ^ "\n")
                  ^ (clauseToString (t ^ "\t") (__G, p)))
             goalToString t
             ((IntSyn.Decl (__G, (IntSyn.Dec (NONE, __A)))), g))
            ^ "\n"
      | (t, __G, All (__D, g)) ->
          let __D' = Names.decLUName (__G, __D) in
          ((^) (((^) (t ^ "ALL     ") Formatter.makestring_fmt
                   (Print.formatDec (__G, __D')))
                  ^ "\n")
             goalToString t ((IntSyn.Decl (__G, __D')), g))
            ^ "\n"
    let rec auxToString __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (t, __G, Trivial) -> ""
      | (t, __G, UnifyEq (__G', p1, __N, ga)) ->
          (^) (((^) (((^) (t ^ "UNIFYEqn  ") Print.expToString
                        ((compose (__G', __G)), p1))
                       ^ " = ")
                  Print.expToString ((compose (__G', __G)), __N))
                 ^ "\n")
            auxToString t (__G, ga)
    let rec clauseToString __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (t, __G, Eq p) ->
          ((^) (t ^ "UNIFY   ") Print.expToString (__G, p)) ^ "\n"
      | (t, __G, Assign (p, ga)) ->
          (((t ^ "ASSIGN  ") ^
              (try Print.expToString (__G, p) with | _ -> "<exc>"))
             ^ "\n")
            ^ (auxToString t (__G, ga))
      | (t, __G, And (r, __A, g)) ->
          (^) (clauseToString t
                 ((IntSyn.Decl (__G, (IntSyn.Dec (NONE, __A)))), r))
            goalToString t (__G, g)
      | (t, __G, In (r, __A, g)) ->
          let __D = Names.decEName (__G, (IntSyn.Dec (NONE, __A))) in
          (^) (((^) (((clauseToString t ((IntSyn.Decl (__G, __D)), r)) ^ t) ^
                       "META    ")
                  Print.decToString (__G, __D))
                 ^ "\n")
            goalToString t (__G, g)
      | (t, __G, Exists (__D, r)) ->
          let __D' = Names.decEName (__G, __D) in
          (^) (((t ^ "EXISTS  ") ^
                  (try Print.decToString (__G, __D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (__G, __D')), r)
      | (t, __G, Axists ((ADec (Some n, d) as D), r)) ->
          let __D' = Names.decEName (__G, __D) in
          (^) (((t ^ "EXISTS'  ") ^
                  (try Print.decToString (__G, __D') with | _ -> "<exc>"))
                 ^ "\n")
            clauseToString t ((IntSyn.Decl (__G, __D')), r)
    let rec subgoalsToString __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (t, __G, True) -> t ^ "True "
      | (t, __G, Conjunct (Goal, __A, Sg)) ->
          (^) (((^) t goalToString t
                  ((IntSyn.Decl (__G, (IntSyn.Dec (NONE, __A)))), Goal))
                 ^ " and ")
            subgoalsToString t (__G, Sg)
    let rec conDecToString __14__ __15__ =
      match (__14__, __15__) with
      | (c, SClause r) ->
          let _ = Names.varReset IntSyn.Null in
          let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
          let l = String.size name in
          (name ^ (if l > 6 then ":\n" else ":")) ^
            ((clauseToString "\t" (IntSyn.Null, r)) ^ "\n")
      | (c, Void) -> (Print.conDecToString (IntSyn.sgnLookup c)) ^ "\n\n"
    let rec sProgToString () =
      let (size, _) = IntSyn.sgnSize () in
      let rec ts cid =
        if cid < size
        then
          (^) (conDecToString (cid, (CompSyn.sProgLookup cid))) ts (cid + 1)
        else "" in
      ts 0
    let rec dProgToString =
      function
      | DProg (IntSyn.Null, IntSyn.Null) -> ""
      | DProg (Decl (__G, Dec (Some x, _)), Decl (dPool, Dec (r, _, _))) ->
          (^) ((((dProgToString (DProg (__G, dPool))) ^ "\nClause    ") ^ x)
                 ^ ":\n")
            clauseToString "\t" (__G, r)
      | DProg
          (Decl (__G, Dec (Some x, __A)), Decl (dPool, CompSyn.Parameter)) ->
          (^) ((((dProgToString (DProg (__G, dPool))) ^ "\nParameter ") ^ x)
                 ^ ":\t")
            Print.expToString (__G, __A)
  end ;;
