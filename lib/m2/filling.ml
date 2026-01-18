
(* Filling *)
(* Author: Carsten Schuermann *)
module type FILLING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : MetaSyn.__State -> (operator list * operator)
    (*
    gets a list of operators, which fill in several non index variables
    on one level simultaneously
  *)
    val apply : operator -> MetaSyn.__State list
    (*
    in the case of an induction hypothesis, an operator can transform a
    state into several states. In the case of just filling in the existential
    parameters, there will by only one resulting state (we only need ONE
    witness instantiation of the variables 
  *)
    val menu : operator -> string
  end;;




(* Filling *)
(* Author: Carsten Schuermann *)
module Filling(Filling:sig
                         module MetaSyn' : METASYN
                         module MetaAbstract : METAABSTRACT
                         module Search : OLDSEARCH
                         module Whnf : WHNF
                         (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                         module Print : PRINT
                       end) : FILLING =
  struct
    (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
    module MetaSyn = MetaSyn'
    exception Error of string 
    exception TimeOut 
    type nonrec operator =
      ((MetaSyn.__State * int) * (unit -> MetaSyn.__State list))
    module M = MetaSyn
    module I = IntSyn
    exception Success of M.__State 
    let rec delay (search, Params) () =
      try search Params with | Error s -> raise (Error s)
    let rec makeAddressInit (S) k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec operators (G, GE, Vs, abstractAll, abstractEx, makeAddress) =
      operatorsW
        (G, GE, (Whnf.whnf Vs), abstractAll, abstractEx, makeAddress)
    let rec operatorsW =
      function
      | (G, GE, ((Root (C, S), _) as Vs), abstractAll, abstractEx,
         makeAddress) ->
          (nil,
            ((makeAddress 0),
              (delay
                 ((function
                   | Params ->
                       (try Search.searchEx Params with | Success (S) -> [S])),
                   (G, GE, Vs, abstractEx)))))
      | (G, GE, (Pi (((Dec (_, V1) as D), P), V2), s), abstractAll,
         abstractEx, makeAddress) ->
          let (GO', O) =
            operators
              ((I.Decl (G, (I.decSub (D, s)))), GE, (V2, (I.dot1 s)),
                abstractAll, abstractEx, (makeAddressCont makeAddress)) in
          ((((makeAddress 0),
              (delay (Search.searchAll, (G, GE, (V1, s), abstractAll)))) ::
              GO'), O)
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | Prefix (Decl (G, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (G', M', B'), s', GE') =
            createEVars (M.Prefix (G, M, B)) in
          ((M.Prefix
              ((I.Decl (G', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'), GE')
      | Prefix (Decl (G, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (G', M', B'), s', GE') =
            createEVars (M.Prefix (G, M, B)) in
          let X = I.newEVar (G', (I.EClo (V, s'))) in
          let X' = Whnf.lowerEVar X in
          ((M.Prefix (G', M', B')), (I.Dot ((I.Exp X), s')), (X' :: GE'))
    let rec expand (State (name, Prefix (G, M, B), V) as S) =
      let (Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B)) in
      let rec abstractAll acc =
        try
          (MetaAbstract.abstract
             (M.State (name, (M.Prefix (G', M', B')), (I.EClo (V, s')))))
            :: acc
        with | Error s -> acc in
      let rec abstractEx () =
        try
          raise
            (Success
               (MetaAbstract.abstract
                  (M.State (name, (M.Prefix (G', M', B')), (I.EClo (V, s'))))))
        with | Error s -> () in
      operators
        (G', GE', (V, s'), abstractAll, abstractEx, (makeAddressInit S))
    let rec apply (_, f) = f ()
    let rec menu ((State (name, Prefix (G, M, B), V), k), Sl) =
      let rec toString =
        function
        | (G, Pi ((Dec (_, V), _), _), 0) -> Print.expToString (G, V)
        | (G, (Root _ as V), 0) -> Print.expToString (G, V)
        | (G, Pi ((D, _), V), k) -> toString ((I.Decl (G, D)), V, (k - 1)) in
      (^) "Filling   : " toString (G, V, k)
    (* operators (G, GE, (V, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   G |- s : G1   G1 |- V : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct
         debruijn index of the variable being filled
       and V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
    (* createEVars (G, M) = ((G', M'), s', GE')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list of EVars

    *)
    (* expand' ((G, M), V) = (OE', OL')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V type
       and  V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
    (* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *)
    (* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
