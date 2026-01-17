
module type FILLING  =
  sig
    module MetaSyn :
    ((METASYN)(* Filling *)(* Author: Carsten Schuermann *))
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : MetaSyn.__State -> (operator list * operator)
    val apply :
      operator ->
        ((MetaSyn.__State)(*
    gets a list of operators, which fill in several non index variables
    on one level simultaneously
  *))
          list
    val menu :
      operator ->
        ((string)(*
    in the case of an induction hypothesis, an operator can transform a
    state into several states. In the case of just filling in the existential
    parameters, there will by only one resulting state (we only need ONE
    witness instantiation of the variables 
  *))
  end;;




module Filling(Filling:sig
                         module MetaSyn' : METASYN
                         module MetaAbstract : METAABSTRACT
                         module Search : OLDSEARCH
                         module Whnf : WHNF
                         module Print :
                         ((PRINT)(* Filling *)(* Author: Carsten Schuermann *)
                         (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*))
                       end) : FILLING =
  struct
    module MetaSyn =
      ((MetaSyn')(*! sharing Print.IntSyn = MetaSyn'.IntSyn !*))
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
    let rec operators (g, GE, Vs, abstractAll, abstractEx, makeAddress) =
      operatorsW
        (g, GE, (Whnf.whnf Vs), abstractAll, abstractEx, makeAddress)
    let rec operatorsW =
      function
      | (g, GE, ((Root (C, S), _) as Vs), abstractAll, abstractEx,
         makeAddress) ->
          (nil,
            ((makeAddress 0),
              (delay
                 ((function
                   | Params ->
                       (try Search.searchEx Params with | Success (S) -> [S])),
                   (g, GE, Vs, abstractEx)))))
      | (g, GE, (Pi (((Dec (_, V1) as D), P), V2), s), abstractAll,
         abstractEx, makeAddress) ->
          let (GO', O) =
            operators
              ((I.Decl (g, (I.decSub (D, s)))), GE, (V2, (I.dot1 s)),
                abstractAll, abstractEx, (makeAddressCont makeAddress)) in
          ((((makeAddress 0),
              (delay (Search.searchAll, (g, GE, (V1, s), abstractAll)))) ::
              GO'), O)
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | Prefix (Decl (g, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (g', M', B'), s', GE') =
            createEVars (M.Prefix (g, M, B)) in
          ((M.Prefix
              ((I.Decl (g', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'), GE')
      | Prefix (Decl (g, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (g', M', B'), s', GE') =
            createEVars (M.Prefix (g, M, B)) in
          let X = I.newEVar (g', (I.EClo (V, s'))) in
          let X' = Whnf.lowerEVar X in
          ((M.Prefix (g', M', B')), (I.Dot ((I.Exp X), s')), (X' :: GE'))
    let rec expand (State (name, Prefix (g, M, B), V) as S) =
      let (Prefix (g', M', B'), s', GE') = createEVars (M.Prefix (g, M, B)) in
      let abstractAll acc =
        try
          (MetaAbstract.abstract
             (M.State (name, (M.Prefix (g', M', B')), (I.EClo (V, s')))))
            :: acc
        with | Error s -> acc in
      let abstractEx () =
        try
          raise
            (Success
               (MetaAbstract.abstract
                  (M.State (name, (M.Prefix (g', M', B')), (I.EClo (V, s'))))))
        with | Error s -> () in
      operators
        (g', GE', (V, s'), abstractAll, abstractEx, (makeAddressInit S))
    let rec apply (_, f) = f ()
    let rec menu ((State (name, Prefix (g, M, B), V), k), Sl) =
      let toString =
        function
        | (g, Pi ((Dec (_, V), _), _), 0) -> Print.expToString (g, V)
        | (g, (Root _ as V), 0) -> Print.expToString (g, V)
        | (g, Pi ((D, _), V), k) -> toString ((I.Decl (g, D)), V, (k - 1)) in
      (^) "Filling   : " toString (g, V, k)
    let ((expand)(* operators (g, GE, (V, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   g |- s : G1   G1 |- V : type
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
      (* createEVars (g, M) = ((g', M'), s', GE')

       Invariant:
       If   |- g ctx
       and  g |- M mtx
       then |- g' ctx
       and  g' |- M' mtx
       and  g' |- s' : g
       and  GE a list of EVars

    *)
      (* expand' ((g, M), V) = (OE', OL')

       Invariant:
       If   |- g ctx
       and  g |- M mtx
       and  g |- V type
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
              toSTring (g, I.Root _, k) for k <> 0
            *))
      = expand
    let apply = apply
    let menu = menu
  end ;;
