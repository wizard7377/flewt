
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
    let rec operators (__g, GE, __Vs, abstractAll, abstractEx, makeAddress) =
      operatorsW
        (__g, GE, (Whnf.whnf __Vs), abstractAll, abstractEx, makeAddress)
    let rec operatorsW =
      function
      | (__g, GE, ((Root (C, S), _) as __Vs), abstractAll, abstractEx,
         makeAddress) ->
          (nil,
            ((makeAddress 0),
              (delay
                 ((function
                   | Params ->
                       (try Search.searchEx Params with | Success (S) -> [S])),
                   (__g, GE, __Vs, abstractEx)))))
      | (__g, GE, (Pi (((Dec (_, V1) as __d), P), V2), s), abstractAll,
         abstractEx, makeAddress) ->
          let (GO', O) =
            operators
              ((I.Decl (__g, (I.decSub (__d, s)))), GE, (V2, (I.dot1 s)),
                abstractAll, abstractEx, (makeAddressCont makeAddress)) in
          ((((makeAddress 0),
              (delay (Search.searchAll, (__g, GE, (V1, s), abstractAll)))) ::
              GO'), O)
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | Prefix (Decl (__g, __d), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (__g', M', B'), s', GE') =
            createEVars (M.Prefix (__g, M, B)) in
          ((M.Prefix
              ((I.Decl (__g', (I.decSub (__d, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'), GE')
      | Prefix (Decl (__g, Dec (_, __v)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (__g', M', B'), s', GE') =
            createEVars (M.Prefix (__g, M, B)) in
          let x = I.newEVar (__g', (I.EClo (__v, s'))) in
          let x' = Whnf.lowerEVar x in
          ((M.Prefix (__g', M', B')), (I.Dot ((I.Exp x), s')), (x' :: GE'))
    let rec expand (State (name, Prefix (__g, M, B), __v) as S) =
      let (Prefix (__g', M', B'), s', GE') = createEVars (M.Prefix (__g, M, B)) in
      let rec abstractAll acc =
        try
          (MetaAbstract.abstract
             (M.State (name, (M.Prefix (__g', M', B')), (I.EClo (__v, s')))))
            :: acc
        with | Error s -> acc in
      let rec abstractEx () =
        try
          raise
            (Success
               (MetaAbstract.abstract
                  (M.State (name, (M.Prefix (__g', M', B')), (I.EClo (__v, s'))))))
        with | Error s -> () in
      operators
        (__g', GE', (__v, s'), abstractAll, abstractEx, (makeAddressInit S))
    let rec apply (_, f) = f ()
    let rec menu ((State (name, Prefix (__g, M, B), __v), k), Sl) =
      let rec toString =
        function
        | (__g, Pi ((Dec (_, __v), _), _), 0) -> Print.expToString (__g, __v)
        | (__g, (Root _ as __v), 0) -> Print.expToString (__g, __v)
        | (__g, Pi ((__d, _), __v), k) -> toString ((I.Decl (__g, __d)), __v, (k - 1)) in
      (^) "Filling   : " toString (__g, __v, k)
    (* operators (__g, GE, (__v, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   __g |- s : G1   G1 |- __v : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct
         debruijn index of the variable being filled
       and __v = {V1}...{Vn} __v'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in __v' with the smallest possible terms.
    *)
    (* createEVars (__g, M) = ((__g', M'), s', GE')

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       then |- __g' ctx
       and  __g' |- M' mtx
       and  __g' |- s' : __g
       and  GE a list of EVars

    *)
    (* expand' ((__g, M), __v) = (OE', OL')

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       and  __g |- __v type
       and  __v = {V1}...{Vn} __v'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in __v' with the smallest possible terms.
    *)
    (* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *)
    (* no cases for
              toSTring (__g, I.Root _, k) for k <> 0
            *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
