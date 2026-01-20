
module type FILLING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : MetaSyn.__State -> (operator list * operator)
    val apply : operator -> MetaSyn.__State list
    val menu : operator -> string
  end;;




module Filling(Filling:sig
                         module MetaSyn' : METASYN
                         module MetaAbstract : METAABSTRACT
                         module Search : OLDSEARCH
                         module Whnf : WHNF
                         module Print : PRINT
                       end) : FILLING =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    exception TimeOut 
    type nonrec operator =
      ((MetaSyn.__State * int) * (unit -> MetaSyn.__State list))
    module M = MetaSyn
    module I = IntSyn
    exception Success of M.__State 
    let rec delay search (Params) () =
      try search Params with | Error s -> raise (Error s)
    let rec makeAddressInit (__S) k = (__S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec operators (__G) (GE) (__Vs) abstractAll abstractEx makeAddress =
      operatorsW
        (__G, GE, (Whnf.whnf __Vs), abstractAll, abstractEx, makeAddress)
    let rec operatorsW __0__ __1__ __2__ __3__ __4__ __5__ =
      match (__0__, __1__, __2__, __3__, __4__, __5__) with
      | (__G, GE, ((Root (__C, __S), _) as Vs), abstractAll, abstractEx,
         makeAddress) ->
          (nil,
            ((makeAddress 0),
              (delay
                 ((fun (Params) ->
                     try Search.searchEx Params with | Success (__S) -> [__S]),
                   (__G, GE, __Vs, abstractEx)))))
      | (__G, GE, (Pi (((Dec (_, __V1) as D), __P), __V2), s), abstractAll,
         abstractEx, makeAddress) ->
          let (GO', __O) =
            operators
              ((I.Decl (__G, (I.decSub (__D, s)))), GE, (__V2, (I.dot1 s)),
                abstractAll, abstractEx, (makeAddressCont makeAddress)) in
          ((((makeAddress 0),
              (delay (Search.searchAll, (__G, GE, (__V1, s), abstractAll))))
              :: GO'), __O)
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | Prefix (Decl (__G, __D), Decl (__M, M.Top), Decl (__B, b)) ->
          let (Prefix (__G', __M', __B'), s', GE') =
            createEVars (M.Prefix (__G, __M, __B)) in
          ((M.Prefix
              ((I.Decl (__G', (I.decSub (__D, s')))), (I.Decl (__M', M.Top)),
                (I.Decl (__B', b)))), (I.dot1 s'), GE')
      | Prefix (Decl (__G, Dec (_, __V)), Decl (__M, M.Bot), Decl (__B, _))
          ->
          let (Prefix (__G', __M', __B'), s', GE') =
            createEVars (M.Prefix (__G, __M, __B)) in
          let __X = I.newEVar (__G', (I.EClo (__V, s'))) in
          let __X' = Whnf.lowerEVar __X in
          ((M.Prefix (__G', __M', __B')), (I.Dot ((I.Exp __X), s')),
            (__X' :: GE'))
    let rec expand (State (name, Prefix (__G, __M, __B), __V) as S) =
      let (Prefix (__G', __M', __B'), s', GE') =
        createEVars (M.Prefix (__G, __M, __B)) in
      let rec abstractAll acc =
        try
          (MetaAbstract.abstract
             (M.State
                (name, (M.Prefix (__G', __M', __B')), (I.EClo (__V, s')))))
            :: acc
        with | Error s -> acc in
      let rec abstractEx () =
        try
          raise
            (Success
               (MetaAbstract.abstract
                  (M.State
                     (name, (M.Prefix (__G', __M', __B')),
                       (I.EClo (__V, s'))))))
        with | Error s -> () in
      operators
        (__G', GE', (__V, s'), abstractAll, abstractEx,
          (makeAddressInit __S))
    let rec apply _ f = f ()
    let rec menu (State (name, Prefix (__G, __M, __B), __V), k) (Sl) =
      let rec toString __6__ __7__ __8__ =
        match (__6__, __7__, __8__) with
        | (__G, Pi ((Dec (_, __V), _), _), 0) -> Print.expToString (__G, __V)
        | (__G, (Root _ as V), 0) -> Print.expToString (__G, __V)
        | (__G, Pi ((__D, _), __V), k) ->
            toString ((I.Decl (__G, __D)), __V, (k - 1)) in
      (((^) "Filling   : " toString (__G, __V, k))
        (* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *))
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
