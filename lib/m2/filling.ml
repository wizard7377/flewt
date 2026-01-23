module type FILLING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    exception TimeOut 
    type nonrec operator
    val expand : MetaSyn.state_ -> (operator list * operator)
    val apply : operator -> MetaSyn.state_ list
    val menu : operator -> string
  end


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
      ((MetaSyn.state_ * int) * (unit -> MetaSyn.state_ list))
    module M = MetaSyn
    module I = IntSyn
    exception Success of M.state_ 
    let rec delay (search, Params) () =
      begin try search Params with | Error s -> raise (Error s) end
    let rec makeAddressInit (s_) k = (s_, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec operators (g_, GE, vs_, abstractAll, abstractEx, makeAddress) =
      operatorsW
        (g_, GE, (Whnf.whnf vs_), abstractAll, abstractEx, makeAddress)
    let rec operatorsW =
      begin function
      | (g_, GE, ((Root (c_, s_), _) as vs_), abstractAll, abstractEx,
         makeAddress) ->
          ([],
            ((makeAddress 0),
              (delay
                 ((begin function
                   | Params ->
                       (begin try Search.searchEx Params
                        with | Success (s_) -> [s_] end) end),
              (g_, GE, vs_, abstractEx)))))
      | (g_, GE, (Pi (((Dec (_, v1_) as d_), p_), v2_), s), abstractAll,
         abstractEx, makeAddress) ->
          let (GO', o_) =
            operators
              ((I.Decl (g_, (I.decSub (d_, s)))), GE, (v2_, (I.dot1 s)),
                abstractAll, abstractEx, (makeAddressCont makeAddress)) in
          ((((makeAddress 0),
              (delay (Search.searchAll, (g_, GE, (v1_, s), abstractAll)))) ::
              GO'), o_) end
let rec createEVars =
  begin function
  | Prefix (I.Null, I.Null, I.Null) ->
      ((M.Prefix (I.Null, I.Null, I.Null)), I.id, [])
  | Prefix (Decl (g_, d_), Decl (m_, M.Top), Decl (b_, b)) ->
      let (Prefix (g'_, m'_, b'_), s', GE') =
        createEVars (M.Prefix (g_, m_, b_)) in
      ((M.Prefix
          ((I.Decl (g'_, (I.decSub (d_, s')))), (I.Decl (m'_, M.Top)),
            (I.Decl (b'_, b)))), (I.dot1 s'), GE')
  | Prefix (Decl (g_, Dec (_, v_)), Decl (m_, M.Bot), Decl (b_, _)) ->
      let (Prefix (g'_, m'_, b'_), s', GE') =
        createEVars (M.Prefix (g_, m_, b_)) in
      let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
      let x'_ = Whnf.lowerEVar x_ in
      ((M.Prefix (g'_, m'_, b'_)), (I.Dot ((I.Exp x_), s')), (x'_ :: GE')) end
let rec expand (State (name, Prefix (g_, m_, b_), v_) as s_) =
  let (Prefix (g'_, m'_, b'_), s', GE') = createEVars (M.Prefix (g_, m_, b_)) in
  let rec abstractAll acc =
    begin try
            (MetaAbstract.abstract
               (M.State (name, (M.Prefix (g'_, m'_, b'_)), (I.EClo (v_, s')))))
              :: acc
    with | Error s -> acc end in
  let rec abstractEx () =
    begin try
            raise
              (Success
                 (MetaAbstract.abstract
                    (M.State
                       (name, (M.Prefix (g'_, m'_, b'_)), (I.EClo (v_, s'))))))
    with | Error s -> () end in
  operators
    (g'_, GE', (v_, s'), abstractAll, abstractEx, (makeAddressInit s_))
let rec apply (_, f) = f ()
let rec menu ((State (name, Prefix (g_, m_, b_), v_), k), Sl) =
  let rec toString =
    begin function
    | (g_, Pi ((Dec (_, v_), _), _), 0) -> Print.expToString (g_, v_)
    | (g_, (Root _ as v_), 0) -> Print.expToString (g_, v_)
    | (g_, Pi ((d_, _), v_), k) -> toString ((I.Decl (g_, d_)), v_, (k - 1)) end in
(((^) "Filling   : " toString (g_, v_, k))
  (* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *))
let expand = expand
let apply = apply
let menu = menu end
