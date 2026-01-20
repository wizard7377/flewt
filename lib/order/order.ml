
module type ORDER  =
  sig
    exception Error of string 
    type 'a __Order =
      | Arg of 'a 
      | Lex of 'a __Order list 
      | Simul of 'a __Order list 
    type __Predicate =
      | Less of (int __Order * int __Order) 
      | Leq of (int __Order * int __Order) 
      | Eq of (int __Order * int __Order) 
    type __Mutual =
      | Empty 
      | LE of (IntSyn.cid * __Mutual) 
      | LT of (IntSyn.cid * __Mutual) 
    type __TDec =
      | TDec of (int __Order * __Mutual) 
    type __RDec =
      | RDec of (__Predicate * __Mutual) 
    val reset : unit -> unit
    val resetROrder : unit -> unit
    val install : IntSyn.cid -> __TDec -> unit
    val uninstall : IntSyn.cid -> bool
    val installROrder : IntSyn.cid -> __RDec -> unit
    val uninstallROrder : IntSyn.cid -> bool
    val selLookup : IntSyn.cid -> int __Order
    val selLookupROrder : IntSyn.cid -> __Predicate
    val mutLookup : IntSyn.cid -> __Mutual
    val closure : IntSyn.cid -> IntSyn.cid list
  end;;




module Order(Order:sig module Table : TABLE end) : ORDER =
  struct
    exception Error of string 
    type 'a __Order =
      | Arg of 'a 
      | Lex of 'a __Order list 
      | Simul of 'a __Order list 
    type __Predicate =
      | Less of (int __Order * int __Order) 
      | Leq of (int __Order * int __Order) 
      | Eq of (int __Order * int __Order) 
    type __Mutual =
      | Empty 
      | LE of (IntSyn.cid * __Mutual) 
      | LT of (IntSyn.cid * __Mutual) 
    type __TDec =
      | TDec of (int __Order * __Mutual) 
    type __RDec =
      | RDec of (__Predicate * __Mutual) 
    module I = IntSyn
    let ((OrderTable) : __TDec Table.__Table) = Table.new__ 0
    let ((RedOrderTable) : __RDec Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear OrderTable
    let rec resetROrder () = Table.clear RedOrderTable
    let rec install cid (__O) = Table.insert OrderTable (cid, __O)
    let rec uninstall cid =
      match Table.lookup OrderTable cid with
      | NONE -> false__
      | Some _ -> (Table.delete OrderTable cid; true__)
    let rec installROrder cid (__P) = Table.insert RedOrderTable (cid, __P)
    let rec uninstallROrder cid =
      match Table.lookup RedOrderTable cid with
      | NONE -> false__
      | Some _ -> (Table.delete RedOrderTable cid; true__)
    let rec lookup cid = Table.lookup OrderTable cid
    let rec lookupROrder cid = Table.lookup RedOrderTable cid
    let rec selLookup a =
      match lookup a with
      | NONE ->
          raise
            (Error
               ((^) "No termination order assigned for " I.conDecName
                  (I.sgnLookup a)))
      | Some (TDec (__S, _)) -> __S
    let rec selLookupROrder a =
      match lookupROrder a with
      | NONE ->
          raise
            (Error
               (((^) "No reduction order assigned for " I.conDecName
                   (I.sgnLookup a))
                  ^ "."))
      | Some (RDec (__P, _)) -> __P
    let rec mutLookupROrder a =
      match lookupROrder a with
      | NONE ->
          raise
            (Error
               (((^) "No order assigned for " I.conDecName (I.sgnLookup a)) ^
                  "."))
      | Some (RDec (_, __M)) -> __M
    let rec mutLookup a =
      match lookup a with
      | NONE ->
          raise
            (Error
               ((^) "No order assigned for " I.conDecName (I.sgnLookup a)))
      | Some (TDec (_, __M)) -> __M
    let rec mutual a =
      let rec mutual' __0__ __1__ =
        match (__0__, __1__) with
        | (Empty, a's) -> a's
        | (LE (a, __M), a's) -> mutual' (__M, (a :: a's))
        | (LT (a, __M), a's) -> mutual' (__M, (a :: a's)) in
      mutual' ((mutLookup a), nil)
    let rec closure __2__ __3__ =
      match (__2__, __3__) with
      | (nil, a2s) -> a2s
      | (a::a1s, a2s) ->
          if List.exists (fun a' -> a = a') a2s
          then closure (a1s, a2s)
          else closure (((mutual a) @ a1s), (a :: a2s))
    let reset = reset
    let resetROrder = resetROrder
    let install = install
    let uninstall = uninstall
    let installROrder = installROrder
    let uninstallROrder = uninstallROrder
    let selLookup = selLookup
    let selLookupROrder = selLookupROrder
    let mutLookup = mutLookup
    let closure a = closure ([a], nil)
  end ;;




module Order = (Make_Order)(struct module Table = IntRedBlackTree end);;
