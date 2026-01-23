module type ORDER  =
  sig
    exception Error of string 
    type 'a order_ =
      | Arg of 'a 
      | Lex of 'a order_ list 
      | Simul of 'a order_ list 
    type predicate_ =
      | Less of (int order_ * int order_) 
      | Leq of (int order_ * int order_) 
      | Eq of (int order_ * int order_) 
    type mutual_ =
      | Empty 
      | LE of (IntSyn.cid * mutual_) 
      | LT of (IntSyn.cid * mutual_) 
    type tDec_ =
      | TDec of (int order_ * mutual_) 
    type rDec_ =
      | RDec of (predicate_ * mutual_) 
    val reset : unit -> unit
    val resetROrder : unit -> unit
    val install : (IntSyn.cid * tDec_) -> unit
    val uninstall : IntSyn.cid -> bool
    val installROrder : (IntSyn.cid * rDec_) -> unit
    val uninstallROrder : IntSyn.cid -> bool
    val selLookup : IntSyn.cid -> int order_
    val selLookupROrder : IntSyn.cid -> predicate_
    val mutLookup : IntSyn.cid -> mutual_
    val closure : IntSyn.cid -> IntSyn.cid list
  end


module Order(Order:sig module Table : TABLE end) : ORDER =
  struct
    exception Error of string 
    type 'a order_ =
      | Arg of 'a 
      | Lex of 'a order_ list 
      | Simul of 'a order_ list 
    type predicate_ =
      | Less of (int order_ * int order_) 
      | Leq of (int order_ * int order_) 
      | Eq of (int order_ * int order_) 
    type mutual_ =
      | Empty 
      | LE of (IntSyn.cid * mutual_) 
      | LT of (IntSyn.cid * mutual_) 
    type tDec_ =
      | TDec of (int order_ * mutual_) 
    type rDec_ =
      | RDec of (predicate_ * mutual_) 
    module I = IntSyn
    let ((OrderTable) : tDec_ Table.table_) = Table.new_ 0
    let ((RedOrderTable) : rDec_ Table.table_) = Table.new_ 0
    let rec reset () = Table.clear OrderTable
    let rec resetROrder () = Table.clear RedOrderTable
    let rec install (cid, o_) = Table.insert OrderTable (cid, o_)
    let rec uninstall cid =
      begin match Table.lookup OrderTable cid with
      | None -> false
      | Some _ -> (begin Table.delete OrderTable cid; true end) end
  let rec installROrder (cid, p_) = Table.insert RedOrderTable (cid, p_)
  let rec uninstallROrder cid =
    begin match Table.lookup RedOrderTable cid with
    | None -> false
    | Some _ -> (begin Table.delete RedOrderTable cid; true end) end
let rec lookup cid = Table.lookup OrderTable cid
let rec lookupROrder cid = Table.lookup RedOrderTable cid
let rec selLookup a =
  begin match lookup a with
  | None ->
      raise
        (Error
           ((^) "No termination order assigned for " I.conDecName
              (I.sgnLookup a)))
  | Some (TDec (s_, _)) -> s_ end
let rec selLookupROrder a =
  begin match lookupROrder a with
  | None ->
      raise
        (Error
           (((^) "No reduction order assigned for " I.conDecName
               (I.sgnLookup a))
              ^ "."))
  | Some (RDec (p_, _)) -> p_ end
let rec mutLookupROrder a =
  begin match lookupROrder a with
  | None ->
      raise
        (Error
           (((^) "No order assigned for " I.conDecName (I.sgnLookup a)) ^ "."))
  | Some (RDec (_, m_)) -> m_ end
let rec mutLookup a =
  begin match lookup a with
  | None ->
      raise
        (Error ((^) "No order assigned for " I.conDecName (I.sgnLookup a)))
  | Some (TDec (_, m_)) -> m_ end
let rec mutual a =
  let rec mutual' =
    begin function
    | (Empty, a's) -> a's
    | (LE (a, m_), a's) -> mutual' (m_, (a :: a's))
    | (LT (a, m_), a's) -> mutual' (m_, (a :: a's)) end in
mutual' ((mutLookup a), [])
let rec closure =
  begin function
  | ([], a2s) -> a2s
  | (a::a1s, a2s) -> if List.exists (begin function | a' -> a = a' end) a2s
      then begin closure (a1s, a2s) end
  else begin closure (((mutual a) @ a1s), (a :: a2s)) end end
let reset = reset
let resetROrder = resetROrder
let install = install
let uninstall = uninstall
let installROrder = installROrder
let uninstallROrder = uninstallROrder
let selLookup = selLookup
let selLookupROrder = selLookupROrder
let mutLookup = mutLookup
let closure = begin function | a -> closure ([a], []) end end



module Order = (Order)(struct module Table = IntRedBlackTree end)