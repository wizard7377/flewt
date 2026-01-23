module type INDEX  =
  sig
    val reset : unit -> unit
    val resetFrom : IntSyn.cid -> unit
    val install : IntSyn.conDecForm_ -> IntSyn.head_ -> unit
    val lookup : IntSyn.cid -> IntSyn.head_ list
  end


module Index(Index:sig module Global : GLOBAL module Queue : QUEUE end) :
  INDEX =
  struct
    module I = IntSyn
    let rec cidFromHead = begin function | Const c -> c | Def c -> c end
    let (indexArray : IntSyn.head_ Queue.queue Array.array) =
      Array.array ((Global.maxCid + 1), Queue.empty)
    let rec reset () = Array.modify (begin function | _ -> Queue.empty end)
      indexArray
  let rec update (a, c) =
    Array.update
      (indexArray, a, (Queue.insert (c, (Array.sub (indexArray, a)))))
  let rec install fromCS (Const c as h_) =
    begin match (fromCS, (I.sgnLookup c)) with
    | (_, ConDec (_, _, _, _, a_, I.Type)) ->
        update ((cidFromHead (I.targetHead a_)), h_)
    | (I.Clause, ConDef (_, _, _, _, a_, I.Type, _)) ->
        update ((cidFromHead (I.targetHead a_)), (I.Def c))
    | _ -> () end
let rec remove (a, cid) =
  begin match Queue.deleteEnd (Array.sub (indexArray, a)) with
  | None -> ()
  | Some ((Const cid' as c), queue') ->
      if cid = cid' then begin Array.update (indexArray, a, queue') end
      else begin () end end
let rec uninstall cid =
  begin match I.sgnLookup cid with
  | ConDec (_, _, _, _, a_, I.Type) ->
      remove ((cidFromHead (I.targetHead a_)), cid)
  | ConDef (_, _, _, _, a_, I.Type, _) ->
      remove ((cidFromHead (I.targetHead a_)), cid)
  | _ -> () end
let rec resetFrom mark =
  let (limit, _) = I.sgnSize () in
  let rec iter i = if i < mark then begin () end
    else begin
      (begin uninstall i; Array.update (indexArray, i, Queue.empty) end) end in
iter (limit - 1)
let rec lookup a =
  let rec lk =
    begin function
    | (l, None) -> l
    | (l, Some q') -> (begin Array.update (indexArray, a, q'); l end) end in
lk (Queue.toList (Array.sub (indexArray, a)))
let reset = reset
let resetFrom = resetFrom
let install = install
let lookup = lookup end



module Index =
  (Index)(struct module Global = Global
                      module Queue = Queue end)
module IndexSkolem =
  (IndexSkolem)(struct module Global = Global
                            module Queue = Queue end)