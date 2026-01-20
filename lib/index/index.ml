
module type INDEX  =
  sig
    val reset : unit -> unit
    val resetFrom : IntSyn.cid -> unit
    val install : IntSyn.__ConDecForm -> IntSyn.__Head -> unit
    val lookup : IntSyn.cid -> IntSyn.__Head list
  end;;




module Index(Index:sig module Global : GLOBAL module Queue : QUEUE end) :
  INDEX =
  struct
    module I = IntSyn
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let (indexArray : IntSyn.__Head Queue.queue Array.array) =
      Array.array ((Global.maxCid + 1), Queue.empty)
    let rec reset () = Array.modify (fun _ -> Queue.empty) indexArray
    let rec update a c =
      Array.update
        (indexArray, a, (Queue.insert (c, (Array.sub (indexArray, a)))))
    let rec install fromCS (Const c as H) =
      match (fromCS, (I.sgnLookup c)) with
      | (_, ConDec (_, _, _, _, __A, I.Type)) ->
          update ((cidFromHead (I.targetHead __A)), __H)
      | (I.Clause, ConDef (_, _, _, _, __A, I.Type, _)) ->
          update ((cidFromHead (I.targetHead __A)), (I.Def c))
      | _ -> ()
    let rec remove a cid =
      match Queue.deleteEnd (Array.sub (indexArray, a)) with
      | None -> ()
      | Some ((Const cid' as c), queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
    let rec uninstall cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, __A, I.Type) ->
          remove ((cidFromHead (I.targetHead __A)), cid)
      | ConDef (_, _, _, _, __A, I.Type, _) ->
          remove ((cidFromHead (I.targetHead __A)), cid)
      | _ -> ()
    let rec resetFrom mark =
      let (limit, _) = I.sgnSize () in
      let rec iter i =
        if i < mark
        then ()
        else (uninstall i; Array.update (indexArray, i, Queue.empty)) in
      iter (limit - 1)
    let rec lookup a =
      let rec lk __0__ __1__ =
        match (__0__, __1__) with
        | (l, None) -> l
        | (l, Some q') -> (Array.update (indexArray, a, q'); l) in
      lk (Queue.toList (Array.sub (indexArray, a)))
    let reset = reset
    let resetFrom = resetFrom
    let install = install
    let lookup = lookup
  end ;;




module Index =
  (Make_Index)(struct module Global = Global
                      module Queue = Queue end)
module IndexSkolem =
  (Make_IndexSkolem)(struct module Global = Global
                            module Queue = Queue end);;
