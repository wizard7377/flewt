
module IndexSkolem(IndexSkolem:sig
                                 module Global : GLOBAL
                                 module Queue : QUEUE
                               end) : INDEX =
  struct
    module I = IntSyn
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let (indexArray : IntSyn.__Head Queue.queue Array.array) =
      Array.array ((Global.maxCid + 1), Queue.empty)
    let rec reset () = Array.modify (fun _ -> Queue.empty) indexArray
    let rec update a c =
      Array.update
        (indexArray, a, (Queue.insert (c, (Array.sub (indexArray, a)))))
    let rec install __0__ __1__ =
      match (__0__, __1__) with
      | (fromCS, (Const c as H)) ->
          (match (fromCS, (I.sgnLookup c)) with
           | (_, ConDec (_, _, _, _, __A, I.Type)) ->
               update ((cidFromHead (I.targetHead __A)), __H)
           | (I.Clause, ConDef (_, _, _, _, __A, I.Type, _)) ->
               update ((cidFromHead (I.targetHead __A)), (I.Def c))
           | _ -> ())
      | (fromCS, (Skonst c as H)) ->
          (match I.sgnLookup c with
           | SkoDec (_, _, _, __A, I.Type) ->
               update ((cidFromHead (I.targetHead __A)), __H)
           | _ -> ())
    let rec remove a cid =
      match Queue.deleteEnd (Array.sub (indexArray, a)) with
      | NONE -> ()
      | Some (Const cid', queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
      | Some (Skonst cid', queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
    let rec uninstall cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, __A, I.Type) ->
          remove ((cidFromHead (I.targetHead __A)), cid)
      | SkoDec (_, _, _, __A, I.Type) ->
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
      let rec lk __2__ __3__ =
        match (__2__, __3__) with
        | (l, NONE) -> l
        | (l, Some q') -> (Array.update (indexArray, a, q'); l) in
      lk (Queue.toList (Array.sub (indexArray, a)))
    let reset = reset
    let resetFrom = resetFrom
    let install = install
    let lookup = lookup
  end ;;
