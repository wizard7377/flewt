
module type FLIT  =
  sig
    val init : string -> unit
    val initForText : unit -> unit
    val dump : string -> string -> int
    val dumpText : string -> string -> unit
    val setFlag : unit -> unit
    val setEndTcb : unit -> unit
    val dumpFlagged : string -> unit
    val dumpSymTable : string -> string -> string -> unit
  end;;




module Flit(Flit:sig
                   module Global : GLOBAL
                   module Word : WORD
                   module Pack : PACK_WORD
                   module Whnf : WHNF
                   module Names : NAMES
                   module Table : TABLE
                   module Index : INDEX
                   module Print : PRINT
                 end) : FLIT =
  struct
    module W = Word
    module I = IntSyn
    module N = Names
    module F = Names.Fixity
    module Idx = Index
    module SHT = StringHashTable
    module IHT = Table
    exception Error of string 
    let size_of_expr = 3
    let (tcb_table : (string * int) list option ref) = ref NONE
    let (tcb_size : int ref) = ref 0
    let rec print_table () =
      let rec print_table' =
        function
        | nil -> ()
        | (name, addr)::[] ->
            print (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^ ")\n")
        | (name, addr)::pairs ->
            (print
               (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^ "),\n");
             print_table' pairs) in
      print "val tcb_table := [\n";
      print_table' (valOf (!tcb_table));
      print "];\n"
    let rec print_size () =
      print (((^) "val tcb_size = " Int.toString (!tcb_size)) ^ ";\n")
    let rec init filename =
      let stream = TextIO.openIn filename in
      let linecount = (ref 0 : int ref) in
      let rec get_line () =
        ((!) ((:=) linecount) linecount) + 1; Compat.inputLine97 stream in
      let rec error () =
        raise
          (Error
             ((("Error reading file '" ^ filename) ^ "', line ") ^
                (Int.toString (!linecount)))) in
      let rec read_size () =
        match Int.fromString (get_line ()) with
        | Some tcb_size -> tcb_size
        | NONE -> error () in
      let () = (:=) tcb_size read_size () in
      let () = if (!Global.chatter) >= 3 then print_size () else () in
      let rec read_table =
        function
        | "" -> nil
        | line ->
            (match String.tokens Char.isSpace line with
             | id::addr::[] ->
                 (::) (id, (valOf (Int.fromString addr))) read_table
                   (get_line ())
             | _ -> error ()) in
      let () = (:=) tcb_table Some (read_table (get_line ())) in
      let () = if (!Global.chatter) >= 3 then print_table () else () in
      let () = TextIO.closeIn stream in ()
    let closedMask = LargeWord.fromInt 256
    let predicateMask = LargeWord.fromInt 512
    let clauseMask = LargeWord.fromInt 1024
    let (baseAddr : int ref) = ref 0
    let (startClause : int option ref) = ref NONE
    let (startSemant : int option ref) = ref NONE
    let (tuples : int ref) = ref 0
    let (out : BinIO.outstream option ref) = ref NONE
    let (symTable : W.word Table.__Table) = Table.new__ 32
    let (printTable : unit Table.__Table) = Table.new__ 32
    let (shadowTable : int SHT.__Table) = SHT.new__ 32
    let (depTable : unit IHT.__Table IHT.__Table) = IHT.new__ 32
    let (recordTable : unit IHT.__Table) = IHT.new__ 32
    let (imitatesTable : int IHT.__Table) = IHT.new__ 32
    let (replaceTable : string IHT.__Table) = IHT.new__ 32
    let rec cname cid = I.conDecName (I.sgnLookup cid)
    let rec clookup name =
      let size = (fun r -> r.1) (I.sgnSize ()) in
      let rec clookup' cid =
        if cid = size
        then raise (Error (("symbol " ^ name) ^ " not found"))
        else if (cname cid) = name then cid else clookup' (cid + 1) in
      clookup' 0
    let rec print_once cid =
      match Table.lookup printTable cid with
      | NONE ->
          (Table.insert printTable (cid, ());
           print ((Print.conDecToString (I.sgnLookup cid)) ^ "\n"))
      | Some _ -> ()
    let rec print_tuple addr code (cld, prd, cls) arg1 arg2 =
      print
        (((((((^) (((^) (((^) (((^) ((W.fmt StringCvt.DEC addr) ^ " : ")
                                  Char.toString code)
                                 ^ "\t")
                            Bool.toString cld)
                           ^ "\t")
                      Bool.toString prd)
                     ^ "\t")
                Bool.toString cls)
               ^ "\t")
              ^ (W.fmt StringCvt.DEC arg1))
             ^ "\t")
            ^ (W.fmt StringCvt.DEC arg2))
           ^ "\n")
    let rec writeArray array =
      match !out with
      | Some stream ->
          (((!) ((:=) tuples) tuples) + 1;
           BinIO.output
             (stream,
               (Word8ArraySlice.vector
                  (Word8ArraySlice.slice (array, 0, NONE)))))
      | NONE -> ()
    let rec tuple code ((cld, prd, cls) as flags) arg1 arg2 =
      let addr = W.fromInt ((!) ((+) (!tuples)) tcb_size) in
      let array =
        Word8Array.array
          ((Pack.bytesPerElem * size_of_expr), (Word8.fromInt 0)) in
      let opcode = ref (Word8.toLargeWord (Byte.charToByte code)) in
      if cld then (:=) opcode LargeWord.orb ((!opcode), closedMask) else ();
      if prd
      then (:=) opcode LargeWord.orb ((!opcode), predicateMask)
      else ();
      if cls then (:=) opcode LargeWord.orb ((!opcode), clauseMask) else ();
      Pack.update (array, 0, (!opcode));
      Pack.update (array, 1, (W.toLargeWord arg1));
      Pack.update (array, 2, (W.toLargeWord arg2));
      if (!Global.chatter) >= 4
      then print_tuple (addr, code, flags, arg1, arg2)
      else ();
      writeArray array;
      addr
    let kd () = W.fromInt 0
    let ty () = W.fromInt 1
    let rec const __0__ __1__ =
      match (__0__, __1__) with
      | (true__, ty) ->
          tuple ('c', (true__, true__, true__), (W.fromInt 0), ty)
      | (false__, _) -> W.fromInt 0
    let rec var __2__ __3__ =
      match (__2__, __3__) with
      | (true__, ty) ->
          tuple ('v', (false__, false__, false__), (W.fromInt 0), ty)
      | (false__, _) -> W.fromInt 0
    let rec pi __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (true__, flags, var, exp) -> tuple ('p', flags, var, exp)
      | (false__, _) -> W.fromInt 0
    let rec lam __8__ __9__ __10__ __11__ =
      match (__8__, __9__, __10__, __11__) with
      | (true__, flags, var, exp) -> tuple ('l', flags, var, exp)
      | (false__, _) -> W.fromInt 0
    let rec app __12__ __13__ __14__ __15__ =
      match (__12__, __13__, __14__, __15__) with
      | (true__, flags, exp, arg) -> tuple ('a', flags, exp, arg)
      | (false__, _) -> W.fromInt 0
    let rec annotate __16__ __17__ __18__ __19__ =
      match (__16__, __17__, __18__, __19__) with
      | (true__, flags, arg, exp) -> tuple (':', flags, arg, exp)
      | (false__, _) -> W.fromInt 0
    let rec scanNumber string =
      let rec check =
        function
        | _::_ as chars -> List.all Char.isDigit chars
        | nil -> false__ in
      if check (String.explode string)
      then StringCvt.scanString (W.scan StringCvt.DEC) string
      else NONE
    let rec scanBinopPf oper string =
      let args = String.tokens (fun c -> c = oper) string in
      match args with
      | arg1::arg2::[] ->
          (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
           | (Some d1, Some d2) -> Some (d1, d2)
           | _ -> NONE)
      | _ -> NONE
    let rec scanTernopPf oper1 oper2 string =
      let args = String.tokens (fun c -> c = oper1) string in
      match args with
      | arg1::args2::[] ->
          let args' = String.tokens (fun c -> c = oper2) args2 in
          (match args' with
           | arg2::arg3::[] ->
               (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                        (StringCvt.scanString (W.scan StringCvt.DEC) arg2),
                        (StringCvt.scanString (W.scan StringCvt.DEC) arg3))
                with
                | (Some d1, Some d2, Some d3) -> Some (d1, d2, d3)
                | _ -> NONE)
           | _ -> NONE)
      | _ -> NONE
    let rec isPredicate cid =
      match ((!startClause), (I.constUni cid)) with
      | (Some cid', I.Kind) -> cid >= cid'
      | _ -> false__
    let rec headCID =
      function
      | Const cid -> Some cid
      | Skonst cid -> Some cid
      | Def cid -> Some cid
      | NSDef cid -> Some cid
      | _ -> NONE
    let rec isClause cid =
      match ((!startClause), (I.constUni cid)) with
      | (Some cid', I.Type) ->
          if cid >= cid'
          then
            let a = I.targetHead (I.constType cid) in
            let clauses =
              List.mapPartial headCID (Idx.lookup (valOf (headCID a))) in
            List.exists (fun x -> x = cid) clauses
          else false__
      | _ -> false__
    let rec lookup cid =
      match Table.lookup symTable cid with
      | Some idx -> idx
      | NONE ->
          let idx =
            compileConDec
              ((I.sgnLookup cid), ((isPredicate cid), (isClause cid))) in
          let () = Table.insert symTable (cid, idx) in
          let () = if (!Global.chatter) >= 3 then print_once cid else () in
          idx
    let rec compileUni = function | I.Kind -> kd () | I.Type -> ty ()
    let rec compileExpN __20__ __21__ __22__ __23__ =
      match (__20__, __21__, __22__, __23__) with
      | (generate, __G, Uni (__V), flags) -> compileUni __V
      | (generate, __G, Pi ((Dec (_, __U1), _), __U2),
         ((cld, _, _) as flags)) ->
          let idxU1 =
            compileExpN generate (__G, __U1, (cld, false__, false__)) in
          let idxU1var = var generate idxU1 in
          let idxU2 =
            compileExpN generate
              ((I.Decl (__G, idxU1var)), __U2, (false__, false__, false__)) in
          pi generate (flags, idxU1var, idxU2)
      | (generate, __G, Lam ((Dec (_, __U1) as D), __U2),
         ((cld, _, _) as flags)) ->
          let idxU1 =
            compileExpN generate (__G, __U1, (cld, false__, false__)) in
          let idxU1var = var generate idxU1 in
          let idxU2 =
            compileExpN generate
              ((I.Decl (__G, idxU1var)), __U2, (false__, false__, false__)) in
          lam generate (flags, idxU1var, idxU2)
      | (generate, __G, (Root (__H, __S) as U), flags) ->
          let idx = compileHead generate (__G, __H) in
          compileSpine generate (__G, idx, __S, flags)
      | (generate, __G, FgnExp csfe, flags) ->
          compileExp generate
            (__G, (I.FgnExpStd.ToInternal.apply csfe ()), flags)
    let rec compileSpine __24__ __25__ __26__ __27__ __28__ =
      match (__24__, __25__, __26__, __27__, __28__) with
      | (generate, __G, idx, I.Nil, flags) -> idx
      | (generate, __G, idx, App (__U1, I.Nil), ((cld, _, _) as flags)) ->
          let idxU1 =
            compileExpN generate (__G, __U1, (cld, false__, false__)) in
          app generate (flags, idx, idxU1)
      | (generate, __G, idx, App (__U1, __S), ((cld, _, _) as flags)) ->
          let idxU1 =
            compileExpN generate (__G, __U1, (cld, false__, false__)) in
          compileSpine generate
            (__G, (app generate ((cld, false__, false__), idx, idxU1)), __S,
              flags)
    let rec compileHead __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (generate, __G, BVar k) -> I.ctxLookup (__G, k)
      | (generate, __G, Const cid) -> lookup cid
      | (generate, __G, Def cid) -> lookup cid
      | (generate, __G, NSDef cid) -> lookup cid
      | (generate, __G, FgnConst (cs, conDec)) ->
          compileFgnDec generate (__G, conDec)
    let rec compileFgnDec __32__ __33__ __34__ =
      match (__32__, __33__, __34__) with
      | (true__, __G, conDec) ->
          let name = I.conDecName conDec in
          let flags = (true__, false__, false__) in
          (match scanNumber name with
           | Some n -> tuple ('#', flags, n, (W.fromInt 0))
           | NONE ->
               (match scanBinopPf '/' name with
                | Some (n1, n2) -> tuple ('/', flags, n1, n2)
                | NONE ->
                    (match scanBinopPf '+' name with
                     | Some (n1, n2) -> tuple ('+', flags, n1, n2)
                     | NONE ->
                         (match scanBinopPf '*' name with
                          | Some (n1, n2) -> tuple ('*', flags, n1, n2)
                          | NONE ->
                              raise
                                (Error ("unknown foreign constant " ^ name))))))
      | (false__, _) -> W.fromInt 0
    let rec compileExp generate (__G) (__U) flags =
      compileExpN generate (__G, (Whnf.normalize (__U, I.id)), flags)
    let rec compileConDec __35__ __36__ =
      match (__35__, __36__) with
      | ((ConDec (_, _, _, _, __V, _) as condec), (true__, cls)) ->
          const true__
            (compileExpN true__ (I.Null, __V, (true__, true__, cls)))
      | ((ConDec (_, _, _, _, _, _) as condec), (pred, cls)) ->
          raise
            (Error ("attempt to shadow constant " ^ (I.conDecName condec)))
      | ((ConDef (_, _, _, __U, __V, _, _) as condec), (pred, cls)) ->
          let exp =
            compileExpN true__ (I.Null, __V, (true__, false__, false__)) in
          let arg = compileExpN true__ (I.Null, __U, (true__, pred, cls)) in
          annotate true__ ((true__, pred, cls), arg, exp)
      | ((AbbrevDef (_, _, _, __U, __V, _) as condec), (pred, cls)) ->
          let exp =
            compileExpN true__ (I.Null, __V, (true__, false__, false__)) in
          let arg = compileExpN true__ (I.Null, __U, (true__, pred, cls)) in
          annotate true__ ((true__, pred, cls), arg, exp)
    let rec initTuples () =
      let _ = tuples := 0 in
      let _ = Table.clear symTable in
      let _ = Table.clear printTable in
      match !tcb_table with
      | Some l ->
          List.app
            (fun name ->
               fun idx ->
                 Table.insert symTable ((clookup name), (W.fromInt idx))) l
      | NONE -> raise (Error "dump(...) before init(...)")
    let rec dump name file =
      let rec dump' cid =
        let _ = (:=) out Some (BinIO.openOut file) in
        let stream = valOf (!out) in
        let _ = initTuples () in
        let idx = W.toInt (lookup cid) in
        let _ = BinIO.closeOut stream in idx in
      let rec error msg =
        let rec closeOut () =
          match !out with | Some stream -> BinIO.closeOut stream | NONE -> () in
        print (("Error: " ^ msg) ^ "\n"); closeOut (); (-1) in
      match N.constLookup (valOf (N.stringToQid name)) with
      | Some cid -> (try dump' cid with | Error msg -> error msg)
      | NONE -> error (("symbol " ^ name) ^ " not found\n")
    let rec setFlag () =
      match !startClause with
      | Some cid -> print "Error: flag already set\n"
      | NONE -> (:=) startClause Some (((fun r -> r.1)) (I.sgnSize ()))
    let rec setEndTcb () =
      match !startSemant with
      | Some cid -> print "Error: flag already set\n"
      | NONE -> (:=) startSemant Some (((fun r -> r.1)) (I.sgnSize ()))
    let rec dumpFlagged file =
      let max = (fun r -> r.1) (I.sgnSize ()) in
      let rec compileSeq cid =
        if cid < max then (lookup cid; compileSeq (cid + 1)) else () in
      let rec dump' cid =
        (:=) out Some (BinIO.openOut file);
        initTuples ();
        compileSeq cid;
        BinIO.closeOut (valOf (!out)) in
      let rec error msg =
        let rec closeOut () =
          match !out with | Some stream -> BinIO.closeOut stream | NONE -> () in
        print (("Error: " ^ msg) ^ "\n"); closeOut () in
      match !startClause with
      | Some cid -> (try dump' cid with | Error msg -> error msg)
      | NONE -> error "setFlag() has not been called yet\n"
    let rec dumpSymTable name1 name2 file =
      let stream = TextIO.openOut file in
      let Strength nonfixLevel = F.minPrec in
      let rec dumpFixity cid =
        match N.getFixity cid with
        | Infix (Strength level, F.Left) -> (level, 1)
        | Infix (Strength level, F.Right) -> (level, 2)
        | Infix (Strength level, F.None) -> (level, 3)
        | F.Nonfix -> (nonfixLevel, 0) in
      let rec dumpEntry cid =
        match ((Table.lookup symTable cid), (dumpFixity cid)) with
        | (Some idx, (level, assoc)) ->
            TextIO.output
              (stream,
                (((^) (((^) ((((I.conDecName (I.sgnLookup cid)) ^ "\t") ^
                                (Word.fmt StringCvt.DEC idx))
                               ^ "\t")
                          Int.toString level)
                         ^ "\t")
                    Int.toString assoc)
                   ^ "\n"))
        | (NONE, _) -> () in
      let rec dumpTable cid1 cid2 =
        if cid1 <= cid2
        then (dumpEntry cid1; dumpTable ((cid1 + 1), cid2))
        else () in
      let rec error msg = print (("Error: " ^ msg) ^ "\n") in
      (match ((N.constLookup (valOf (N.stringToQid name1))),
               (N.constLookup (valOf (N.stringToQid name2))))
       with
       | (Some cid1, Some cid2) -> dumpTable (cid1, cid2)
       | (NONE, _) -> error (name1 ^ " undefined")
       | (_, NONE) -> error (name2 ^ " undefined"));
      TextIO.flushOut stream;
      TextIO.closeOut stream
    let rec sort cmp l =
      let rec split l =
        let rec s __37__ __38__ __39__ =
          match (__37__, __38__, __39__) with
          | (a1, a2, nil) -> (a1, a2)
          | (a1, a2, h::t) -> s a2 (h :: a1) t in
        s nil nil l in
      let rec merge __40__ __41__ =
        match (__40__, __41__) with
        | (a, nil) -> a
        | (nil, b) -> b
        | ((a::ta as aa), (b::tb as bb)) ->
            (match cmp (a, b) with
             | EQUAL -> (::) (a :: b) merge ta tb
             | LESS -> (::) a merge ta bb
             | GREATER -> (::) b merge aa tb) in
      let rec ms =
        function
        | nil -> nil
        | s::[] -> [s]
        | a::b::[] -> merge [a] [b]
        | ll -> let (a, b) = split ll in merge (ms a) (ms b) in
      ms l
    let rec sortedKeys t =
      let r = ref [] in
      let _ = IHT.app (fun x -> (!) ((::) (r := x)) r) t in
      sort Int.compare (map (fun r -> r.1) (!r))
    exception noPriorEntry of string 
    exception Error of string 
    let rec valOfE __42__ __43__ =
      match (__42__, __43__) with | (e, NONE) -> raise e | (e, Some x) -> x
    let counter = ref 0
    let rec isShadowedBy cid =
      let name = I.conDecName (I.sgnLookup cid) in
      let currentcid =
        valOfE (noPriorEntry name) (SHT.lookup shadowTable name) in
      (name, (if currentcid <> cid then Some currentcid else NONE))
    let rec isShadowing () =
      let _ = SHT.clear shadowTable in
      let changes = ref false__ in
      let rec processDep rcid cid =
        let rec handleProblem currentcid name =
          match Table.lookup replaceTable cid with
          | Some _ -> ()
          | _ ->
              let replacement =
                Option.map (I.conDecName o I.sgnLookup)
                  (Table.lookup imitatesTable cid) in
              (((match replacement with
                 | NONE ->
                     raise
                       (Error
                          (((^) (((^) (((^) (("Error: " ^ name) ^ " (")
                                          Int.toString cid)
                                         ^ ") used by cid ")
                                    Int.toString rcid)
                                   ^ " but shadowed by ")
                              Int.toString currentcid)
                             ^ ".\n"))
                 | Some x -> ((Table.insert replaceTable (cid, x))
                     (* print ("DX planning to subtly rename " ^ Int.toString cid ^ " to " ^ x ^ "\n");  *))))
                (* Option.mapPartial
                                                    (fn x => (case isShadowedBy x of
                                                    (_, Some _) => NONE
                                                      | (x, NONE) => Some x)) *)
                (* XXX worrying - jcreed 7/05 *)) in
        let (name, sb) = isShadowedBy cid in
        match sb with
        | Some currentcid ->
            ((if
                ((<) cid valOf (!startSemant)) ||
                  ((>=) cid valOf (!startClause))
              then handleProblem (currentcid, name)
              else
                (let newname = (^) "shadowed_" Int.toString (!counter) in
                 ((I.rename (cid, newname);
                   SHT.insert shadowTable (newname, cid);
                   ((!) ((:=) counter) counter) + 1;
                   changes := true__)
                   (* print ("DX renaming " ^ Int.toString cid ^ " to " ^ newname ^ "\n"); *))))
            (* problematic shadowing *)(* nonproblematic shadowing - change its name *))
        | NONE -> () in
      let rec processCid cid =
        let name = I.conDecName (I.sgnLookup cid) in
        (((try
             List.app (processDep cid)
               (sortedKeys (valOf (IHT.lookup depTable cid)))
           with | Option -> ());
          SHT.insert shadowTable (name, cid))
          (* val _ = print ("DX processing cid " ^ Int.toString cid ^ " which has name [" ^ name ^ "].\n") *)) in
      (((try List.app processCid (sortedKeys recordTable)
         with
         | noPriorEntry s as e ->
             (print (("Error: No Prior Entry: " ^ s) ^ "\n"); raise e));
        !changes)
        (* val _ = print "clearing table...\n" *))
    let rec is_def cid = try I.constDef cid; true__ with | Match -> false__
    let rec fixityDec cid =
      match N.getFixity cid with
      | Infix _ as f ->
          ((^) ((F.toString f) ^ " ") I.conDecName (I.sgnLookup cid)) ^ ".\n"
      | _ -> ""
    let rec record_once k cid =
      match IHT.insertShadow recordTable (cid, ()) with
      | NONE -> ((k cid)
          (* print("DX Recording " ^ Int.toString cid ^ ".\n") ; *))
      | Some _ -> ()
    let rec recordDependency x y =
      let table =
        match IHT.lookup depTable x with
        | Some y -> y
        | NONE -> let t = IHT.new__ 32 in (IHT.insert depTable (x, t); t) in
      ((IHT.insert table (y, ()))
        (*        val msg = "DX dep " ^ Int.toString x ^ " on " ^ Int.toString y ^ "\n" *))
    open I
    let rec etaReduce __44__ __45__ =
      match (__44__, __45__) with
      | (n, Root (h, sp)) -> if etaReduceSpine n sp then Some h else NONE
      | (n, Lam (_, t)) -> etaReduce (n + 1) t
      | (_, _) -> NONE
    let rec etaReduceSpine __46__ __47__ =
      match (__46__, __47__) with
      | (n, App (fst, sp)) ->
          (match etaReduce 0 fst with
           | Some (BVar n') -> (n = n') && (etaReduceSpine (n - 1) sp)
           | _ -> false__)
      | (n, Nil) -> true__
      | (n, _) -> false__
    let rec checkTrivial cid =
      match sgnLookup cid with
      | AbbrevDef (_, _, _, __M, __V, _) ->
          (match etaReduce 0 __M with
           | Some (Const cid') ->
               (print
                  (((^) (((^) "DX inserting " Int.toString cid') ^ " = ")
                      Int.toString cid)
                     ^ "\n");
                Table.insert imitatesTable (cid', cid))
           | _ -> ())
      | _ -> ()
    let rec travExp __48__ __49__ =
      match (__48__, __49__) with
      | (cid, Uni _) -> ()
      | (cid, Pi ((__D, _), __B)) -> (travDec cid __D; travExp cid __B)
      | (cid, Root (__H, __S)) -> (travHead cid __H; travSpine cid __S)
      | (cid, Redex (__M, __S)) -> (travExp cid __M; travSpine cid __S)
      | (cid, Lam (__D, __M)) -> (travDec cid __D; travExp cid __M)
      | (cid, _) -> ()
    let rec travDec __50__ __51__ =
      match (__50__, __51__) with
      | (cid, Dec (_, __A)) -> travExp cid __A
      | (cid, BDec (_, (c, _))) -> (recordDependency (cid, c); traverse c)
    let rec travSpine __52__ __53__ =
      match (__52__, __53__) with
      | (cid, Nil) -> ()
      | (cid, App (__M, __S)) -> (travExp cid __M; travSpine cid __S)
      | (cid, _) -> ()
    let rec travHead cid h =
      Option.map (fun n -> recordDependency (cid, n); traverse n) (headCID h)
    let rec traverseDescendants' __54__ __55__ =
      match (__54__, __55__) with
      | (cid, ConDec (_, _, _, _, __V, _)) -> travExp cid __V
      | (cid, ConDef (_, _, _, __M, __V, _, _)) ->
          (travExp cid __M; travExp cid __V)
      | (cid, AbbrevDef (_, _, _, __M, __V, _)) ->
          (travExp cid __M; travExp cid __V)
      | (cid, _) -> ()
    let rec traverseDescendants cid =
      traverseDescendants' cid (I.sgnLookup cid)
    let rec traverse cid =
      let name = conDecName (sgnLookup cid) in
      ((record_once traverseDescendants cid)
        (* val message = "DX Traversing cid = " ^ Int.toString cid ^ " name = " ^ name ^ "\n" *))
    let rec initForText () =
      startClause := NONE;
      startSemant := NONE;
      Table.clear depTable;
      Table.clear recordTable;
      Table.clear imitatesTable;
      Table.clear replaceTable
    exception InfixWithImplicitArgs 
    let rec appRange f min max =
      if min < max then (f min; appRange f (min + 1) max) else ()
    let rec dumpAll max first outputSemant outputChecker =
      let streamSemant = TextIO.openOut outputSemant in
      let streamChecker = TextIO.openOut outputChecker in
      let streamTcb = TextIO.openOut "dumptcb" in
      let rec waitUntilFalse f = if f () then waitUntilFalse f else () in
      let rec outputCid cid =
        let s = (Print.conDecToString (I.sgnLookup cid)) ^ "\n" in
        let s' =
          if ((>=) cid valOf (!startClause)) && (is_def cid)
          then (if isClause cid then "%clause " ^ s else s)
          else s in
        let stream =
          ((if (<) cid valOf (!startSemant)
            then streamTcb
            else
              if (>=) cid valOf (!startClause)
              then streamChecker
              else streamSemant)
          (* DX *)) in
        TextIO.output (stream, (s' ^ (fixityDec cid)))(* DX *)(* if cid < (valOf(!startSemant)) then () else *) in
      ((appRange checkTrivial 0 max;
        appRange traverse first max;
        appRange (fun cid -> Table.insert recordTable (cid, ())) 0
          (valOf (!startSemant));
        waitUntilFalse isShadowing;
        Table.app IntSyn.rename replaceTable;
        List.app outputCid (sortedKeys recordTable);
        TextIO.closeOut streamSemant;
        TextIO.closeOut streamChecker;
        TextIO.closeOut streamTcb)
        (* DX *)(* DX *))
    let rec dumpText outputSemant outputChecker =
      let max = (fun r -> r.1) (I.sgnSize ()) in
      let rec correctFixities cid =
        if cid < max
        then
          ((let fixity = N.getFixity cid in
            let imp = I.constImp cid in
            let name = I.conDecName (I.sgnLookup cid) in
            let inSemant =
              ((>=) cid valOf (!startSemant)) &&
                ((<) cid valOf (!startClause)) in
            let makeNonfix =
              match (fixity, imp, inSemant) with
              | (Infix _, _, true__) -> ((true__)
                  (*print ("DX setting nonfix " ^ Int.toString cid ^ "\n"); *))
              | (Infix _, 0, false__) -> false__
              | (Infix _, _, false__) -> raise InfixWithImplicitArgs
              | (_, _, _) -> false__ in
            ((if makeNonfix then N.installFixity (cid, F.Nonfix) else ())
              (* val _ = case fixity of F.Infix _ => print ("DX Infix " ^ Int.toString cid ^ " " ^ name ^ " " ^ Int.toString imp ^ " \n") | _ => () *)));
           correctFixities (cid + 1))
        else () in
      let _ = correctFixities 0 in
      let rec error msg = print (("Error: " ^ msg) ^ "\n") in
      ((match !startClause with
        | Some cid ->
            (try dumpAll (max, cid, outputSemant, outputChecker)
             with | Error msg -> error msg)
        | NONE -> error "setFlag() has not been called yet\n")
        (* val _ = print ("DX startSemant = " ^ Int.toString(valOf(!startSemant)) ^ "\n") *)
        (* val _ = print ("DX startClause = " ^ Int.toString(valOf(!startClause)) ^ "\n") *))
    let init = init
    let initForText = initForText
    let dump = dump
    let dumpText = dumpText
    let setFlag = setFlag
    let setEndTcb = setEndTcb
    let dumpFlagged = dumpFlagged
    let dumpSymTable = dumpSymTable
  end ;;




module Flit =
  (Make_Flit)(struct
                module Global = Global
                module Word = Word32
                module Pack = PackWord32Little
                module IntSyn = IntSyn
                module Whnf = Whnf
                module Print = Print
                module Names = Names
                module Index = Index
                module Table = IntRedBlackTree
              end);;
