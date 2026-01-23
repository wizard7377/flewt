module type FLIT  =
  sig
    val init : string -> unit
    val initForText : unit -> unit
    val dump : (string * string) -> int
    val dumpText : (string * string) -> unit
    val setFlag : unit -> unit
    val setEndTcb : unit -> unit
    val dumpFlagged : string -> unit
    val dumpSymTable : (string * string * string) -> unit
  end


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
    let (tcb_table : (string * int) list option ref) = ref None
    let (tcb_size : int ref) = ref 0
    let rec print_table () =
      let rec print_table' =
        begin function
        | [] -> ()
        | (name, addr)::[] ->
            print (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^ ")\n")
        | (name, addr)::pairs ->
            (begin print
                     (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^
                        "),\n");
             print_table' pairs end) end in
    begin print "val tcb_table := [\n";
    print_table' (valOf !tcb_table);
    print "];\n" end
let rec print_size () =
  print (((^) "val tcb_size = " Int.toString !tcb_size) ^ ";\n")
let rec init filename =
  let stream = TextIO.openIn filename in
  let linecount = (ref 0 : int ref) in
  let rec get_line () =
    begin ((!) ((:=) linecount) linecount) + 1; Compat.inputLine97 stream end in
  let rec error () =
    raise
      (Error
         ((("Error reading file '" ^ filename) ^ "', line ") ^
            (Int.toString !linecount))) in
  let rec read_size () =
    begin match Int.fromString (get_line ()) with
    | Some tcb_size -> tcb_size
    | None -> error () end in
  let () = (:=) tcb_size read_size () in
  let () = if !Global.chatter >= 3 then begin print_size () end
    else begin () end in
  let rec read_table =
    begin function
    | "" -> []
    | line ->
        (begin match String.tokens Char.isSpace line with
         | id::addr::[] ->
             (::) (id, (valOf (Int.fromString addr))) read_table
               (get_line ())
         | _ -> error () end) end in
  let () = (:=) tcb_table Some (read_table (get_line ())) in
  let () = if !Global.chatter >= 3 then begin print_table () end
    else begin () end in
  let () = TextIO.closeIn stream in ()
let closedMask = LargeWord.fromInt 256
let predicateMask = LargeWord.fromInt 512
let clauseMask = LargeWord.fromInt 1024
let (baseAddr : int ref) = ref 0
let (startClause : int option ref) = ref None
let (startSemant : int option ref) = ref None
let (tuples : int ref) = ref 0
let (out : BinIO.outstream option ref) = ref None
let (symTable : W.word Table.table_) = Table.new_ 32
let (printTable : unit Table.table_) = Table.new_ 32
let (shadowTable : int SHT.table_) = SHT.new_ 32
let (depTable : unit IHT.table_ IHT.table_) = IHT.new_ 32
let (recordTable : unit IHT.table_) = IHT.new_ 32
let (imitatesTable : int IHT.table_) = IHT.new_ 32
let (replaceTable : string IHT.table_) = IHT.new_ 32
let rec cname cid = I.conDecName (I.sgnLookup cid)
let rec clookup name =
  let size = (fun r -> r.1) (I.sgnSize ()) in
  let rec clookup' cid =
    if cid = size
    then begin raise (Error (("symbol " ^ name) ^ " not found")) end
    else begin if (cname cid) = name then begin cid end
      else begin clookup' (cid + 1) end end in
clookup' 0
let rec print_once cid =
  begin match Table.lookup printTable cid with
  | None ->
      (begin Table.insert printTable (cid, ());
       print ((Print.conDecToString (I.sgnLookup cid)) ^ "\n") end)
  | Some _ -> () end
let rec print_tuple (addr, code, (cld, prd, cls), arg1, arg2) =
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
  begin match !out with
  | Some stream ->
      (begin ((!) ((:=) tuples) tuples) + 1;
       BinIO.output
         (stream,
           (Word8ArraySlice.vector (Word8ArraySlice.slice (array, 0, None)))) end)
  | None -> () end
let rec tuple (code, ((cld, prd, cls) as flags), arg1, arg2) =
  let addr = W.fromInt ((!) ((+) !tuples) tcb_size) in
  let array =
    Word8Array.array ((Pack.bytesPerElem * size_of_expr), (Word8.fromInt 0)) in
  let opcode = ref (Word8.toLargeWord (Byte.charToByte code)) in
  begin if cld then begin (:=) opcode LargeWord.orb (!opcode, closedMask) end
  else begin () end;
    if prd then begin (:=) opcode LargeWord.orb (!opcode, predicateMask) end
    else begin () end;
  if cls then begin (:=) opcode LargeWord.orb (!opcode, clauseMask) end
  else begin () end; Pack.update (array, 0, !opcode);
Pack.update (array, 1, (W.toLargeWord arg1));
Pack.update (array, 2, (W.toLargeWord arg2));
if !Global.chatter >= 4
then begin print_tuple (addr, code, flags, arg1, arg2) end else begin () end;
writeArray array;
addr end
let kd = begin function | () -> W.fromInt 0 end
let ty = begin function | () -> W.fromInt 1 end
let rec const arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (true, ty) -> tuple ('c', (true, true, true), (W.fromInt 0), ty)
  | (false, _) -> W.fromInt 0 end
let rec var arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (true, ty) -> tuple ('v', (false, false, false), (W.fromInt 0), ty)
  | (false, _) -> W.fromInt 0 end
let rec pi arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (true, (flags, var, exp)) -> tuple ('p', flags, var, exp)
  | (false, _) -> W.fromInt 0 end
let rec lam arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (true, (flags, var, exp)) -> tuple ('l', flags, var, exp)
  | (false, _) -> W.fromInt 0 end
let rec app arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (true, (flags, exp, arg)) -> tuple ('a', flags, exp, arg)
  | (false, _) -> W.fromInt 0 end
let rec annotate arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (true, (flags, arg, exp)) -> tuple (':', flags, arg, exp)
  | (false, _) -> W.fromInt 0 end
let rec scanNumber string =
  let rec check =
    begin function
    | _::_ as chars -> List.all Char.isDigit chars
    | [] -> false end in
if check (String.explode string)
then begin StringCvt.scanString (W.scan StringCvt.DEC) string end
  else begin None end
let rec scanBinopPf oper string =
  let args = String.tokens (begin function | c -> c = oper end) string in
begin match args with
| arg1::arg2::[] ->
    (begin match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
     | (Some d1, Some d2) -> Some (d1, d2)
     | _ -> None end)
  | _ -> None end
let rec scanTernopPf oper1 oper2 string =
  let args = String.tokens (begin function | c -> c = oper1 end) string in
begin match args with
| arg1::args2::[] ->
    let args' = String.tokens (begin function | c -> c = oper2 end) args2 in
  (begin match args' with
   | arg2::arg3::[] ->
       (begin match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                      (StringCvt.scanString (W.scan StringCvt.DEC) arg2),
                      (StringCvt.scanString (W.scan StringCvt.DEC) arg3))
              with
        | (Some d1, Some d2, Some d3) -> Some (d1, d2, d3)
        | _ -> None end)
    | _ -> None end)
| _ -> None end
let rec isPredicate cid =
  begin match (!startClause, (I.constUni cid)) with
  | (Some cid', I.Kind) -> cid >= cid'
  | _ -> false end
let rec headCID =
  begin function
  | Const cid -> Some cid
  | Skonst cid -> Some cid
  | Def cid -> Some cid
  | NSDef cid -> Some cid
  | _ -> None end
let rec isClause cid =
  begin match (!startClause, (I.constUni cid)) with
  | (Some cid', I.Type) ->
      if cid >= cid'
      then
        begin let a = I.targetHead (I.constType cid) in
              let clauses =
                List.mapPartial headCID (Idx.lookup (valOf (headCID a))) in
              List.exists (begin function | x -> x = cid end) clauses end
  else begin false end
| _ -> false end
let rec lookup cid =
  begin match Table.lookup symTable cid with
  | Some idx -> idx
  | None ->
      let idx =
        compileConDec
          ((I.sgnLookup cid), ((isPredicate cid), (isClause cid))) in
      let () = Table.insert symTable (cid, idx) in
      let () = if !Global.chatter >= 3 then begin print_once cid end
        else begin () end in
      idx end
let rec compileUni = begin function | I.Kind -> kd () | I.Type -> ty () end
let rec compileExpN arg__12 arg__13 =
  begin match (arg__12, arg__13) with
  | (generate, (g_, Uni (v_), flags)) -> compileUni v_
  | (generate, (g_, Pi ((Dec (_, u1_), _), u2_), ((cld, _, _) as flags))) ->
      let idxU1 = compileExpN generate (g_, u1_, (cld, false, false)) in
      let idxU1var = var generate idxU1 in
      let idxU2 =
        compileExpN generate
          ((I.Decl (g_, idxU1var)), u2_, (false, false, false)) in
      pi generate (flags, idxU1var, idxU2)
  | (generate, (g_, Lam ((Dec (_, u1_) as d_), u2_), ((cld, _, _) as flags)))
      ->
      let idxU1 = compileExpN generate (g_, u1_, (cld, false, false)) in
      let idxU1var = var generate idxU1 in
      let idxU2 =
        compileExpN generate
          ((I.Decl (g_, idxU1var)), u2_, (false, false, false)) in
      lam generate (flags, idxU1var, idxU2)
  | (generate, (g_, (Root (h_, s_) as u_), flags)) ->
      let idx = compileHead generate (g_, h_) in
      compileSpine generate (g_, idx, s_, flags)
  | (generate, (g_, FgnExp csfe, flags)) ->
      compileExp generate (g_, (I.FgnExpStd.ToInternal.apply csfe ()), flags) end
let rec compileSpine arg__14 arg__15 =
  begin match (arg__14, arg__15) with
  | (generate, (g_, idx, I.Nil, flags)) -> idx
  | (generate, (g_, idx, App (u1_, I.Nil), ((cld, _, _) as flags))) ->
      let idxU1 = compileExpN generate (g_, u1_, (cld, false, false)) in
      app generate (flags, idx, idxU1)
  | (generate, (g_, idx, App (u1_, s_), ((cld, _, _) as flags))) ->
      let idxU1 = compileExpN generate (g_, u1_, (cld, false, false)) in
      compileSpine generate
        (g_, (app generate ((cld, false, false), idx, idxU1)), s_, flags) end
let rec compileHead arg__16 arg__17 =
  begin match (arg__16, arg__17) with
  | (generate, (g_, BVar k)) -> I.ctxLookup (g_, k)
  | (generate, (g_, Const cid)) -> lookup cid
  | (generate, (g_, Def cid)) -> lookup cid
  | (generate, (g_, NSDef cid)) -> lookup cid
  | (generate, (g_, FgnConst (cs, conDec))) ->
      compileFgnDec generate (g_, conDec) end
let rec compileFgnDec arg__18 arg__19 =
  begin match (arg__18, arg__19) with
  | (true, (g_, conDec)) ->
      let name = I.conDecName conDec in
      let flags = (true, false, false) in
      (begin match scanNumber name with
       | Some n -> tuple ('#', flags, n, (W.fromInt 0))
       | None ->
           (begin match scanBinopPf '/' name with
            | Some (n1, n2) -> tuple ('/', flags, n1, n2)
            | None ->
                (begin match scanBinopPf '+' name with
                 | Some (n1, n2) -> tuple ('+', flags, n1, n2)
                 | None ->
                     (begin match scanBinopPf '*' name with
                      | Some (n1, n2) -> tuple ('*', flags, n1, n2)
                      | None ->
                          raise (Error ("unknown foreign constant " ^ name)) end) end) end) end)
| (false, _) -> W.fromInt 0 end
let rec compileExp generate (g_, u_, flags) =
  compileExpN generate (g_, (Whnf.normalize (u_, I.id)), flags)
let rec compileConDec =
  begin function
  | ((ConDec (_, _, _, _, v_, _) as condec), (true, cls)) ->
      const true (compileExpN true (I.Null, v_, (true, true, cls)))
  | ((ConDec (_, _, _, _, _, _) as condec), (pred, cls)) ->
      raise (Error ("attempt to shadow constant " ^ (I.conDecName condec)))
  | ((ConDef (_, _, _, u_, v_, _, _) as condec), (pred, cls)) ->
      let exp = compileExpN true (I.Null, v_, (true, false, false)) in
      let arg = compileExpN true (I.Null, u_, (true, pred, cls)) in
      annotate true ((true, pred, cls), arg, exp)
  | ((AbbrevDef (_, _, _, u_, v_, _) as condec), (pred, cls)) ->
      let exp = compileExpN true (I.Null, v_, (true, false, false)) in
      let arg = compileExpN true (I.Null, u_, (true, pred, cls)) in
      annotate true ((true, pred, cls), arg, exp) end
let rec initTuples () =
  let _ = tuples := 0 in
  let _ = Table.clear symTable in
  let _ = Table.clear printTable in
  begin match !tcb_table with
  | Some l ->
      List.app
        (begin function
         | (name, idx) ->
             Table.insert symTable ((clookup name), (W.fromInt idx)) end)
      l
    | None -> raise (Error "dump(...) before init(...)") end
let rec dump (name, file) =
  let rec dump' cid =
    let _ = (:=) out Some (BinIO.openOut file) in
    let stream = valOf !out in
    let _ = initTuples () in
    let idx = W.toInt (lookup cid) in let _ = BinIO.closeOut stream in idx in
  let rec error msg =
    let rec closeOut () =
      begin match !out with
      | Some stream -> BinIO.closeOut stream
      | None -> () end in
  begin print (("Error: " ^ msg) ^ "\n"); closeOut (); (-1) end in
begin match N.constLookup (valOf (N.stringToQid name)) with
| Some cid -> (begin try dump' cid with | Error msg -> error msg end)
  | None -> error (("symbol " ^ name) ^ " not found\n") end
let rec setFlag () =
  begin match !startClause with
  | Some cid -> print "Error: flag already set\n"
  | None -> (:=) startClause Some (((fun r -> r.1)) (I.sgnSize ())) end
let rec setEndTcb () =
  begin match !startSemant with
  | Some cid -> print "Error: flag already set\n"
  | None -> (:=) startSemant Some (((fun r -> r.1)) (I.sgnSize ())) end
let rec dumpFlagged file =
  let max = (fun r -> r.1) (I.sgnSize ()) in
  let rec compileSeq cid =
    if cid < max then begin (begin lookup cid; compileSeq (cid + 1) end) end
    else begin () end in
let rec dump' cid =
  begin (:=) out Some (BinIO.openOut file);
  initTuples ();
  compileSeq cid;
  BinIO.closeOut (valOf !out) end in
let rec error msg =
  let rec closeOut () =
    begin match !out with | Some stream -> BinIO.closeOut stream | None -> () end in
begin print (("Error: " ^ msg) ^ "\n"); closeOut () end in
begin match !startClause with
| Some cid -> (begin try dump' cid with | Error msg -> error msg end)
| None -> error "setFlag() has not been called yet\n" end
let rec dumpSymTable (name1, name2, file) =
  let stream = TextIO.openOut file in
  let Strength nonfixLevel = F.minPrec in
  let rec dumpFixity cid =
    begin match N.getFixity cid with
    | Infix (Strength level, F.Left) -> (level, 1)
    | Infix (Strength level, F.Right) -> (level, 2)
    | Infix (Strength level, F.None) -> (level, 3)
    | F.Nonfix -> (nonfixLevel, 0) end in
  let rec dumpEntry cid =
    begin match ((Table.lookup symTable cid), (dumpFixity cid)) with
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
    | (None, _) -> () end in
  let rec dumpTable (cid1, cid2) =
    if cid1 <= cid2
    then begin (begin dumpEntry cid1; dumpTable ((cid1 + 1), cid2) end) end
    else begin () end in
let rec error msg = print (("Error: " ^ msg) ^ "\n") in
begin (begin match ((N.constLookup (valOf (N.stringToQid name1))),
                     (N.constLookup (valOf (N.stringToQid name2))))
             with
       | (Some cid1, Some cid2) -> dumpTable (cid1, cid2)
       | (None, _) -> error (name1 ^ " undefined")
       | (_, None) -> error (name2 ^ " undefined") end);
  TextIO.flushOut stream; TextIO.closeOut stream end
let rec sort cmp l =
  let rec split l =
    let rec s arg__20 arg__21 arg__22 =
      begin match (arg__20, arg__21, arg__22) with
      | (a1, a2, []) -> (a1, a2)
      | (a1, a2, h::t) -> s a2 (h :: a1) t end in
  s [] [] l in
let rec merge arg__23 arg__24 =
  begin match (arg__23, arg__24) with
  | (a, []) -> a
  | ([], b) -> b
  | ((a::ta as aa), (b::tb as bb)) ->
      (begin match cmp (a, b) with
       | EQUAL -> (::) (a :: b) merge ta tb
       | LESS -> (::) a merge ta bb
       | GREATER -> (::) b merge aa tb end) end in
let rec ms =
  begin function
  | [] -> []
  | s::[] -> [s]
  | a::b::[] -> merge [a] [b]
  | ll -> let (a, b) = split ll in merge (ms a) (ms b) end in
ms l
let rec sortedKeys t =
  let r = ref [] in
  let _ = IHT.app (begin function | x -> (!) ((::) (r := x)) r end) t in
  sort Int.compare (map (fun r -> r.1) !r)
exception noPriorEntry of string 
exception Error of string 
let rec valOfE arg__25 arg__26 =
  begin match (arg__25, arg__26) with
  | (e, None) -> raise e
  | (e, Some x) -> x end
let counter = ref 0
let rec isShadowedBy cid =
  let name = I.conDecName (I.sgnLookup cid) in
  let currentcid = valOfE (noPriorEntry name) (SHT.lookup shadowTable name) in
  (name, (if currentcid <> cid then begin Some currentcid end
    else begin None end))
let rec isShadowing () =
  let _ = SHT.clear shadowTable in
  let changes = ref false in
  let rec processDep rcid cid =
    let rec handleProblem (currentcid, name) =
      begin match Table.lookup replaceTable cid with
      | Some _ -> ()
      | _ ->
          let replacement =
            Option.map (I.conDecName o I.sgnLookup)
              (Table.lookup imitatesTable cid) in
          (((begin match replacement with
             | None ->
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
                 (* print ("DX planning to subtly rename " ^ Int.toString cid ^ " to " ^ x ^ "\n");  *)) end))
          (* Option.mapPartial
                                                    (fn x => (case isShadowedBy x of
                                                    (_, SOME _) => NONE
                                                      | (x, NONE) => SOME x)) *)
          (* XXX worrying - jcreed 7/05 *)) end in
  let (name, sb) = isShadowedBy cid in
  begin match sb with
  | Some currentcid ->
      ((if ((<) cid valOf !startSemant) || ((>=) cid valOf !startClause)
        then begin handleProblem (currentcid, name) end
      else begin
        (let newname = (^) "shadowed_" Int.toString !counter in
         ((begin I.rename (cid, newname);
           SHT.insert shadowTable (newname, cid);
           ((!) ((:=) counter) counter) + 1;
           changes := true end)
        (* print ("DX renaming " ^ Int.toString cid ^ " to " ^ newname ^ "\n"); *))) end)
    (* problematic shadowing *)(* nonproblematic shadowing - change its name *))
    | None -> () end in
let rec processCid cid =
let name = I.conDecName (I.sgnLookup cid) in
((begin (begin try
                 List.app (processDep cid)
                   (sortedKeys (valOf (IHT.lookup depTable cid)))
         with | Option -> () end);
  SHT.insert shadowTable (name, cid) end)
(* val _ = print ("DX processing cid " ^ Int.toString cid ^ " which has name [" ^ name ^ "].\n") *)) in
((begin (begin try List.app processCid (sortedKeys recordTable)
       with
       | noPriorEntry s as e ->
           (begin print (("Error: No Prior Entry: " ^ s) ^ "\n"); raise e end) end);
!changes end)
(* val _ = print "clearing table...\n" *))
let rec is_def cid = begin try begin I.constDef cid; true end
  with | Match -> false end
let rec fixityDec cid =
  begin match N.getFixity cid with
  | Infix _ as f ->
      ((^) ((F.toString f) ^ " ") I.conDecName (I.sgnLookup cid)) ^ ".\n"
  | _ -> "" end
let rec record_once k cid =
  begin match IHT.insertShadow recordTable (cid, ()) with
  | None -> ((k cid)
      (* print("DX Recording " ^ Int.toString cid ^ ".\n") ; *))
  | Some _ -> () end
let rec recordDependency (x, y) =
  let table =
    begin match IHT.lookup depTable x with
    | Some y -> y
    | None ->
        let t = IHT.new_ 32 in (begin IHT.insert depTable (x, t); t end) end in
((IHT.insert table (y, ()))
  (*        val msg = "DX dep " ^ Int.toString x ^ " on " ^ Int.toString y ^ "\n" *))
open I
let rec etaReduce arg__27 arg__28 =
  begin match (arg__27, arg__28) with
  | (n, Root (h, sp)) -> if etaReduceSpine n sp then begin Some h end
      else begin None end
  | (n, Lam (_, t)) -> etaReduce (n + 1) t | (_, _) -> None end
let rec etaReduceSpine arg__29 arg__30 =
  begin match (arg__29, arg__30) with
  | (n, App (fst, sp)) ->
      (begin match etaReduce 0 fst with
       | Some (BVar n') -> (n = n') && (etaReduceSpine (n - 1) sp)
       | _ -> false end)
  | (n, Nil) -> true | (n, _) -> false end
let rec checkTrivial cid =
  begin match sgnLookup cid with
  | AbbrevDef (_, _, _, m_, v_, _) ->
      (begin match etaReduce 0 m_ with
       | Some (Const cid') ->
           (begin print
                    (((^) (((^) "DX inserting " Int.toString cid') ^ " = ")
                        Int.toString cid)
                       ^ "\n");
            Table.insert imitatesTable (cid', cid) end)
      | _ -> () end)
  | _ -> () end
let rec travExp arg__31 arg__32 =
  begin match (arg__31, arg__32) with
  | (cid, Uni _) -> ()
  | (cid, Pi ((d_, _), b_)) -> (begin travDec cid d_; travExp cid b_ end)
  | (cid, Root (h_, s_)) -> (begin travHead cid h_; travSpine cid s_ end)
  | (cid, Redex (m_, s_)) -> (begin travExp cid m_; travSpine cid s_ end)
| (cid, Lam (d_, m_)) -> (begin travDec cid d_; travExp cid m_ end)
| (cid, _) -> () end
let rec travDec arg__33 arg__34 =
  begin match (arg__33, arg__34) with
  | (cid, Dec (_, a_)) -> travExp cid a_
  | (cid, BDec (_, (c, _))) ->
      (begin recordDependency (cid, c); traverse c end) end
let rec travSpine arg__35 arg__36 =
  begin match (arg__35, arg__36) with
  | (cid, Nil) -> ()
  | (cid, App (m_, s_)) -> (begin travExp cid m_; travSpine cid s_ end)
  | (cid, _) -> () end
let rec travHead cid h =
  Option.map
    (begin function | n -> (begin recordDependency (cid, n); traverse n end) end)
  (headCID h)
let rec traverseDescendants' arg__37 arg__38 =
  begin match (arg__37, arg__38) with
  | (cid, ConDec (_, _, _, _, v_, _)) -> travExp cid v_
  | (cid, ConDef (_, _, _, m_, v_, _, _)) ->
      (begin travExp cid m_; travExp cid v_ end)
  | (cid, AbbrevDef (_, _, _, m_, v_, _)) ->
      (begin travExp cid m_; travExp cid v_ end)
  | (cid, _) -> () end
let rec traverseDescendants cid = traverseDescendants' cid (I.sgnLookup cid)
let rec traverse cid =
  let name = conDecName (sgnLookup cid) in
  ((record_once traverseDescendants cid)
    (* val message = "DX Traversing cid = " ^ Int.toString cid ^ " name = " ^ name ^ "\n" *))
let rec initForText () =
  begin startClause := None;
  startSemant := None;
  Table.clear depTable;
  Table.clear recordTable;
  Table.clear imitatesTable;
  Table.clear replaceTable end
exception InfixWithImplicitArgs 
let rec appRange f min max =
  if min < max then begin (begin f min; appRange f (min + 1) max end) end
  else begin () end
let rec dumpAll (max, first, outputSemant, outputChecker) =
  let streamSemant = TextIO.openOut outputSemant in
  let streamChecker = TextIO.openOut outputChecker in
  let streamTcb = TextIO.openOut "dumptcb" in
  let rec waitUntilFalse f = if f () then begin waitUntilFalse f end
    else begin () end in
  let rec outputCid cid =
    let s = (Print.conDecToString (I.sgnLookup cid)) ^ "\n" in
    let s' =
      if ((>=) cid valOf !startClause) && (is_def cid)
      then begin (if isClause cid then begin "%clause " ^ s end
        else begin s end) end
      else begin s end in
  let stream = ((if (<) cid valOf !startSemant then begin streamTcb end
    else begin if (>=) cid valOf !startClause then begin streamChecker end
      else begin streamSemant end end)
  (* DX *)) in
TextIO.output (stream, (s' ^ (fixityDec cid)))(* DX *)
(* if cid < (valOf(!startSemant)) then () else *) in
((begin appRange checkTrivial 0 max;
appRange traverse first max;
appRange (begin function | cid -> Table.insert recordTable (cid, ()) end)
0
(valOf !startSemant); waitUntilFalse isShadowing;
Table.app IntSyn.rename replaceTable;
List.app outputCid (sortedKeys recordTable); TextIO.closeOut streamSemant;
TextIO.closeOut streamChecker; TextIO.closeOut streamTcb end)
(* DX *)(* DX *))
let rec dumpText (outputSemant, outputChecker) =
  let max = (fun r -> r.1) (I.sgnSize ()) in
  let rec correctFixities cid =
    if cid < max
    then
      begin (begin (let fixity = N.getFixity cid in
                    let imp = I.constImp cid in
                    let name = I.conDecName (I.sgnLookup cid) in
                    let inSemant =
                      ((>=) cid valOf !startSemant) &&
                        ((<) cid valOf !startClause) in
                    let makeNonfix =
                      begin match (fixity, imp, inSemant) with
                      | (Infix _, _, true) -> ((true)
                          (*print ("DX setting nonfix " ^ Int.toString cid ^ "\n"); *))
                      | (Infix _, 0, false) -> false
                      | (Infix _, _, false) -> raise InfixWithImplicitArgs
                      | (_, _, _) -> false end in
                    ((if makeNonfix
                      then begin N.installFixity (cid, F.Nonfix) end
                      else begin () end)
                      (* val _ = case fixity of F.Infix _ => print ("DX Infix " ^ Int.toString cid ^ " " ^ name ^ " " ^ Int.toString imp ^ " \n") | _ => () *)));
    correctFixities (cid + 1) end) end
  else begin () end in
let _ = correctFixities 0 in
let rec error msg = print (("Error: " ^ msg) ^ "\n") in
((begin match !startClause with
| Some cid ->
    (begin try dumpAll (max, cid, outputSemant, outputChecker)
     with | Error msg -> error msg end)
| None -> error "setFlag() has not been called yet\n" end)
(* val _ = print ("DX startSemant = " ^ Int.toString(valOf(!startSemant)) ^ "\n") *)
(* val _ = print ("DX startClause = " ^ Int.toString(valOf(!startClause)) ^ "\n") *))
let init = init
let initForText = initForText
let dump = dump
let dumpText = dumpText
let setFlag = setFlag
let setEndTcb = setEndTcb
let dumpFlagged = dumpFlagged
let dumpSymTable = dumpSymTable end



module Flit =
  (Flit)(struct
                module Global = Global
                module Word = Word32
                module Pack = PackWord32Little
                module IntSyn = IntSyn
                module Whnf = Whnf
                module Print = Print
                module Names = Names
                module Index = Index
                module Table = IntRedBlackTree
              end)