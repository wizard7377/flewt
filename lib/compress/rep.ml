
module Rep =
  struct
    module I = IntSyn
    module S = Syntax
    let rec defSize x =
      match x with | DEF_TERM y -> S.size_term y | DEF_TYPE y -> S.size_tp y
    let rec cidSize cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, _, I.Type) ->
          S.size_tp (S.typeOf (Sgn.classifier cid))
      | ConDec (_, _, _, _, _, I.Kind) ->
          S.size_knd (S.kindOf (Sgn.classifier cid))
      | ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.def cid)
      | AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.def cid)
      | _ -> 0
    let rec o_cidSize cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, _, I.Type) ->
          S.size_tp (S.typeOf (Sgn.o_classifier cid))
      | ConDec (_, _, _, _, _, I.Kind) ->
          S.size_knd (S.kindOf (Sgn.o_classifier cid))
      | ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.o_def cid)
      | AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.o_def cid)
      | _ -> 0
    open SMLofNJ.Cont
    (* val l : (Syntax.term * Syntax.tp) list ref = ref [] *)
    let (k : Reductio.eq_c option ref) = ref NONE
    exception Crap 
    let rec sanityCheck cid =
      try
        ((match I.sgnLookup cid with
          | ConDec (_, _, _, _, _, I.Type) ->
              Reductio.check_plusconst_type (Sgn.typeOf (Sgn.classifier cid))
          | ConDec (_, _, _, _, _, I.Kind) ->
              Reductio.check_kind ([], (Sgn.kindOf (Sgn.classifier cid)))
          | ConDef (_, _, _, _, _, I.Type, _) ->
              let DEF_TERM y = Sgn.def cid in
              let tclass z = Sgn.classifier cid in
              ((Reductio.check ([], y, z))
                (*				     l := (y,z):: !l; *))
          | ConDef (_, _, _, _, _, I.Kind, _) ->
              let DEF_TYPE y = Sgn.def cid in
              let kclass z = Sgn.classifier cid in
              Reductio.check_type Reductio.CON_LF ((Syntax.explodeKind z), y)
          | AbbrevDef (_, _, _, _, _, I.Type) ->
              let DEF_TERM y = Sgn.def cid in
              let tclass z = Sgn.classifier cid in
              ((Reductio.check ([], y, z))
                (*				     l := (y,z):: !l; *))
          | AbbrevDef (_, _, _, _, _, I.Kind) ->
              let DEF_TYPE y = Sgn.def cid in
              let kclass z = Sgn.classifier cid in
              Reductio.check_type Reductio.CON_LF ((Syntax.explodeKind z), y)
          | _ -> true__)
        (* we're not checking block declarations or anything else like that *))
      with | Syntax _ -> (print ((^) "--> " Int.toString cid); raise Match)
    let rec gen_graph n autoCompress =
      let _ = autoCompress n in
      let rec sanity n =
        if n < 0
        then true__
        else
          (sanity (n - 1)) &&
            (if sanityCheck n
             then true__
             else
               (print (("insane: <" ^ (Int.toString n)) ^ ">\n"); raise Crap)) in
      let _ = sanity n in
      let pairs =
        List.tabulate
          ((n + 1), (function | x -> ((o_cidSize x), (cidSize x)))) in
      let s =
        foldl (^) ""
          (map
             (function
              | (x, y) ->
                  ((^) ((Int.toString x) ^ " ") Int.toString y) ^ "\n") pairs) in
      let f = TextIO.openOut "/tmp/graph" in
      let _ = TextIO.output (f, s) in let _ = TextIO.closeOut f in ()
    (* DEBUG  handle Reductio.Matching2 s => (print "doesn'tmatch"; k := SOME s); *)
    (* fun gg n = (Compress.sgnReset(); gen_graph n
	    (fn n => Compress.sgnAutoCompressUpTo n Compress.naiveModes)) *)
    (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)
    open Reductio
  end;;
