module type TABLEINDEX  =
  sig
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    type strategy_ =
      | Variant 
      | Subsumption 
    val strategy : strategy_ ref
    val termDepth : int option ref
    val ctxDepth : int option ref
    val ctxLength : int option ref
    val strengthen : bool ref
    val query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ * IntSyn.sub_ *
        (CompSyn.pskeleton -> unit)) option ref
    type answState =
      | New 
      | Repeated 
    val table :
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) * answer) list ref
    val noAnswers :
      ((IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) * answer) list -> bool
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) ->
        ((IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) * answer) list option
    val answerCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ * IntSyn.sub_ *
        CompSyn.pskeleton) -> answState
    val reset : unit -> unit
    val printTable : unit -> unit
    val printTableEntries : unit -> unit
    val updateTable : unit -> bool
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list
    val lookup : answer -> int
  end


module TableIndex(TableIndex:sig
                               module Global : GLOBAL
                               module Queue : QUEUE
                               module Subordinate : SUBORDINATE
                               module Conv : CONV
                               module Unify : UNIFY
                               module AbstractTabled : ABSTRACTTABLED
                               module Whnf : WHNF
                               module Print : PRINT
                               module CPrint : CPRINT
                               module Names : NAMES
                               module TypeCheck : TYPECHECK
                             end) : TABLEINDEX =
  struct
    module Conv = Conv
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    type nonrec entry =
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) * answer)
    type nonrec entries = entry list
    type nonrec index = entry list
    type answState =
      | New 
      | Repeated 
    type strategy_ =
      | Variant 
      | Subsumption 
    let added = ref false
    let strategy = ref Variant
    let termDepth = (ref None : int option ref)
    let ctxDepth = (ref None : int option ref)
    let ctxLength = (ref None : int option ref)
    let strengthen = AbstractTabled.strengthen
    let (query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.exp_ * IntSyn.sub_ *
        (CompSyn.pskeleton -> unit)) option ref)
      = ref None
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    let (table : index ref) = ref []
    let rec concat =
      begin function
      | (I.Null, g'_) -> g'_
      | (Decl (g_, d_), g'_) -> I.Decl ((concat (g_, g'_)), d_) end
    let rec reverse =
      begin function
      | (I.Null, g'_) -> g'_
      | (Decl (g_, d_), g'_) -> reverse (g_, (I.Decl (g'_, d_))) end
  let rec printTable () =
    let rec proofTerms =
      begin function
      | (g_, d_, u_, []) -> print ""
      | (g_, d_, u_, ((d'_, s'), _)::s_) ->
          (((begin (begin try
                            print
                              (Print.expToString
                                 (I.Null,
                                   (A.raiseType
                                      ((Names.ctxName d'_),
                                        (I.EClo
                                           ((A.raiseType
                                               ((Names.ctxName g_), u_)), s'))))))
                    with | _ -> print "EXCEPTION" end);
          print ", \n\t"; proofTerms (g_, d_, u_, s_) end))
      (* (print (Print.expToString (I.Null,  *)(*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
      (* do not print pskeletons *)) end in
let rec printT =
  begin function
  | [] -> ()
  | ((k, g_, d_, u_), { solutions = s_; lookup = i; lookup = i })::t_ ->
      (begin match s_ with
       | [] ->
           (begin printT t_;
            print
              ((Print.expToString
                  (I.Null, (A.raiseType ((concat (g_, d_)), u_))))
                 ^ ", NONE\n") end)
      | a::answ ->
          (begin printT t_;
           print
             ((Print.expToString
                 (I.Null, (A.raiseType ((concat (g_, d_)), u_))))
                ^ ", [\n\t");
           proofTerms (g_, d_, u_, (rev s_));
           print (((^) " ] -- lookup : " Int.toString i) ^ "\n\n") end) end) end in
begin print "Table: \n";
printT !table;
print "End Table \n";
print
(((^) "Number of table entries   : " Int.toString (length !table)) ^ "\n") end
let rec printTableEntries () =
  let rec printT =
    begin function
    | [] -> ()
    | ((k, g_, d_, u_), { solutions = s_; lookup = i; lookup = i })::t_ ->
        (begin printT t_;
         print
           ((((Print.expToString
                 (I.Null, (A.raiseType ((concat (g_, d_)), u_))))
                ^ "\n Access Counter : ")
               ^ (Int.toString !k))
              ^ " \n") end) end in
begin print "TableEntries: \n";
printT !table;
print "End TableEntries \n";
print
  (((^) "Number of table entries   : " Int.toString (length !table)) ^ "\n") end
let rec lengthSpine =
  begin function | I.Nil -> 0 | SClo (s_, s') -> (+) 1 lengthSpine s_ end
let rec exceedsTermDepth i =
  begin match !termDepth with | None -> false | Some n -> i > n end
let rec exceedsCtxDepth i =
  begin match !ctxDepth with
  | None -> false
  | Some n ->
      (begin print
               (((^) (((^) "\n exceedsCtxDepth " Int.toString i) ^ " > ")
                   Int.toString n)
                  ^ " ? ");
       i > n end) end
let rec exceedsCtxLength i =
  begin match !ctxLength with | None -> false | Some n -> i > n end
let rec max (x, y) = if x > y then begin x end else begin y end
let rec oroption =
  begin function
  | (None, None, None) -> false
  | (Some k, _, _) -> true
  | (_, Some n, _) -> true
  | (_, _, Some n) -> true end
let rec abstractionSet () = oroption (!termDepth, !ctxDepth, !ctxLength)
let rec exceeds (u_) = countDecl (0, 0, u_)
let rec countDecl =
  begin function
  | (ctrType, ctrLength, Pi ((d_, _), v_)) ->
      let ctrType' = countDec (0, d_) in
      ((if ctrType' > ctrType
        then begin countDecl (ctrType', (ctrLength + 1), v_) end
        else begin countDecl (ctrType, (ctrLength + 1), v_) end)
  (*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *))
  | (ctrType, ctrLength, u_) ->
      let ctrTerm = count (0, u_) in
      (((exceedsCtxDepth ctrType) ||
          ((exceedsCtxLength ctrLength) || (exceedsTermDepth (count (0, u_)))))
        (*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)) end
let rec countDec =
  begin function
  | (ctr, Dec (_, u_)) -> count (ctr, u_)
  | (ctr, BDec (_, s)) -> 0 end
let rec count =
  begin function
  | (ctr, (Uni (l_) as u_)) -> ctr
  | (ctr, Pi ((d_, _), v_)) ->
      let ctrTerm = count (ctr, v_) in
      let ctrType = countDec (ctr, d_) in ((max (ctrType, ctrTerm))
        (*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)
        (* to revise ?*))
  | (ctr, Root (f_, s_)) ->
      let ctrDepth = countSpine (1, s_) in (((ctrDepth + 1) + ctr)
        (*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
        (*         (ctrLength + ctr) *))
  | (ctr, Redex (u_, s_)) ->
      let ctrDepth = count (0, u_) in
      let ctrDepth' = countSpine (ctrDepth, s_) in
      (((max (ctrDepth', ctrDepth)) + ctr)
        (*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*))
  | (ctr, Lam (d_, u_)) -> count ((ctr + 1), u_)
  | (ctr, (EVar _ as x_)) -> ctr
  | (ctr, EClo (e_, s)) -> count (ctr, e_)
  | (ctr, (FgnExp (cs, ops) as f_)) -> ctr end(* shouldn't happen *)
(* shouldn't happen *)
let rec countSpine =
  begin function
  | (ctrDepth, I.Nil) -> ctrDepth
  | (ctr, SClo (s_, s')) -> countSpine (ctr, s_)
  | (ctrDepth, App (u_, s_)) ->
      let ctrDepth' = count (0, u_) in
      countSpine ((max (ctrDepth', ctrDepth)), s_) end(* ? *)
let rec reinstSub =
  begin function
  | (g_, I.Null, s) -> s
  | (g_, Decl (d_, Dec (_, a_)), s) ->
      let x_ = I.newEVar (I.Null, a_) in
      I.Dot ((I.Exp x_), (reinstSub (g_, d_, s))) end
let rec variant (us_, us'_) = Conv.conv (us_, us'_)
let rec subsumes ((g_, d_, u_), (g'_, d'_, u'_)) =
  let Upi = A.raiseType (g_, u_) in
  let Upi' = A.raiseType (g'_, u'_) in
  let s' = reinstSub (g'_, d'_, I.id) in
  CSManager.trail
    (begin function | () -> Unify.unifiable (d_, (Upi', s'), (Upi, I.id)) end)
let rec equalSub =
  begin function
  | (Shift k, Shift k') -> k = k'
  | (Dot (f_, s_), Dot (f'_, s'_)) ->
      (equalFront (f_, f'_)) && (equalSub (s_, s'_))
  | (Dot (f_, s_), Shift k) -> false
  | (Shift k, Dot (f_, s_)) -> false end
let rec equalFront =
  begin function
  | (Idx n, Idx n') -> n = n'
  | (Exp (u_), Exp (v_)) -> Conv.conv ((u_, I.id), (v_, I.id))
  | (I.Undef, I.Undef) -> true end
let rec equalSub1 (Dot (ms, s), Dot (ms', s')) = equalSub (s, s')
let rec equalCtx =
  begin function
  | (I.Null, I.Null) -> true
  | (Decl (Dk, Dec (_, a_)), Decl (d1_, Dec (_, a1_))) ->
      (Conv.conv ((a_, I.id), (a1_, I.id))) && (equalCtx (Dk, d1_)) end
let rec callCheckVariant (g_, d_, u_) =
  let Upi = A.raiseType ((concat (g_, d_)), u_) in
  let rec lookup =
    begin function
    | ((g_, d_, u_), []) ->
        (((begin (table :=
                    (((ref 1), g_, d_, u_), { solutions = []; lookup = 0 }))
                   :: !table;
           if !Global.chatter >= 5
           then
             begin (begin print "\n \n Added ";
                    print
                      ((Print.expToString (I.Null, Upi)) ^ "\n to Table \n") end) end
        else begin () end;
    added := true;
    if abstractionSet ()
    then
      begin (((if exceeds (A.raiseType (g_, u_))
               then
                 begin (begin if !Global.chatter >= 5
                              then
                                begin print
                                        (((^) "\n term " Print.expToString
                                            (I.Null, Upi))
                                           ^ " exceeds depth or length \n") end
                        else begin () end;
               Some [] end) end
    else begin None end))
  (* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *)) end
else begin None end end))
(* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *))
| ((g_, d_, u_), (((k, g'_, d'_, u'_), answ) as h_)::t_) ->
    if
      variant ((Upi, I.id), ((A.raiseType ((concat (g'_, d'_)), u'_)), I.id))
    then
      begin (begin ((!) ((:=) k) k) + 1;
             if !Global.chatter >= 5
             then
               begin print
                       (((^) "call " Print.expToString (I.Null, Upi)) ^
                          " found in table \n ") end
             else begin () end;
    Some [((g'_, d'_, u'_), answ)] end) end
else begin lookup ((g_, d_, u_), t_) end end in
lookup ((g_, d_, u_), !table)
let rec callCheckSubsumes (g_, d_, u_) =
  let rec lookup =
    begin function
    | ((g_, d_, u_), []) ->
        (begin (table :=
                  (((ref 1), g_, d_, u_), { solutions = []; lookup = 0 }))
                 :: !table;
         if !Global.chatter >= 5
         then
           begin print
                   (((^) "Added " Print.expToString
                       (I.Null, (A.raiseType ((concat (g_, d_)), u_))))
                      ^ " to Table \n") end
         else begin () end;
    added := true;
    if exceeds (A.raiseType (g_, u_))
    then
      begin (begin if !Global.chatter >= 4
                   then
                     begin print
                             (((^) "\n term " Print.expToString
                                 (I.Null,
                                   (A.raiseType ((concat (g_, d_)), u_))))
                                ^ " exceeds depth or length \n") end
             else begin () end;
    Some [] end) end
  else begin None end end)
| ((g_, d_, u_), ((k, g'_, d'_, u'_), answ)::t_) ->
    if subsumes ((g_, d_, u_), (g'_, d'_, u'_))
    then
      begin (begin if !Global.chatter >= 5
                   then
                     begin print
                             (((^) "call " Print.expToString
                                 (I.Null,
                                   (A.raiseType ((concat (g_, d_)), u_))))
                                ^ "found in table \n ") end
             else begin () end;
    ((!) ((:=) k) k) + 1;
    Some [((g'_, d'_, u'_), answ)] end) end
else begin lookup ((g_, d_, u_), t_) end end in
lookup ((g_, d_, u_), !table)
let rec member =
  begin function
  | ((Dk, sk), []) -> false
  | ((Dk, sk), ((d1_, s1), _)::s_) ->
      if (equalSub (sk, s1)) && (equalCtx (Dk, d1_)) then begin true end
      else begin member ((Dk, sk), s_) end end(* do we really need to compare Gus and Gs1 ?  *)
let rec answCheckVariant (g_, d_, u_, s, o_) =
  let Upi = A.raiseType ((concat (g_, d_)), u_) in
  let _ =
    if !Global.chatter >= 5
    then
      begin (begin print "\n AnswCheckInsert: ";
             print
               ((Print.expToString
                   (I.Null, (I.EClo ((A.raiseType (g_, u_)), s))))
                  ^ "\n");
             print "\n Table Index : ";
             print ((Print.expToString (I.Null, Upi)) ^ "\n") end) end
    else begin () end in
let rec lookup arg__0 arg__1 arg__2 =
  begin match (arg__0, arg__1, arg__2) with
  | ((g_, d_, u_, s), [], t_) ->
      (begin print
               ((Print.expToString
                   (I.Null, (I.EClo ((A.raiseType (g_, u_)), s))))
                  ^ " call should always be already in the table !\n");
       Repeated end)
  | ((g_, d_, u_, s),
     (((k, g'_, d'_, u'_), { solutions = s_; lookup = i; lookup = i }) as h_)::t_,
     t'_) ->
      if
        variant
          ((Upi, I.id), ((A.raiseType ((concat (g'_, d'_)), u'_)), I.id))
      then
        begin let (Dk, sk) = A.abstractAnswSub s in
              (((if member ((Dk, sk), s_) then begin Repeated end
                else begin
                  (begin (table := (rev t'_)) @
                           (((k, g'_, d'_, u'_),
                              {
                                solutions = (((Dk, sk), o_) :: s_);
                                lookup = i
                              }) :: t_);
                   if !Global.chatter >= 5
                   then
                     begin (begin print "\n Add solution  -- ";
                            print
                              (Print.expToString
                                 (I.Null,
                                   (I.EClo ((A.raiseType (g'_, u'_)), s))));
                            print "\n solution added  -- ";
                            print
                              (Print.expToString
                                 (I.Null,
                                   (A.raiseType
                                      ((Names.ctxName Dk),
                                        (I.EClo
                                           ((A.raiseType (g'_, u'_)), sk)))))) end) end
                  else begin () end;
        New end) end))
  (* answer check *)) end
else begin lookup (g_, d_, u_, s) t_ (h_ :: t'_) end end(* cannot happen ! *) in
lookup (g_, d_, u_, s) !table []
let rec memberSubsumes =
  begin function
  | ((g_, d_, u_, s), (g'_, u'_, [])) -> false
  | ((g_, d_, u_, s), (g'_, u'_, ((d1_, s1), _)::a_)) ->
      let Upi = A.raiseType (g_, u_) in
      let Upi' = A.raiseType (g'_, u'_) in
      let s1' = reinstSub (g'_, d1_, I.id) in
      let Vpis = ((I.EClo (Upi', s1)), s1') in
      let b =
        CSManager.trail
          (begin function | () -> Unify.unifiable (d_, (Upi, s), Vpis) end) in
      ((if b
        then
          begin (begin if !Global.chatter >= 5
                       then
                         begin print "\n answer in table subsumes answer \n " end
                 else begin () end;
        true end) end
        else begin memberSubsumes ((g_, d_, u_, s), (g'_, u'_, a_)) end)
  (* assume G' and G are the same for now *)) end
let rec shift =
  begin function | (0, s) -> s | (n, s) -> shift ((n - 1), (I.dot1 s)) end
let rec answCheckSubsumes (g_, d_, u_, s, o_) =
  let Upi = A.raiseType (g_, u_) in
  let _ =
    if !Global.chatter >= 4
    then
      begin (begin print "\n AnswCheckInsert (subsumes): ";
             print ((Print.expToString (I.Null, (I.EClo (Upi, s)))) ^ "\n") end) end
    else begin () end in
let rec lookup =
  begin function
  | ((g_, d_, u_, s), [], t_) ->
      (begin print
               ((Print.expToString ((concat (g_, d_)), (I.EClo (u_, s)))) ^
                  " call should always be already in the table !\n");
       Repeated end)
  | ((g_, d_, u_, s),
     ((k, g'_, d'_, u'_), { solutions = a_; lookup = i; lookup = i })::t_,
     t'_) ->
      if subsumes ((g_, d_, u_), (g'_, d'_, u'_))
      then
        begin let (Dk, sk) = A.abstractAnswSub s in
              (if memberSubsumes ((g_, Dk, u_, sk), (g'_, u'_, a_))
               then begin Repeated end
                else begin
                  (let s' = reinstSub (g'_, d'_, I.id) in
                   let _ =
                     if !Global.chatter >= 4
                     then
                       begin (begin print
                                      "\n new answer to be added to Index \n";
                              print
                                ((Print.expToString
                                    (I.Null,
                                      (A.raiseType ((concat (g'_, d'_)), u'_))))
                                   ^ "\n");
                              print "\n answer added \n";
                              print
                                ((Print.expToString
                                    (I.Null,
                                      (A.raiseType
                                         (Dk,
                                           (I.EClo
                                              ((A.raiseType (g_, u_)), sk))))))
                                   ^ "\n") end) end
                     else begin () end in
              let _ =
                if
                  Unify.unifiable
                    (Dk, ((A.raiseType (g_, u_)), sk),
                      ((A.raiseType (g'_, u'_)), s'))
                then
                  begin (if !Global.chatter >= 4
                         then
                           begin (begin print
                                          "\n1 unification successful !\n";
                                  print
                                    ((Print.expToString
                                        (I.Null,
                                          (A.raiseType
                                             (Dk,
                                               (I.EClo
                                                  ((A.raiseType (g'_, u'_)),
                                                    s'))))))
                                       ^ "\n") end) end
                else begin () end) end
        else begin print "\n1 unification failed! -- should never happen ?" end in
let (Dk', sk') = A.abstractAnsw (Dk, s') in
let rs = reinstSub (g'_, Dk', I.id) in
((begin (((begin match !query with
           | None -> ()
           | Some (g1_, d1_, u1_, s1, sc1) ->
               (begin if !Global.chatter >= 4
                      then
                        begin (begin print "Generate answers for: ";
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (I.EClo ((A.raiseType (g1_, u1_)), s1))))
                                    ^ " \n");
                               print "Answer in table: ";
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (A.raiseType
                                          (Dk,
                                            (I.EClo
                                               ((A.raiseType (g'_, u'_)), s'))))))
                                    ^ " : \n");
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (I.EClo
                                          ((A.raiseType
                                              (Dk,
                                                (I.EClo
                                                   ((A.raiseType (g'_, u'_)),
                                                     sk')))), rs))))
                                    ^ " : \n") end) end
               else begin () end;
  ((if subsumes ((g1_, d1_, u1_), (g'_, d'_, u'_))
    then
      begin CSManager.trail
              (begin function
               | () ->
                   if
                     Unify.unifiable
                       (d1_, ((A.raiseType (g1_, u1_)), s1),
                         ((I.EClo ((A.raiseType (g'_, u'_)), sk')), rs))
                   then
                     begin let w =
                             if !strengthen
                             then
                               begin Subordinate.weaken
                                       (I.Null,
                                         (IntSyn.targetFam (I.EClo (u1_, s1)))) end
                             else begin I.id end in
                 ((sc1 o_)
                   (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)) end
              else begin () end end) end
  else begin () end)
(* original query is an instance of the entry we are adding answ to *)) end) end))
(* nothing to do *));
table :=
  ((rev t'_) @
     (((k, g'_, d'_, u'_),
        { solutions = (((Dk', sk'), o_) :: a_); lookup = i }) :: t_));
if !Global.chatter >= 5
then
  begin (begin print "\n \n solution (original) was: \n";
         print
           ((Print.expToString (I.Null, (I.EClo ((A.raiseType (g_, u_)), s))))
              ^ "\n");
         print "\n \n solution (deref) was: \n";
         print
           (((Print.expToString
                (I.Null,
                  (A.raiseType (Dk, (I.EClo ((A.raiseType (g_, u_)), sk))))))
               ^ "\n")
           (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *));
         print "\n solution added  --- ";
         print
           ((Print.expToString
               (I.Null,
                 (A.raiseType (Dk', (I.EClo ((A.raiseType (g'_, u'_)), s'))))))
              ^ "\n");
         print "\n solution added (dereferenced) --- ";
         print
           ((Print.expToString
               (I.Null,
                 (A.raiseType (Dk', (I.EClo ((A.raiseType (g'_, u'_)), sk'))))))
              ^ "\n") end) end else begin () end; New end)
(*  higher-order matching *)(* reinstantiate us' *))) end) end
else begin
  lookup
    ((g_, d_, u_, s), t_,
      (((k, g'_, d'_, u'_), { solutions = a_; lookup = i }) :: t'_)) end end
(* cannot happen ! *) in
lookup ((g_, d_, u_, s), !table, [])
let rec reset () = table := []
let rec solutions { solutions = s_; lookup = i; lookup = i } = s_
let rec lookup { solutions = s_; lookup = i; lookup = i } = i
let rec noAnswers =
  begin function
  | [] -> true
  | (((g'_, d'_, u'_), answ) as h_)::l'_ ->
      (begin match List.take ((solutions answ), (lookup answ)) with
       | [] -> noAnswers l'_
       | l_ -> false end) end
let rec callCheck (g_, d_, u_) =
  begin match !strategy with
  | Variant -> callCheckVariant (g_, d_, u_)
  | Subsumption -> callCheckSubsumes (g_, d_, u_) end
let rec answCheck (g_, d_, u_, s, o_) =
  begin match !strategy with
  | Variant -> answCheckVariant (g_, d_, u_, s, o_)
  | Subsumption -> answCheckSubsumes (g_, d_, u_, s, o_) end
let rec updateTable () =
  let rec update arg__3 arg__4 arg__5 =
    begin match (arg__3, arg__4, arg__5) with
    | ([], t_, Flag) -> (Flag, t_)
    | (((k, g_, d_, u_), { solutions = s_; lookup = i; lookup = i })::t_,
       t'_, Flag) ->
        let l = length s_ in
        ((if l = i
          then
            begin update t_
                    (((k, g_, d_, u_),
                       { solutions = s_; lookup = (List.length s_) }) :: t'_)
                    Flag end
          else begin
            update t_
              (((k, g_, d_, u_),
                 { solutions = s_; lookup = (List.length s_) }) :: t'_) true end)
    (* no new solutions were added in the previous stage *)
    (* new solutions were added *)) end in
let (Flag, t_) = update !table [] false in
let r = Flag || !added in ((begin added := false; (:=) table rev t_; r end)
(* in each stage incrementally increase termDepth *)
(*          termDepth := (!termDepth +1); *))
let table = table
let solutions = solutions
let lookup = lookup
let noAnswers = noAnswers
let reset = reset
let printTable = printTable
let printTableEntries = printTableEntries
let callCheck = callCheck
let answerCheck = answCheck
let updateTable = updateTable end
