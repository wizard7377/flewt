
module type TABLEINDEX  =
  sig
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    type __Strategy =
      | Variant 
      | Subsumption 
    val strategy : __Strategy ref
    val termDepth : int option ref
    val ctxDepth : int option ref
    val ctxLength : int option ref
    val strengthen : bool ref
    val query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub *
        (CompSyn.pskeleton -> unit)) option ref
    type answState =
      | New 
      | Repeated 
    val table :
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list
        ref
    val noAnswers :
      ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list -> bool
    val callCheck :
      IntSyn.dctx ->
        IntSyn.dctx ->
          IntSyn.__Exp ->
            ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list option
    val answerCheck :
      IntSyn.dctx ->
        IntSyn.dctx ->
          IntSyn.__Exp -> IntSyn.__Sub -> CompSyn.pskeleton -> answState
    val reset : unit -> unit
    val printTable : unit -> unit
    val printTableEntries : unit -> unit
    val updateTable : unit -> bool
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list
    val lookup : answer -> int
  end;;




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
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    type nonrec entry =
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer)
    type nonrec entries = entry list
    type nonrec index = entry list
    type answState =
      | New 
      | Repeated 
    type __Strategy =
      | Variant 
      | Subsumption 
    let added = ref false__
    let strategy = ref Variant
    let termDepth = (ref NONE : int option ref)
    let ctxDepth = (ref NONE : int option ref)
    let ctxLength = (ref NONE : int option ref)
    let strengthen = AbstractTabled.strengthen
    let (query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub *
        (CompSyn.pskeleton -> unit)) option ref)
      = ref NONE
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    let (table : index ref) = ref []
    let rec concat __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, __G') -> __G'
      | (Decl (__G, __D), __G') -> I.Decl ((concat (__G, __G')), __D)
    let rec reverse __2__ __3__ =
      match (__2__, __3__) with
      | (I.Null, __G') -> __G'
      | (Decl (__G, __D), __G') -> reverse (__G, (I.Decl (__G', __D)))
    let rec printTable () =
      let rec proofTerms __4__ __5__ __6__ __7__ =
        match (__4__, __5__, __6__, __7__) with
        | (__G, __D, __U, []) -> print ""
        | (__G, __D, __U, ((__D', s'), _)::__S) ->
            ((((try
                  print
                    (Print.expToString
                       (I.Null,
                         (A.raiseType
                            ((Names.ctxName __D'),
                              (I.EClo
                                 ((A.raiseType ((Names.ctxName __G), __U)),
                                   s'))))))
                with | _ -> print "EXCEPTION");
               print ", \n\t";
               proofTerms (__G, __D, __U, __S)))
            (* (print (Print.expToString (I.Null,  *)
            (*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
            (* do not print pskeletons *)) in
      let rec printT =
        function
        | [] -> ()
        | ((k, __G, __D, __U), { solutions = __S; lookup = i; lookup = i })::__T
            ->
            (match __S with
             | [] ->
                 (printT __T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                       ^ ", NONE\n"))
             | a::answ ->
                 (printT __T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                       ^ ", [\n\t");
                  proofTerms (__G, __D, __U, (rev __S));
                  print (((^) " ] -- lookup : " Int.toString i) ^ "\n\n"))) in
      print "Table: \n";
      printT (!table);
      print "End Table \n";
      print
        (((^) "Number of table entries   : " Int.toString (length (!table)))
           ^ "\n")
    let rec printTableEntries () =
      let rec printT =
        function
        | [] -> ()
        | ((k, __G, __D, __U), { solutions = __S; lookup = i; lookup = i })::__T
            ->
            (printT __T;
             print
               ((((Print.expToString
                     (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                    ^ "\n Access Counter : ")
                   ^ (Int.toString (!k)))
                  ^ " \n")) in
      print "TableEntries: \n";
      printT (!table);
      print "End TableEntries \n";
      print
        (((^) "Number of table entries   : " Int.toString (length (!table)))
           ^ "\n")
    let rec lengthSpine =
      function | I.Nil -> 0 | SClo (__S, s') -> (+) 1 lengthSpine __S
    let rec exceedsTermDepth i =
      match !termDepth with | NONE -> false__ | Some n -> i > n
    let rec exceedsCtxDepth i =
      match !ctxDepth with
      | NONE -> false__
      | Some n ->
          (print
             (((^) (((^) "\n exceedsCtxDepth " Int.toString i) ^ " > ")
                 Int.toString n)
                ^ " ? ");
           i > n)
    let rec exceedsCtxLength i =
      match !ctxLength with | NONE -> false__ | Some n -> i > n
    let rec max x y = if x > y then x else y
    let rec oroption __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (NONE, NONE, NONE) -> false__
      | (Some k, _, _) -> true__
      | (_, Some n, _) -> true__
      | (_, _, Some n) -> true__
    let rec abstractionSet () =
      oroption ((!termDepth), (!ctxDepth), (!ctxLength))
    let rec exceeds (__U) = countDecl (0, 0, __U)
    let rec countDecl __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (ctrType, ctrLength, Pi ((__D, _), __V)) ->
          let ctrType' = countDec (0, __D) in
          ((if ctrType' > ctrType
            then countDecl (ctrType', (ctrLength + 1), __V)
            else countDecl (ctrType, (ctrLength + 1), __V))
            (*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *))
      | (ctrType, ctrLength, __U) ->
          let ctrTerm = count (0, __U) in
          (((exceedsCtxDepth ctrType) ||
              ((exceedsCtxLength ctrLength) ||
                 (exceedsTermDepth (count (0, __U)))))
            (*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*))
    let rec countDec __14__ __15__ =
      match (__14__, __15__) with
      | (ctr, Dec (_, __U)) -> count (ctr, __U)
      | (ctr, BDec (_, s)) -> 0
    let rec count __16__ __17__ =
      match (__16__, __17__) with
      | (ctr, (Uni (__L) as U)) -> ctr
      | (ctr, Pi ((__D, _), __V)) ->
          let ctrTerm = count (ctr, __V) in
          let ctrType = countDec (ctr, __D) in ((max (ctrType, ctrTerm))
            (*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)
            (* to revise ?*))
      | (ctr, Root (__F, __S)) ->
          let ctrDepth = countSpine (1, __S) in (((ctrDepth + 1) + ctr)
            (*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
            (*         (ctrLength + ctr) *))
      | (ctr, Redex (__U, __S)) ->
          let ctrDepth = count (0, __U) in
          let ctrDepth' = countSpine (ctrDepth, __S) in
          (((max (ctrDepth', ctrDepth)) + ctr)
            (*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*))
      | (ctr, Lam (__D, __U)) -> count ((ctr + 1), __U)
      | (ctr, (EVar _ as X)) -> ctr
      | (ctr, EClo (__E, s)) -> count (ctr, __E)
      | (ctr, (FgnExp (cs, ops) as F)) -> ctr(* shouldn't happen *)
      (* shouldn't happen *)
    let rec countSpine __18__ __19__ =
      match (__18__, __19__) with
      | (ctrDepth, I.Nil) -> ctrDepth
      | (ctr, SClo (__S, s')) -> countSpine (ctr, __S)
      | (ctrDepth, App (__U, __S)) ->
          let ctrDepth' = count (0, __U) in
          countSpine ((max (ctrDepth', ctrDepth)), __S)(* ? *)
    let rec reinstSub __20__ __21__ __22__ =
      match (__20__, __21__, __22__) with
      | (__G, I.Null, s) -> s
      | (__G, Decl (__D, Dec (_, __A)), s) ->
          let __X = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __X), (reinstSub (__G, __D, s)))
    let rec variant (__Us) (__Us') = Conv.conv (__Us, __Us')
    let rec subsumes (__G, __D, __U) (__G', __D', __U') =
      let Upi = A.raiseType (__G, __U) in
      let Upi' = A.raiseType (__G', __U') in
      let s' = reinstSub (__G', __D', I.id) in
      CSManager.trail
        (fun () -> Unify.unifiable (__D, (Upi', s'), (Upi, I.id)))
    let rec equalSub __23__ __24__ =
      match (__23__, __24__) with
      | (Shift k, Shift k') -> k = k'
      | (Dot (__F, __S), Dot (__F', __S')) ->
          (equalFront (__F, __F')) && (equalSub (__S, __S'))
      | (Dot (__F, __S), Shift k) -> false__
      | (Shift k, Dot (__F, __S)) -> false__
    let rec equalFront __25__ __26__ =
      match (__25__, __26__) with
      | (Idx n, Idx n') -> n = n'
      | (Exp (__U), Exp (__V)) -> Conv.conv ((__U, I.id), (__V, I.id))
      | (I.Undef, I.Undef) -> true__
    let rec equalSub1 (Dot (ms, s)) (Dot (ms', s')) = equalSub (s, s')
    let rec equalCtx __27__ __28__ =
      match (__27__, __28__) with
      | (I.Null, I.Null) -> true__
      | (Decl (Dk, Dec (_, __A)), Decl (__D1, Dec (_, __A1))) ->
          (Conv.conv ((__A, I.id), (__A1, I.id))) && (equalCtx (Dk, __D1))
    let rec callCheckVariant (__G) (__D) (__U) =
      let Upi = A.raiseType ((concat (__G, __D)), __U) in
      let rec lookup __29__ __30__ =
        match (__29__, __30__) with
        | ((__G, __D, __U), []) ->
            ((((table :=
                  (((ref 1), __G, __D, __U), { solutions = []; lookup = 0 }))
                 :: (!table);
               if (!Global.chatter) >= 5
               then
                 (print "\n \n Added ";
                  print
                    ((Print.expToString (I.Null, Upi)) ^ "\n to Table \n"))
               else ();
               added := true__;
               if abstractionSet ()
               then
                 (((if exceeds (A.raiseType (__G, __U))
                    then
                      (if (!Global.chatter) >= 5
                       then
                         print
                           (((^) "\n term " Print.expToString (I.Null, Upi))
                              ^ " exceeds depth or length \n")
                       else ();
                       Some [])
                    else NONE))
                 (* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *))
               else NONE))
            (* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *))
        | ((__G, __D, __U), (((k, __G', __D', __U'), answ) as H)::__T) ->
            if
              variant
                ((Upi, I.id),
                  ((A.raiseType ((concat (__G', __D')), __U')), I.id))
            then
              (((!) ((:=) k) k) + 1;
               if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString (I.Null, Upi)) ^
                      " found in table \n ")
               else ();
               Some [((__G', __D', __U'), answ)])
            else lookup ((__G, __D, __U), __T) in
      lookup ((__G, __D, __U), (!table))
    let rec callCheckSubsumes (__G) (__D) (__U) =
      let rec lookup __31__ __32__ =
        match (__31__, __32__) with
        | ((__G, __D, __U), []) ->
            ((table :=
                (((ref 1), __G, __D, __U), { solutions = []; lookup = 0 }))
               :: (!table);
             if (!Global.chatter) >= 5
             then
               print
                 (((^) "Added " Print.expToString
                     (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                    ^ " to Table \n")
             else ();
             added := true__;
             if exceeds (A.raiseType (__G, __U))
             then
               (if (!Global.chatter) >= 4
                then
                  print
                    (((^) "\n term " Print.expToString
                        (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                       ^ " exceeds depth or length \n")
                else ();
                Some [])
             else NONE)
        | ((__G, __D, __U), ((k, __G', __D', __U'), answ)::__T) ->
            if subsumes ((__G, __D, __U), (__G', __D', __U'))
            then
              (if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString
                       (I.Null, (A.raiseType ((concat (__G, __D)), __U))))
                      ^ "found in table \n ")
               else ();
               ((!) ((:=) k) k) + 1;
               Some [((__G', __D', __U'), answ)])
            else lookup ((__G, __D, __U), __T) in
      lookup ((__G, __D, __U), (!table))
    let rec member __33__ __34__ =
      match (__33__, __34__) with
      | ((Dk, sk), []) -> false__
      | ((Dk, sk), ((__D1, s1), _)::__S) ->
          if (equalSub (sk, s1)) && (equalCtx (Dk, __D1))
          then true__
          else member ((Dk, sk), __S)(* do we really need to compare Gus and Gs1 ?  *)
    let rec answCheckVariant (__G) (__D) (__U) s (__O) =
      let Upi = A.raiseType ((concat (__G, __D)), __U) in
      let _ =
        if (!Global.chatter) >= 5
        then
          (print "\n AnswCheckInsert: ";
           print
             ((Print.expToString
                 (I.Null, (I.EClo ((A.raiseType (__G, __U)), s))))
                ^ "\n");
           print "\n Table Index : ";
           print ((Print.expToString (I.Null, Upi)) ^ "\n"))
        else () in
      let rec lookup __35__ __36__ __37__ __38__ __39__ __40__ =
        match (__35__, __36__, __37__, __38__, __39__, __40__) with
        | (__G, __D, __U, s, [], __T) ->
            (print
               ((Print.expToString
                   (I.Null, (I.EClo ((A.raiseType (__G, __U)), s))))
                  ^ " call should always be already in the table !\n");
             Repeated)
        | (__G, __D, __U, s,
           (((k, __G', __D', __U'),
             { solutions = __S; lookup = i; lookup = i }) as H)::__T,
           __T') ->
            if
              variant
                ((Upi, I.id),
                  ((A.raiseType ((concat (__G', __D')), __U')), I.id))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (((if member ((Dk, sk), __S)
                 then Repeated
                 else
                   ((table := (rev __T')) @
                      (((k, __G', __D', __U'),
                         { solutions = (((Dk, sk), __O) :: __S); lookup = i })
                         :: __T);
                    if (!Global.chatter) >= 5
                    then
                      (print "\n Add solution  -- ";
                       print
                         (Print.expToString
                            (I.Null,
                              (I.EClo ((A.raiseType (__G', __U')), s))));
                       print "\n solution added  -- ";
                       print
                         (Print.expToString
                            (I.Null,
                              (A.raiseType
                                 ((Names.ctxName Dk),
                                   (I.EClo ((A.raiseType (__G', __U')), sk)))))))
                    else ();
                    New)))
                (* answer check *))
            else lookup (__G, __D, __U, s) __T (__H :: __T')(* cannot happen ! *) in
      lookup (__G, __D, __U, s) (!table) []
    let rec memberSubsumes __41__ __42__ =
      match (__41__, __42__) with
      | ((__G, __D, __U, s), (__G', __U', [])) -> false__
      | ((__G, __D, __U, s), (__G', __U', ((__D1, s1), _)::__A)) ->
          let Upi = A.raiseType (__G, __U) in
          let Upi' = A.raiseType (__G', __U') in
          let s1' = reinstSub (__G', __D1, I.id) in
          let Vpis = ((I.EClo (Upi', s1)), s1') in
          let b =
            CSManager.trail (fun () -> Unify.unifiable (__D, (Upi, s), Vpis)) in
          ((if b
            then
              (if (!Global.chatter) >= 5
               then print "\n answer in table subsumes answer \n "
               else ();
               true__)
            else memberSubsumes ((__G, __D, __U, s), (__G', __U', __A)))
            (* assume G' and G are the same for now *))
    let rec shift __43__ __44__ =
      match (__43__, __44__) with
      | (0, s) -> s
      | (n, s) -> shift ((n - 1), (I.dot1 s))
    let rec answCheckSubsumes (__G) (__D) (__U) s (__O) =
      let Upi = A.raiseType (__G, __U) in
      let _ =
        if (!Global.chatter) >= 4
        then
          (print "\n AnswCheckInsert (subsumes): ";
           print ((Print.expToString (I.Null, (I.EClo (Upi, s)))) ^ "\n"))
        else () in
      let rec lookup __45__ __46__ __47__ =
        match (__45__, __46__, __47__) with
        | ((__G, __D, __U, s), [], __T) ->
            (print
               ((Print.expToString ((concat (__G, __D)), (I.EClo (__U, s))))
                  ^ " call should always be already in the table !\n");
             Repeated)
        | ((__G, __D, __U, s),
           ((k, __G', __D', __U'),
            { solutions = __A; lookup = i; lookup = i })::__T,
           __T') ->
            if subsumes ((__G, __D, __U), (__G', __D', __U'))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (if memberSubsumes ((__G, Dk, __U, sk), (__G', __U', __A))
               then Repeated
               else
                 (let s' = reinstSub (__G', __D', I.id) in
                  let _ =
                    if (!Global.chatter) >= 4
                    then
                      (print "\n new answer to be added to Index \n";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType ((concat (__G', __D')), __U'))))
                            ^ "\n");
                       print "\n answer added \n";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType
                                  (Dk,
                                    (I.EClo ((A.raiseType (__G, __U)), sk))))))
                            ^ "\n"))
                    else () in
                  let _ =
                    if
                      Unify.unifiable
                        (Dk, ((A.raiseType (__G, __U)), sk),
                          ((A.raiseType (__G', __U')), s'))
                    then
                      (if (!Global.chatter) >= 4
                       then
                         (print "\n1 unification successful !\n";
                          print
                            ((Print.expToString
                                (I.Null,
                                  (A.raiseType
                                     (Dk,
                                       (I.EClo
                                          ((A.raiseType (__G', __U')), s'))))))
                               ^ "\n"))
                       else ())
                    else
                      print
                        "\n1 unification failed! -- should never happen ?" in
                  let (Dk', sk') = A.abstractAnsw (Dk, s') in
                  let rs = reinstSub (__G', Dk', I.id) in
                  (((((match !query with
                       | NONE -> ()
                       | Some (__G1, __D1, __U1, s1, sc1) ->
                           (if (!Global.chatter) >= 4
                            then
                              (print "Generate answers for: ";
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (I.EClo
                                          ((A.raiseType (__G1, __U1)), s1))))
                                    ^ " \n");
                               print "Answer in table: ";
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (A.raiseType
                                          (Dk,
                                            (I.EClo
                                               ((A.raiseType (__G', __U')),
                                                 s'))))))
                                    ^ " : \n");
                               print
                                 ((Print.expToString
                                     (I.Null,
                                       (I.EClo
                                          ((A.raiseType
                                              (Dk,
                                                (I.EClo
                                                   ((A.raiseType (__G', __U')),
                                                     sk')))), rs))))
                                    ^ " : \n"))
                            else ();
                            ((if
                                subsumes
                                  ((__G1, __D1, __U1), (__G', __D', __U'))
                              then
                                CSManager.trail
                                  (fun () ->
                                     if
                                       Unify.unifiable
                                         (__D1,
                                           ((A.raiseType (__G1, __U1)), s1),
                                           ((I.EClo
                                               ((A.raiseType (__G', __U')),
                                                 sk')), rs))
                                     then
                                       let w =
                                         if !strengthen
                                         then
                                           Subordinate.weaken
                                             (I.Null,
                                               (IntSyn.targetFam
                                                  (I.EClo (__U1, s1))))
                                         else I.id in
                                       ((sc1 __O)
                                         (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *))
                                     else ())
                              else ())
                            (* original query is an instance of the entry we are adding answ to *)))))
                    (* nothing to do *));
                    table :=
                      ((rev __T') @
                         (((k, __G', __D', __U'),
                            {
                              solutions = (((Dk', sk'), __O) :: __A);
                              lookup = i
                            }) :: __T));
                    if (!Global.chatter) >= 5
                    then
                      (print "\n \n solution (original) was: \n";
                       print
                         ((Print.expToString
                             (I.Null, (I.EClo ((A.raiseType (__G, __U)), s))))
                            ^ "\n");
                       print "\n \n solution (deref) was: \n";
                       print
                         (((Print.expToString
                              (I.Null,
                                (A.raiseType
                                   (Dk,
                                     (I.EClo ((A.raiseType (__G, __U)), sk))))))
                             ^ "\n")
                         (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *));
                       print "\n solution added  --- ";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType
                                  (Dk',
                                    (I.EClo ((A.raiseType (__G', __U')), s'))))))
                            ^ "\n");
                       print "\n solution added (dereferenced) --- ";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType
                                  (Dk',
                                    (I.EClo ((A.raiseType (__G', __U')), sk'))))))
                            ^ "\n"))
                    else ();
                    New)
                    (*  higher-order matching *)(* reinstantiate us' *))))
            else
              lookup
                ((__G, __D, __U, s), __T,
                  (((k, __G', __D', __U'), { solutions = __A; lookup = i })
                     :: __T'))(* cannot happen ! *) in
      lookup ((__G, __D, __U, s), (!table), [])
    let rec reset () = table := []
    let rec solutions { solutions = __S; lookup = i; lookup = i } = __S
    let rec lookup { solutions = __S; lookup = i; lookup = i } = i
    let rec noAnswers =
      function
      | [] -> true__
      | (((__G', __D', __U'), answ) as H)::__L' ->
          (match List.take ((solutions answ), (lookup answ)) with
           | [] -> noAnswers __L'
           | __L -> false__)
    let rec callCheck (__G) (__D) (__U) =
      match !strategy with
      | Variant -> callCheckVariant (__G, __D, __U)
      | Subsumption -> callCheckSubsumes (__G, __D, __U)
    let rec answCheck (__G) (__D) (__U) s (__O) =
      match !strategy with
      | Variant -> answCheckVariant (__G, __D, __U, s, __O)
      | Subsumption -> answCheckSubsumes (__G, __D, __U, s, __O)
    let rec updateTable () =
      let rec update __48__ __49__ __50__ =
        match (__48__, __49__, __50__) with
        | ([], __T, Flag) -> (Flag, __T)
        | (((k, __G, __D, __U), { solutions = __S; lookup = i; lookup = i })::__T,
           __T', Flag) ->
            let l = length __S in
            ((if l = i
              then
                update __T
                  (((k, __G, __D, __U),
                     { solutions = __S; lookup = (List.length __S) }) :: __T')
                  Flag
              else
                update __T
                  (((k, __G, __D, __U),
                     { solutions = __S; lookup = (List.length __S) }) :: __T')
                  true__)
              (* no new solutions were added in the previous stage *)
              (* new solutions were added *)) in
      let (Flag, __T) = update (!table) [] false__ in
      let r = Flag || (!added) in ((added := false__; (:=) table rev __T; r)
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
    let updateTable = updateTable
  end ;;
