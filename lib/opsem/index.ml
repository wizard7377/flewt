
(* Indexing *)
(* Author: Brigitte Pientka *)
module type TABLEINDEX  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
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
    (* table: __g, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *)
    val table :
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list
        ref
    val noAnswers :
      ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list -> bool
    (* call check/insert *)
    (* callCheck (__g, __d, __u)
   *
   * if __d, __g |- __u     in table  
   *    then Some(entries)
   * if __d, __g |- __u not in table 
   *    then None  
   *          SIDE EFFECT: __d, __g |- __u added to table
   *)
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) ->
        ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list option
    (* answer check/insert *)
    (* answerCheck (__g, __d, (__u,s))
   * 
   * Assumption: __d, __g |- __u is in table
   *             and A represents the corresponding solutions
   * 
   * __g |- s : __d, __g
   * Dk, __g |- sk : __d, __g
   *
   * If  (Dk, sk) in A then repeated
   *  else New
   *)
    val answerCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub *
        CompSyn.pskeleton) -> answState
    (* reset table *)
    val reset : unit -> unit
    val printTable : unit -> unit
    val printTableEntries : unit -> unit
    (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
    val updateTable : unit -> bool
    val solutions :
      answer -> ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list
    val lookup : answer -> int
  end;;




(* Indexing for table *)
(* Author: Brigitte Pientka *)
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
                               (*! structure IntSyn' : INTSYN !*)
                               (*! structure CompSyn': COMPSYN !*)
                               (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                               (*! sharing Subordinate.IntSyn = IntSyn'                   !*)
                               (*! sharing Conv.IntSyn = IntSyn' !*)
                               (*! sharing Unify.IntSyn = IntSyn' !*)
                               (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                               (*! sharing Whnf.IntSyn = IntSyn' !*)
                               (*! sharing Print.IntSyn = IntSyn' !*)
                               (*! sharing CPrint.IntSyn = IntSyn' !*)
                               (*! sharing CPrint.CompSyn = CompSyn' !*)
                               (*! sharing Names.IntSyn = IntSyn' !*)
                               module TypeCheck : TYPECHECK
                             end) : TABLEINDEX =
  struct
    (*! sharing TypeCheck.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    module Conv = Conv
    (* TABLE

   table entry : __d, __g  |- u

   Answer substitution:

                 Dk, __g  |- sk : __d, __g

   Answer :
                 Dk, __g |- u[sk]
   *)
    (* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *)
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    (* entry = (((i, __g, __d, __u), A)) where i is the access counter
   *)
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
    (* ---------------------------------------------------------------------- *)
    (* global search parameters *)
    let strategy = ref Variant
    (* Subsumption *)
    (* Variant *)
    (* term abstraction after term depth is greater than 5 *)
    let termDepth = (ref None : int option ref)
    let ctxDepth = (ref None : int option ref)
    let ctxLength = (ref None : int option ref)
    (*   val termDepth = ref (!globalTermDepth); *)
    (*   val ctxDepth = ref (!globalCtxDepth);   *)
    (*   val ctxLength = ref (!globalCtxLength); *)
    (* apply strengthening during abstraction *)
    let strengthen = AbstractTabled.strengthen
    (* original query *)
    let (query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub *
        (CompSyn.pskeleton -> unit)) option ref)
      = ref None
    (* ---------------------------------------------------------------------- *)
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    let (table : index ref) = ref []
    let rec concat =
      function
      | (I.Null, __g') -> __g'
      | (Decl (__g, __d), __g') -> I.Decl ((concat (__g, __g')), __d)
    let rec reverse =
      function
      | (I.Null, __g') -> __g'
      | (Decl (__g, __d), __g') -> reverse (__g, (I.Decl (__g', __d)))
    let rec printTable () =
      let rec proofTerms =
        function
        | (__g, __d, __u, []) -> print ""
        | (__g, __d, __u, ((__d', s'), _)::S) ->
            ((try
                print
                  (Print.expToString
                     (I.Null,
                       (A.raiseType
                          ((Names.ctxName __d'),
                            (I.EClo
                               ((A.raiseType ((Names.ctxName __g), __u)), s'))))))
              with | _ -> print "EXCEPTION");
             print ", \n\t";
             proofTerms (__g, __d, __u, S)) in
      let rec printT =
        function
        | [] -> ()
        | ((k, __g, __d, __u), { solutions = S; lookup = i; lookup = i })::T ->
            (match S with
             | [] ->
                 (printT T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
                       ^ ", None\n"))
             | a::answ ->
                 (printT T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
                       ^ ", [\n\t");
                  proofTerms (__g, __d, __u, (rev S));
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
        | ((k, __g, __d, __u), { solutions = S; lookup = i; lookup = i })::T ->
            (printT T;
             print
               ((((Print.expToString
                     (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
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
      function | I.Nil -> 0 | SClo (S, s') -> (+) 1 lengthSpine S
    let rec exceedsTermDepth i =
      match !termDepth with | None -> false__ | Some n -> i > n
    let rec exceedsCtxDepth i =
      match !ctxDepth with
      | None -> false__
      | Some n ->
          (print
             (((^) (((^) "\n exceedsCtxDepth " Int.toString i) ^ " > ")
                 Int.toString n)
                ^ " ? ");
           i > n)
    let rec exceedsCtxLength i =
      match !ctxLength with | None -> false__ | Some n -> i > n
    let rec max (x, y) = if x > y then x else y
    let rec oroption =
      function
      | (None, None, None) -> false__
      | (Some k, _, _) -> true__
      | (_, Some n, _) -> true__
      | (_, _, Some n) -> true__
    let rec abstractionSet () =
      oroption ((!termDepth), (!ctxDepth), (!ctxLength))
    let rec exceeds (__u) = countDecl (0, 0, __u)
    let rec countDecl =
      function
      | (ctrType, ctrLength, Pi ((__d, _), __v)) ->
          let ctrType' = countDec (0, __d) in
          if ctrType' > ctrType
          then countDecl (ctrType', (ctrLength + 1), __v)
          else countDecl (ctrType, (ctrLength + 1), __v)
      | (ctrType, ctrLength, __u) ->
          let ctrTerm = count (0, __u) in
          (exceedsCtxDepth ctrType) ||
            ((exceedsCtxLength ctrLength) ||
               (exceedsTermDepth (count (0, __u))))
    let rec countDec =
      function
      | (ctr, Dec (_, __u)) -> count (ctr, __u)
      | (ctr, BDec (_, s)) -> 0
    let rec count =
      function
      | (ctr, (Uni (__l) as __u)) -> ctr
      | (ctr, Pi ((__d, _), __v)) ->
          let ctrTerm = count (ctr, __v) in
          let ctrType = countDec (ctr, __d) in max (ctrType, ctrTerm)
      | (ctr, Root (F, S)) ->
          let ctrDepth = countSpine (1, S) in (ctrDepth + 1) + ctr
      | (ctr, Redex (__u, S)) ->
          let ctrDepth = count (0, __u) in
          let ctrDepth' = countSpine (ctrDepth, S) in
          (max (ctrDepth', ctrDepth)) + ctr
      | (ctr, Lam (__d, __u)) -> count ((ctr + 1), __u)
      | (ctr, (EVar _ as x)) -> ctr
      | (ctr, EClo (E, s)) -> count (ctr, E)
      | (ctr, (FgnExp (cs, ops) as F)) -> ctr
    let rec countSpine =
      function
      | (ctrDepth, I.Nil) -> ctrDepth
      | (ctr, SClo (S, s')) -> countSpine (ctr, S)
      | (ctrDepth, App (__u, S)) ->
          let ctrDepth' = count (0, __u) in
          countSpine ((max (ctrDepth', ctrDepth)), S)
    let rec reinstSub =
      function
      | (__g, I.Null, s) -> s
      | (__g, Decl (__d, Dec (_, A)), s) ->
          let x = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp x), (reinstSub (__g, __d, s)))
    let rec variant (__Us, __Us') = Conv.conv (__Us, __Us')
    let rec subsumes ((__g, __d, __u), (__g', __d', __u')) =
      let Upi = A.raiseType (__g, __u) in
      let Upi' = A.raiseType (__g', __u') in
      let s' = reinstSub (__g', __d', I.id) in
      CSManager.trail
        (function | () -> Unify.unifiable (__d, (Upi', s'), (Upi, I.id)))
    let rec equalSub =
      function
      | (Shift k, Shift k') -> k = k'
      | (Dot (F, S), Dot (__F', S')) ->
          (equalFront (F, __F')) && (equalSub (S, S'))
      | (Dot (F, S), Shift k) -> false__
      | (Shift k, Dot (F, S)) -> false__
    let rec equalFront =
      function
      | (Idx n, Idx n') -> n = n'
      | (Exp (__u), Exp (__v)) -> Conv.conv ((__u, I.id), (__v, I.id))
      | (I.Undef, I.Undef) -> true__
    let rec equalSub1 (Dot (ms, s), Dot (ms', s')) = equalSub (s, s')
    let rec equalCtx =
      function
      | (I.Null, I.Null) -> true__
      | (Decl (Dk, Dec (_, A)), Decl (D1, Dec (_, A1))) ->
          (Conv.conv ((A, I.id), (A1, I.id))) && (equalCtx (Dk, D1))
    let rec callCheckVariant (__g, __d, __u) =
      let Upi = A.raiseType ((concat (__g, __d)), __u) in
      let rec lookup =
        function
        | ((__g, __d, __u), []) ->
            ((table := (((ref 1), __g, __d, __u), { solutions = []; lookup = 0 }))
               :: (!table);
             if (!Global.chatter) >= 5
             then
               (print "\n \n Added ";
                print ((Print.expToString (I.Null, Upi)) ^ "\n to Table \n"))
             else ();
             added := true__;
             if abstractionSet ()
             then
               (if exceeds (A.raiseType (__g, __u))
                then
                  (if (!Global.chatter) >= 5
                   then
                     print
                       (((^) "\n term " Print.expToString (I.Null, Upi)) ^
                          " exceeds depth or length \n")
                   else ();
                   Some [])
                else None)
             else None)
        | ((__g, __d, __u), (((k, __g', __d', __u'), answ) as H)::T) ->
            if
              variant
                ((Upi, I.id), ((A.raiseType ((concat (__g', __d')), __u')), I.id))
            then
              (((!) ((:=) k) k) + 1;
               if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString (I.Null, Upi)) ^
                      " found in table \n ")
               else ();
               Some [((__g', __d', __u'), answ)])
            else lookup ((__g, __d, __u), T) in
      lookup ((__g, __d, __u), (!table))
    let rec callCheckSubsumes (__g, __d, __u) =
      let rec lookup =
        function
        | ((__g, __d, __u), []) ->
            ((table := (((ref 1), __g, __d, __u), { solutions = []; lookup = 0 }))
               :: (!table);
             if (!Global.chatter) >= 5
             then
               print
                 (((^) "Added " Print.expToString
                     (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
                    ^ " to Table \n")
             else ();
             added := true__;
             if exceeds (A.raiseType (__g, __u))
             then
               (if (!Global.chatter) >= 4
                then
                  print
                    (((^) "\n term " Print.expToString
                        (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
                       ^ " exceeds depth or length \n")
                else ();
                Some [])
             else None)
        | ((__g, __d, __u), ((k, __g', __d', __u'), answ)::T) ->
            if subsumes ((__g, __d, __u), (__g', __d', __u'))
            then
              (if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString
                       (I.Null, (A.raiseType ((concat (__g, __d)), __u))))
                      ^ "found in table \n ")
               else ();
               ((!) ((:=) k) k) + 1;
               Some [((__g', __d', __u'), answ)])
            else lookup ((__g, __d, __u), T) in
      lookup ((__g, __d, __u), (!table))
    let rec member =
      function
      | ((Dk, sk), []) -> false__
      | ((Dk, sk), ((D1, s1), _)::S) ->
          if (equalSub (sk, s1)) && (equalCtx (Dk, D1))
          then true__
          else member ((Dk, sk), S)
    let rec answCheckVariant (__g, __d, __u, s, O) =
      let Upi = A.raiseType ((concat (__g, __d)), __u) in
      let _ =
        if (!Global.chatter) >= 5
        then
          (print "\n AnswCheckInsert: ";
           print
             ((Print.expToString (I.Null, (I.EClo ((A.raiseType (__g, __u)), s))))
                ^ "\n");
           print "\n Table Index : ";
           print ((Print.expToString (I.Null, Upi)) ^ "\n"))
        else () in
      let rec lookup arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | ((__g, __d, __u, s), [], T) ->
            (print
               ((Print.expToString
                   (I.Null, (I.EClo ((A.raiseType (__g, __u)), s))))
                  ^ " call should always be already in the table !\n");
             Repeated)
        | ((__g, __d, __u, s),
           (((k, __g', __d', __u'), { solutions = S; lookup = i; lookup = i }) as H)::T,
           T') ->
            if
              variant
                ((Upi, I.id), ((A.raiseType ((concat (__g', __d')), __u')), I.id))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (if member ((Dk, sk), S)
               then Repeated
               else
                 ((table := (rev T')) @
                    (((k, __g', __d', __u'),
                       { solutions = (((Dk, sk), O) :: S); lookup = i }) :: T);
                  if (!Global.chatter) >= 5
                  then
                    (print "\n Add solution  -- ";
                     print
                       (Print.expToString
                          (I.Null, (I.EClo ((A.raiseType (__g', __u')), s))));
                     print "\n solution added  -- ";
                     print
                       (Print.expToString
                          (I.Null,
                            (A.raiseType
                               ((Names.ctxName Dk),
                                 (I.EClo ((A.raiseType (__g', __u')), sk)))))))
                  else ();
                  New))
            else lookup (__g, __d, __u, s) T (H :: T') in
      lookup (__g, __d, __u, s) (!table) []
    let rec memberSubsumes =
      function
      | ((__g, __d, __u, s), (__g', __u', [])) -> false__
      | ((__g, __d, __u, s), (__g', __u', ((D1, s1), _)::A)) ->
          let Upi = A.raiseType (__g, __u) in
          let Upi' = A.raiseType (__g', __u') in
          let s1' = reinstSub (__g', D1, I.id) in
          let Vpis = ((I.EClo (Upi', s1)), s1') in
          let b =
            CSManager.trail
              (function | () -> Unify.unifiable (__d, (Upi, s), Vpis)) in
          if b
          then
            (if (!Global.chatter) >= 5
             then print "\n answer in table subsumes answer \n "
             else ();
             true__)
          else memberSubsumes ((__g, __d, __u, s), (__g', __u', A))
    let rec shift =
      function | (0, s) -> s | (n, s) -> shift ((n - 1), (I.dot1 s))
    let rec answCheckSubsumes (__g, __d, __u, s, O) =
      let Upi = A.raiseType (__g, __u) in
      let _ =
        if (!Global.chatter) >= 4
        then
          (print "\n AnswCheckInsert (subsumes): ";
           print ((Print.expToString (I.Null, (I.EClo (Upi, s)))) ^ "\n"))
        else () in
      let rec lookup =
        function
        | ((__g, __d, __u, s), [], T) ->
            (print
               ((Print.expToString ((concat (__g, __d)), (I.EClo (__u, s)))) ^
                  " call should always be already in the table !\n");
             Repeated)
        | ((__g, __d, __u, s),
           ((k, __g', __d', __u'), { solutions = A; lookup = i; lookup = i })::T,
           T') ->
            if subsumes ((__g, __d, __u), (__g', __d', __u'))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (if memberSubsumes ((__g, Dk, __u, sk), (__g', __u', A))
               then Repeated
               else
                 (let s' = reinstSub (__g', __d', I.id) in
                  let _ =
                    if (!Global.chatter) >= 4
                    then
                      (print "\n new answer to be added to Index \n";
                       print
                         ((Print.expToString
                             (I.Null, (A.raiseType ((concat (__g', __d')), __u'))))
                            ^ "\n");
                       print "\n answer added \n";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType
                                  (Dk, (I.EClo ((A.raiseType (__g, __u)), sk))))))
                            ^ "\n"))
                    else () in
                  let _ =
                    if
                      Unify.unifiable
                        (Dk, ((A.raiseType (__g, __u)), sk),
                          ((A.raiseType (__g', __u')), s'))
                    then
                      (if (!Global.chatter) >= 4
                       then
                         (print "\n1 unification successful !\n";
                          print
                            ((Print.expToString
                                (I.Null,
                                  (A.raiseType
                                     (Dk,
                                       (I.EClo ((A.raiseType (__g', __u')), s'))))))
                               ^ "\n"))
                       else ())
                    else
                      print
                        "\n1 unification failed! -- should never happen ?" in
                  let (Dk', sk') = A.abstractAnsw (Dk, s') in
                  let rs = reinstSub (__g', Dk', I.id) in
                  (match !query with
                   | None -> ()
                   | Some (G1, D1, __U1, s1, sc1) ->
                       (if (!Global.chatter) >= 4
                        then
                          (print "Generate answers for: ";
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (I.EClo ((A.raiseType (G1, __U1)), s1))))
                                ^ " \n");
                           print "Answer in table: ";
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (A.raiseType
                                      (Dk,
                                        (I.EClo ((A.raiseType (__g', __u')), s'))))))
                                ^ " : \n");
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (I.EClo
                                      ((A.raiseType
                                          (Dk,
                                            (I.EClo
                                               ((A.raiseType (__g', __u')), sk')))),
                                        rs))))
                                ^ " : \n"))
                        else ();
                        if subsumes ((G1, D1, __U1), (__g', __d', __u'))
                        then
                          CSManager.trail
                            (function
                             | () ->
                                 if
                                   Unify.unifiable
                                     (D1, ((A.raiseType (G1, __U1)), s1),
                                       ((I.EClo ((A.raiseType (__g', __u')), sk')),
                                         rs))
                                 then
                                   let w =
                                     if !strengthen
                                     then
                                       Subordinate.weaken
                                         (I.Null,
                                           (IntSyn.targetFam
                                              (I.EClo (__U1, s1))))
                                     else I.id in
                                   sc1 O
                                 else ())
                        else ()));
                  table :=
                    ((rev T') @
                       (((k, __g', __d', __u'),
                          { solutions = (((Dk', sk'), O) :: A); lookup = i })
                          :: T));
                  if (!Global.chatter) >= 5
                  then
                    (print "\n \n solution (original) was: \n";
                     print
                       ((Print.expToString
                           (I.Null, (I.EClo ((A.raiseType (__g, __u)), s))))
                          ^ "\n");
                     print "\n \n solution (deref) was: \n";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk, (I.EClo ((A.raiseType (__g, __u)), sk))))))
                          ^ "\n");
                     print "\n solution added  --- ";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk', (I.EClo ((A.raiseType (__g', __u')), s'))))))
                          ^ "\n");
                     print "\n solution added (dereferenced) --- ";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk', (I.EClo ((A.raiseType (__g', __u')), sk'))))))
                          ^ "\n"))
                  else ();
                  New))
            else
              lookup
                ((__g, __d, __u, s), T,
                  (((k, __g', __d', __u'), { solutions = A; lookup = i }) :: T')) in
      lookup ((__g, __d, __u, s), (!table), [])
    let rec reset () = table := []
    let rec solutions { solutions = S; lookup = i; lookup = i } = S
    let rec lookup { solutions = S; lookup = i; lookup = i } = i
    let rec noAnswers =
      function
      | [] -> true__
      | (((__g', __d', __u'), answ) as H)::__l' ->
          (match List.take ((solutions answ), (lookup answ)) with
           | [] -> noAnswers __l'
           | __l -> false__)
    let rec callCheck (__g, __d, __u) =
      match !strategy with
      | Variant -> callCheckVariant (__g, __d, __u)
      | Subsumption -> callCheckSubsumes (__g, __d, __u)
    let rec answCheck (__g, __d, __u, s, O) =
      match !strategy with
      | Variant -> answCheckVariant (__g, __d, __u, s, O)
      | Subsumption -> answCheckSubsumes (__g, __d, __u, s, O)
    let rec updateTable () =
      let rec update arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | ([], T, Flag) -> (Flag, T)
        | (((k, __g, __d, __u), { solutions = S; lookup = i; lookup = i })::T, T',
           Flag) ->
            let l = length S in
            if l = i
            then
              update T
                (((k, __g, __d, __u), { solutions = S; lookup = (List.length S) })
                   :: T') Flag
            else
              update T
                (((k, __g, __d, __u), { solutions = S; lookup = (List.length S) })
                   :: T') true__ in
      let (Flag, T) = update (!table) [] false__ in
      let r = Flag || (!added) in added := false__; (:=) table rev T; r
    (* Global Table *)
    (* concat(Gdp, __g) = __g''
     *
     * if Gdp = ym...y1
     *    __g   = xn...x1
     * then
     *    Gdp, __g = __g''
     *    ym...y1, xn...x1
     *
     *)
    (* ---------------------------------------------------------------------- *)
    (* printTable () = () *)
    (* (print (Print.expToString (I.Null,  *)
    (*              A.raiseType(Names.ctxName(concat(__g,__d')), I.EClo(__u, s')))) *)
    (* do not print pskeletons *)
    (* printTableEntries () = () *)
    (* ---------------------------------------------------------------------- *)
    (* Term Abstraction *)
    (* countDepth __u =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *)
    (*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
    (*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)
    (*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)
    (* to revise ?*)
    (*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
    (*         (ctrLength + ctr) *)
    (*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)
    (* shouldn't happen *)
    (* shouldn't happen *)
    (* count max depth of term in S + length of S *)
    (* ? *)
    (* ---------------------------------------------------------------------- *)
    (* reinstSub (__g, __d, s) = s'
    *
    * If __d', __g |- s : __d, __g
    * then  __g |- s' : __d, __g
    *)
    (* ---------------------------------------------------------------------- *)
    (* variant (__u,s) (__u',s')) = bool   *)
    (* subsumes ((__g, __d, __u), (__g', __d', __u')) = bool
     *
     * if
     *    __d, __g   |- __u
     *    __d', __g' |- __u'
     * then
     *      __g' |- s' : __d', __g'
     *    return true if __d, __g |- __u is an instance of __g' |- __u'[s']
     *    otherwise false
     *
     *)
    (* ---------------------------------------------------------------------- *)
    (* Call check and insert *)
    (* callCheck (__g, __d, __u) = callState

       check whether __d, __g |- __u is in the table

     returns None,
        if __d, __g |- __u is not already in the table
          Sideeffect: add __d, __g |- __u to table

     returns Some(A)
        if __d, __g |- __u is in table and
          A is an entry in the table together with its answer list

    Variant:
    if it succeeds there is exactly one table entry which is a variant to __u
    Subsumption:
    if it succeeds it will return the most general table entry of which __u is
    an instance of (by invariant now, the most general table entry will be found first,
    any entry found later, will be an instance of this entry)
    *)
    (* if termdepth(__u) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *)
    (* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *)
    (* Subsumption:

       Assumes: Table is in order [tn, ...., t1]
       i.e. tn is added to the table later than t1
            this implies that tn is more general than ti (i < n)

       if we find a tn s.t M is an instance of it, then return tn
       and do not search further

    *)
    (* ---------------------------------------------------------------------- *)
    (* do we really need to compare Gus and Gs1 ?  *)
    (* answer check and insert

      if     __g |- __u[s]
          __d, __g |- __u
             __g |- s : __d, __g

      answerCheck (__g, __d, (__u,s)) = repeated
         if s already occurs in answer list for __u
      answerCheck (__g, __d, (__u,s)) = new
         if s did not occur in answer list for __u
         Sideeffect: update answer list for __u

        Dk, __g |- sk : __d, __g
        Dk, __g |- __u[sk]

        sk is the abstraction of s and Dk contains all "free" vars

     *)
    (* cannot happen ! *)
    (* answer check *)
    (* memberSubsumes ((__g, Dk, __u, sk), (__g', __u', A)) = bool

   If Dk, __g |- __u[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for all i in [1, ..., n]
          Di, __g' |- __u'[si]
              __g' |- si' : Di, __g'
   then
     exists an i in [1,...,n]  s.t.
         Dk, __g |- __u[sk] is an instance of __g' |- __u'[si']
   *)
    (* assume __g' and __g are the same for now *)
    (* cannot happen ! *)
    (*  higher-order matching *)
    (* reinstantiate us' *)
    (* nothing to do *)
    (* original query is an instance of the entry we are adding answ to *)
    (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
    (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(__g, Dk), __u), sk)) *)
    (* ---------------------------------------------------------------------- *)
    (* TOP LEVEL *)
    (* needs to take into account previous size of table *)
    (* no new solutions were added in the previous stage *)
    (* new solutions were added *)
    (* in each stage incrementally increase termDepth *)
    (*          termDepth := (!termDepth +1); *)
    (*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*)
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
