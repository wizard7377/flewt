
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
    (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *)
    val table :
      ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list
        ref
    val noAnswers :
      ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list -> bool
    (* call check/insert *)
    (* callCheck (G, D, U)
   *
   * if D, G |- U     in table  
   *    then SOME(entries)
   * if D, G |- U not in table 
   *    then NONE  
   *          SIDE EFFECT: D, G |- U added to table
   *)
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) ->
        ((IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp) * answer) list option
    (* answer check/insert *)
    (* answerCheck (G, D, (U,s))
   * 
   * Assumption: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
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

   table entry : D, G  |- u

   Answer substitution:

                 Dk, G  |- sk : D, G

   Answer :
                 Dk, G |- u[sk]
   *)
    (* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *)
    type nonrec answer =
      <
        solutions: ((IntSyn.dctx * IntSyn.__Sub) * CompSyn.pskeleton) list  ;
        lookup: int   > 
    (* entry = (((i, G, D, U), A)) where i is the access counter
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
    let termDepth = (ref NONE : int option ref)
    let ctxDepth = (ref NONE : int option ref)
    let ctxLength = (ref NONE : int option ref)
    (*   val termDepth = ref (!globalTermDepth); *)
    (*   val ctxDepth = ref (!globalCtxDepth);   *)
    (*   val ctxLength = ref (!globalCtxLength); *)
    (* apply strengthening during abstraction *)
    let strengthen = AbstractTabled.strengthen
    (* original query *)
    let (query :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp * IntSyn.__Sub *
        (CompSyn.pskeleton -> unit)) option ref)
      = ref NONE
    (* ---------------------------------------------------------------------- *)
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    let (table : index ref) = ref []
    let rec concat =
      function
      | (I.Null, G') -> G'
      | (Decl (G, D), G') -> I.Decl ((concat (G, G')), D)
    let rec reverse =
      function
      | (I.Null, G') -> G'
      | (Decl (G, D), G') -> reverse (G, (I.Decl (G', D)))
    let rec printTable () =
      let rec proofTerms =
        function
        | (G, D, U, []) -> print ""
        | (G, D, U, ((D', s'), _)::S) ->
            ((try
                print
                  (Print.expToString
                     (I.Null,
                       (A.raiseType
                          ((Names.ctxName D'),
                            (I.EClo
                               ((A.raiseType ((Names.ctxName G), U)), s'))))))
              with | _ -> print "EXCEPTION");
             print ", \n\t";
             proofTerms (G, D, U, S)) in
      let rec printT =
        function
        | [] -> ()
        | ((k, G, D, U), { solutions = S; lookup = i; lookup = i })::T ->
            (match S with
             | [] ->
                 (printT T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (G, D)), U))))
                       ^ ", NONE\n"))
             | a::answ ->
                 (printT T;
                  print
                    ((Print.expToString
                        (I.Null, (A.raiseType ((concat (G, D)), U))))
                       ^ ", [\n\t");
                  proofTerms (G, D, U, (rev S));
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
        | ((k, G, D, U), { solutions = S; lookup = i; lookup = i })::T ->
            (printT T;
             print
               ((((Print.expToString
                     (I.Null, (A.raiseType ((concat (G, D)), U))))
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
      match !termDepth with | NONE -> false__ | SOME n -> i > n
    let rec exceedsCtxDepth i =
      match !ctxDepth with
      | NONE -> false__
      | SOME n ->
          (print
             (((^) (((^) "\n exceedsCtxDepth " Int.toString i) ^ " > ")
                 Int.toString n)
                ^ " ? ");
           i > n)
    let rec exceedsCtxLength i =
      match !ctxLength with | NONE -> false__ | SOME n -> i > n
    let rec max (x, y) = if x > y then x else y
    let rec oroption =
      function
      | (NONE, NONE, NONE) -> false__
      | (SOME k, _, _) -> true__
      | (_, SOME n, _) -> true__
      | (_, _, SOME n) -> true__
    let rec abstractionSet () =
      oroption ((!termDepth), (!ctxDepth), (!ctxLength))
    let rec exceeds (U) = countDecl (0, 0, U)
    let rec countDecl =
      function
      | (ctrType, ctrLength, Pi ((D, _), V)) ->
          let ctrType' = countDec (0, D) in
          if ctrType' > ctrType
          then countDecl (ctrType', (ctrLength + 1), V)
          else countDecl (ctrType, (ctrLength + 1), V)
      | (ctrType, ctrLength, U) ->
          let ctrTerm = count (0, U) in
          (exceedsCtxDepth ctrType) ||
            ((exceedsCtxLength ctrLength) ||
               (exceedsTermDepth (count (0, U))))
    let rec countDec =
      function
      | (ctr, Dec (_, U)) -> count (ctr, U)
      | (ctr, BDec (_, s)) -> 0
    let rec count =
      function
      | (ctr, (Uni (L) as U)) -> ctr
      | (ctr, Pi ((D, _), V)) ->
          let ctrTerm = count (ctr, V) in
          let ctrType = countDec (ctr, D) in max (ctrType, ctrTerm)
      | (ctr, Root (F, S)) ->
          let ctrDepth = countSpine (1, S) in (ctrDepth + 1) + ctr
      | (ctr, Redex (U, S)) ->
          let ctrDepth = count (0, U) in
          let ctrDepth' = countSpine (ctrDepth, S) in
          (max (ctrDepth', ctrDepth)) + ctr
      | (ctr, Lam (D, U)) -> count ((ctr + 1), U)
      | (ctr, (EVar _ as X)) -> ctr
      | (ctr, EClo (E, s)) -> count (ctr, E)
      | (ctr, (FgnExp (cs, ops) as F)) -> ctr
    let rec countSpine =
      function
      | (ctrDepth, I.Nil) -> ctrDepth
      | (ctr, SClo (S, s')) -> countSpine (ctr, S)
      | (ctrDepth, App (U, S)) ->
          let ctrDepth' = count (0, U) in
          countSpine ((max (ctrDepth', ctrDepth)), S)
    let rec reinstSub =
      function
      | (G, I.Null, s) -> s
      | (G, Decl (D, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (reinstSub (G, D, s)))
    let rec variant (Us, Us') = Conv.conv (Us, Us')
    let rec subsumes ((G, D, U), (G', D', U')) =
      let Upi = A.raiseType (G, U) in
      let Upi' = A.raiseType (G', U') in
      let s' = reinstSub (G', D', I.id) in
      CSManager.trail
        (function | () -> Unify.unifiable (D, (Upi', s'), (Upi, I.id)))
    let rec equalSub =
      function
      | (Shift k, Shift k') -> k = k'
      | (Dot (F, S), Dot (F', S')) ->
          (equalFront (F, F')) && (equalSub (S, S'))
      | (Dot (F, S), Shift k) -> false__
      | (Shift k, Dot (F, S)) -> false__
    let rec equalFront =
      function
      | (Idx n, Idx n') -> n = n'
      | (Exp (U), Exp (V)) -> Conv.conv ((U, I.id), (V, I.id))
      | (I.Undef, I.Undef) -> true__
    let rec equalSub1 (Dot (ms, s), Dot (ms', s')) = equalSub (s, s')
    let rec equalCtx =
      function
      | (I.Null, I.Null) -> true__
      | (Decl (Dk, Dec (_, A)), Decl (D1, Dec (_, A1))) ->
          (Conv.conv ((A, I.id), (A1, I.id))) && (equalCtx (Dk, D1))
    let rec callCheckVariant (G, D, U) =
      let Upi = A.raiseType ((concat (G, D)), U) in
      let rec lookup =
        function
        | ((G, D, U), []) ->
            ((table := (((ref 1), G, D, U), { solutions = []; lookup = 0 }))
               :: (!table);
             if (!Global.chatter) >= 5
             then
               (print "\n \n Added ";
                print ((Print.expToString (I.Null, Upi)) ^ "\n to Table \n"))
             else ();
             added := true__;
             if abstractionSet ()
             then
               (if exceeds (A.raiseType (G, U))
                then
                  (if (!Global.chatter) >= 5
                   then
                     print
                       (((^) "\n term " Print.expToString (I.Null, Upi)) ^
                          " exceeds depth or length \n")
                   else ();
                   SOME [])
                else NONE)
             else NONE)
        | ((G, D, U), (((k, G', D', U'), answ) as H)::T) ->
            if
              variant
                ((Upi, I.id), ((A.raiseType ((concat (G', D')), U')), I.id))
            then
              (((!) ((:=) k) k) + 1;
               if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString (I.Null, Upi)) ^
                      " found in table \n ")
               else ();
               SOME [((G', D', U'), answ)])
            else lookup ((G, D, U), T) in
      lookup ((G, D, U), (!table))
    let rec callCheckSubsumes (G, D, U) =
      let rec lookup =
        function
        | ((G, D, U), []) ->
            ((table := (((ref 1), G, D, U), { solutions = []; lookup = 0 }))
               :: (!table);
             if (!Global.chatter) >= 5
             then
               print
                 (((^) "Added " Print.expToString
                     (I.Null, (A.raiseType ((concat (G, D)), U))))
                    ^ " to Table \n")
             else ();
             added := true__;
             if exceeds (A.raiseType (G, U))
             then
               (if (!Global.chatter) >= 4
                then
                  print
                    (((^) "\n term " Print.expToString
                        (I.Null, (A.raiseType ((concat (G, D)), U))))
                       ^ " exceeds depth or length \n")
                else ();
                SOME [])
             else NONE)
        | ((G, D, U), ((k, G', D', U'), answ)::T) ->
            if subsumes ((G, D, U), (G', D', U'))
            then
              (if (!Global.chatter) >= 5
               then
                 print
                   (((^) "call " Print.expToString
                       (I.Null, (A.raiseType ((concat (G, D)), U))))
                      ^ "found in table \n ")
               else ();
               ((!) ((:=) k) k) + 1;
               SOME [((G', D', U'), answ)])
            else lookup ((G, D, U), T) in
      lookup ((G, D, U), (!table))
    let rec member =
      function
      | ((Dk, sk), []) -> false__
      | ((Dk, sk), ((D1, s1), _)::S) ->
          if (equalSub (sk, s1)) && (equalCtx (Dk, D1))
          then true__
          else member ((Dk, sk), S)
    let rec answCheckVariant (G, D, U, s, O) =
      let Upi = A.raiseType ((concat (G, D)), U) in
      let _ =
        if (!Global.chatter) >= 5
        then
          (print "\n AnswCheckInsert: ";
           print
             ((Print.expToString (I.Null, (I.EClo ((A.raiseType (G, U)), s))))
                ^ "\n");
           print "\n Table Index : ";
           print ((Print.expToString (I.Null, Upi)) ^ "\n"))
        else () in
      let rec lookup arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | ((G, D, U, s), [], T) ->
            (print
               ((Print.expToString
                   (I.Null, (I.EClo ((A.raiseType (G, U)), s))))
                  ^ " call should always be already in the table !\n");
             Repeated)
        | ((G, D, U, s),
           (((k, G', D', U'), { solutions = S; lookup = i; lookup = i }) as H)::T,
           T') ->
            if
              variant
                ((Upi, I.id), ((A.raiseType ((concat (G', D')), U')), I.id))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (if member ((Dk, sk), S)
               then Repeated
               else
                 ((table := (rev T')) @
                    (((k, G', D', U'),
                       { solutions = (((Dk, sk), O) :: S); lookup = i }) :: T);
                  if (!Global.chatter) >= 5
                  then
                    (print "\n Add solution  -- ";
                     print
                       (Print.expToString
                          (I.Null, (I.EClo ((A.raiseType (G', U')), s))));
                     print "\n solution added  -- ";
                     print
                       (Print.expToString
                          (I.Null,
                            (A.raiseType
                               ((Names.ctxName Dk),
                                 (I.EClo ((A.raiseType (G', U')), sk)))))))
                  else ();
                  New))
            else lookup (G, D, U, s) T (H :: T') in
      lookup (G, D, U, s) (!table) []
    let rec memberSubsumes =
      function
      | ((G, D, U, s), (G', U', [])) -> false__
      | ((G, D, U, s), (G', U', ((D1, s1), _)::A)) ->
          let Upi = A.raiseType (G, U) in
          let Upi' = A.raiseType (G', U') in
          let s1' = reinstSub (G', D1, I.id) in
          let Vpis = ((I.EClo (Upi', s1)), s1') in
          let b =
            CSManager.trail
              (function | () -> Unify.unifiable (D, (Upi, s), Vpis)) in
          if b
          then
            (if (!Global.chatter) >= 5
             then print "\n answer in table subsumes answer \n "
             else ();
             true__)
          else memberSubsumes ((G, D, U, s), (G', U', A))
    let rec shift =
      function | (0, s) -> s | (n, s) -> shift ((n - 1), (I.dot1 s))
    let rec answCheckSubsumes (G, D, U, s, O) =
      let Upi = A.raiseType (G, U) in
      let _ =
        if (!Global.chatter) >= 4
        then
          (print "\n AnswCheckInsert (subsumes): ";
           print ((Print.expToString (I.Null, (I.EClo (Upi, s)))) ^ "\n"))
        else () in
      let rec lookup =
        function
        | ((G, D, U, s), [], T) ->
            (print
               ((Print.expToString ((concat (G, D)), (I.EClo (U, s)))) ^
                  " call should always be already in the table !\n");
             Repeated)
        | ((G, D, U, s),
           ((k, G', D', U'), { solutions = A; lookup = i; lookup = i })::T,
           T') ->
            if subsumes ((G, D, U), (G', D', U'))
            then
              let (Dk, sk) = A.abstractAnswSub s in
              (if memberSubsumes ((G, Dk, U, sk), (G', U', A))
               then Repeated
               else
                 (let s' = reinstSub (G', D', I.id) in
                  let _ =
                    if (!Global.chatter) >= 4
                    then
                      (print "\n new answer to be added to Index \n";
                       print
                         ((Print.expToString
                             (I.Null, (A.raiseType ((concat (G', D')), U'))))
                            ^ "\n");
                       print "\n answer added \n";
                       print
                         ((Print.expToString
                             (I.Null,
                               (A.raiseType
                                  (Dk, (I.EClo ((A.raiseType (G, U)), sk))))))
                            ^ "\n"))
                    else () in
                  let _ =
                    if
                      Unify.unifiable
                        (Dk, ((A.raiseType (G, U)), sk),
                          ((A.raiseType (G', U')), s'))
                    then
                      (if (!Global.chatter) >= 4
                       then
                         (print "\n1 unification successful !\n";
                          print
                            ((Print.expToString
                                (I.Null,
                                  (A.raiseType
                                     (Dk,
                                       (I.EClo ((A.raiseType (G', U')), s'))))))
                               ^ "\n"))
                       else ())
                    else
                      print
                        "\n1 unification failed! -- should never happen ?" in
                  let (Dk', sk') = A.abstractAnsw (Dk, s') in
                  let rs = reinstSub (G', Dk', I.id) in
                  (match !query with
                   | NONE -> ()
                   | SOME (G1, D1, U1, s1, sc1) ->
                       (if (!Global.chatter) >= 4
                        then
                          (print "Generate answers for: ";
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (I.EClo ((A.raiseType (G1, U1)), s1))))
                                ^ " \n");
                           print "Answer in table: ";
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (A.raiseType
                                      (Dk,
                                        (I.EClo ((A.raiseType (G', U')), s'))))))
                                ^ " : \n");
                           print
                             ((Print.expToString
                                 (I.Null,
                                   (I.EClo
                                      ((A.raiseType
                                          (Dk,
                                            (I.EClo
                                               ((A.raiseType (G', U')), sk')))),
                                        rs))))
                                ^ " : \n"))
                        else ();
                        if subsumes ((G1, D1, U1), (G', D', U'))
                        then
                          CSManager.trail
                            (function
                             | () ->
                                 if
                                   Unify.unifiable
                                     (D1, ((A.raiseType (G1, U1)), s1),
                                       ((I.EClo ((A.raiseType (G', U')), sk')),
                                         rs))
                                 then
                                   let w =
                                     if !strengthen
                                     then
                                       Subordinate.weaken
                                         (I.Null,
                                           (IntSyn.targetFam
                                              (I.EClo (U1, s1))))
                                     else I.id in
                                   sc1 O
                                 else ())
                        else ()));
                  table :=
                    ((rev T') @
                       (((k, G', D', U'),
                          { solutions = (((Dk', sk'), O) :: A); lookup = i })
                          :: T));
                  if (!Global.chatter) >= 5
                  then
                    (print "\n \n solution (original) was: \n";
                     print
                       ((Print.expToString
                           (I.Null, (I.EClo ((A.raiseType (G, U)), s))))
                          ^ "\n");
                     print "\n \n solution (deref) was: \n";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk, (I.EClo ((A.raiseType (G, U)), sk))))))
                          ^ "\n");
                     print "\n solution added  --- ";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk', (I.EClo ((A.raiseType (G', U')), s'))))))
                          ^ "\n");
                     print "\n solution added (dereferenced) --- ";
                     print
                       ((Print.expToString
                           (I.Null,
                             (A.raiseType
                                (Dk', (I.EClo ((A.raiseType (G', U')), sk'))))))
                          ^ "\n"))
                  else ();
                  New))
            else
              lookup
                ((G, D, U, s), T,
                  (((k, G', D', U'), { solutions = A; lookup = i }) :: T')) in
      lookup ((G, D, U, s), (!table), [])
    let rec reset () = table := []
    let rec solutions { solutions = S; lookup = i; lookup = i } = S
    let rec lookup { solutions = S; lookup = i; lookup = i } = i
    let rec noAnswers =
      function
      | [] -> true__
      | (((G', D', U'), answ) as H)::L' ->
          (match List.take ((solutions answ), (lookup answ)) with
           | [] -> noAnswers L'
           | L -> false__)
    let rec callCheck (G, D, U) =
      match !strategy with
      | Variant -> callCheckVariant (G, D, U)
      | Subsumption -> callCheckSubsumes (G, D, U)
    let rec answCheck (G, D, U, s, O) =
      match !strategy with
      | Variant -> answCheckVariant (G, D, U, s, O)
      | Subsumption -> answCheckSubsumes (G, D, U, s, O)
    let rec updateTable () =
      let rec update arg__0 arg__1 arg__2 =
        match (arg__0, arg__1, arg__2) with
        | ([], T, Flag) -> (Flag, T)
        | (((k, G, D, U), { solutions = S; lookup = i; lookup = i })::T, T',
           Flag) ->
            let l = length S in
            if l = i
            then
              update T
                (((k, G, D, U), { solutions = S; lookup = (List.length S) })
                   :: T') Flag
            else
              update T
                (((k, G, D, U), { solutions = S; lookup = (List.length S) })
                   :: T') true__ in
      let (Flag, T) = update (!table) [] false__ in
      let r = Flag || (!added) in added := false__; (:=) table rev T; r
    (* Global Table *)
    (* concat(Gdp, G) = G''
     *
     * if Gdp = ym...y1
     *    G   = xn...x1
     * then
     *    Gdp, G = G''
     *    ym...y1, xn...x1
     *
     *)
    (* ---------------------------------------------------------------------- *)
    (* printTable () = () *)
    (* (print (Print.expToString (I.Null,  *)
    (*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
    (* do not print pskeletons *)
    (* printTableEntries () = () *)
    (* ---------------------------------------------------------------------- *)
    (* Term Abstraction *)
    (* countDepth U =
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
    (* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)
    (* ---------------------------------------------------------------------- *)
    (* variant (U,s) (U',s')) = bool   *)
    (* subsumes ((G, D, U), (G', D', U')) = bool
     *
     * if
     *    D, G   |- U
     *    D', G' |- U'
     * then
     *      G' |- s' : D', G'
     *    return true if D, G |- U is an instance of G' |- U'[s']
     *    otherwise false
     *
     *)
    (* ---------------------------------------------------------------------- *)
    (* Call check and insert *)
    (* callCheck (G, D, U) = callState

       check whether D, G |- U is in the table

     returns NONE,
        if D, G |- U is not already in the table
          Sideeffect: add D, G |- U to table

     returns SOME(A)
        if D, G |- U is in table and
          A is an entry in the table together with its answer list

    Variant:
    if it succeeds there is exactly one table entry which is a variant to U
    Subsumption:
    if it succeeds it will return the most general table entry of which U is
    an instance of (by invariant now, the most general table entry will be found first,
    any entry found later, will be an instance of this entry)
    *)
    (* if termdepth(U) > n then force the tabled engine to suspend
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

      if     G |- U[s]
          D, G |- U
             G |- s : D, G

      answerCheck (G, D, (U,s)) = repeated
         if s already occurs in answer list for U
      answerCheck (G, D, (U,s)) = new
         if s did not occur in answer list for U
         Sideeffect: update answer list for U

        Dk, G |- sk : D, G
        Dk, G |- U[sk]

        sk is the abstraction of s and Dk contains all "free" vars

     *)
    (* cannot happen ! *)
    (* answer check *)
    (* memberSubsumes ((G, Dk, U, sk), (G', U', A)) = bool

   If Dk, G |- U[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for all i in [1, ..., n]
          Di, G' |- U'[si]
              G' |- si' : Di, G'
   then
     exists an i in [1,...,n]  s.t.
         Dk, G |- U[sk] is an instance of G' |- U'[si']
   *)
    (* assume G' and G are the same for now *)
    (* cannot happen ! *)
    (*  higher-order matching *)
    (* reinstantiate us' *)
    (* nothing to do *)
    (* original query is an instance of the entry we are adding answ to *)
    (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
    (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *)
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
