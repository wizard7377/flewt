
module type PARSE_TERM  =
  sig
    module ExtSyn : EXTSYN
    val parseQualId' : (string list * Parsing.lexResult) Parsing.parser
    val parseQualIds' : (string list * string) list Parsing.parser
    val parseFreeze' : (string list * string) list Parsing.parser
    val parseSubord' :
      ((string list * string) * (string list * string)) list Parsing.parser
    val parseThaw' : (string list * string) list Parsing.parser
    val parseDeterministic' : (string list * string) list Parsing.parser
    val parseCompile' : (string list * string) list Parsing.parser
    val parseTerm' : ExtSyn.term Parsing.parser
    val parseDec' : (string option * ExtSyn.term option) Parsing.parser
    val parseCtx' : ExtSyn.dec list Parsing.parser
  end;;




module ParseTerm(ParseTerm:sig module ExtSyn' : EXTSYN module Names : NAMES
                           end) : PARSE_TERM =
  struct
    module ExtSyn = ExtSyn'
    module L = Lexer
    module LS = Lexer.Stream
    module FX = Names.Fixity
    type 'a operator =
      | Atom of 'a 
      | Infix of ((FX.precedence * FX.associativity) * ('a -> 'a -> 'a)) 
      | Prefix of (FX.precedence * ('a -> 'a)) 
      | Postfix of (FX.precedence * ('a -> 'a)) 
    let juxOp = Infix (((FX.inc FX.maxPrec), FX.Left), ExtSyn.app)
    let arrowOp = Infix (((FX.dec FX.minPrec), FX.Right), ExtSyn.arrow)
    let backArrowOp =
      Infix (((FX.dec FX.minPrec), FX.Left), ExtSyn.backarrow)
    let colonOp =
      Infix (((FX.dec (FX.dec FX.minPrec)), FX.Left), ExtSyn.hastype)
    let rec infixOp infixity tm =
      Infix
        (infixity,
          (fun tm1 -> fun tm2 -> ExtSyn.app ((ExtSyn.app (tm, tm1)), tm2)))
    let rec prefixOp prec tm =
      Prefix (prec, (fun tm1 -> ExtSyn.app (tm, tm1)))
    let rec postfixOp prec tm =
      Postfix (prec, (fun tm1 -> ExtSyn.app (tm, tm1)))
    let rec idToTerm __0__ __1__ __2__ __3__ =
      match (__0__, __1__, __2__, __3__) with
      | (L.Lower, ids, name, r) -> ExtSyn.lcid (ids, name, r)
      | (L.Upper, ids, name, r) -> ExtSyn.ucid (ids, name, r)
      | (L.Quoted, ids, name, r) -> ExtSyn.quid (ids, name, r)
    let rec isQuoted = function | L.Quoted -> true | _ -> false
    type nonrec stack = ExtSyn.term operator list
    type nonrec opr = ExtSyn.term operator
    module P :
      sig
        val reduce : stack -> stack
        val reduceAll : Paths.region -> stack -> ExtSyn.term
        val shiftAtom : ExtSyn.term -> stack -> stack
        val shift : Paths.region -> opr -> stack -> stack
        val resolve : Paths.region -> opr -> stack -> stack
      end =
      struct
        let rec reduce =
          function
          | (Atom tm2)::(Infix (_, con))::(Atom tm1)::p' ->
              (Atom (con (tm1, tm2))) :: p'
          | (Atom tm)::(Prefix (_, con))::p' -> (Atom (con tm)) :: p'
          | (Postfix (_, con))::(Atom tm)::p' -> (Atom (con tm)) :: p'
        let rec reduceRec =
          function | (Atom e)::nil -> e | p -> reduceRec (reduce p)
        let rec reduceAll __4__ __5__ =
          match (__4__, __5__) with
          | (r, (Atom e)::nil) -> e
          | (r, (Infix _)::p') ->
              Parsing.error (r, "Incomplete infix expression")
          | (r, (Prefix _)::p') ->
              Parsing.error (r, "Incomplete prefix expression")
          | (r, nil) -> Parsing.error (r, "Empty expression")
          | (r, p) -> reduceRec (reduce p)
        let rec shiftAtom __6__ __7__ =
          match (__6__, __7__) with
          | (tm, ((Atom _)::p' as p)) -> reduce (((Atom tm) :: juxOp) :: p)
          | (tm, p) -> (Atom tm) :: p(* juxtaposition binds most strongly *)
          (* insert juxOp operator and reduce *)
        let rec shift __8__ __9__ __10__ =
          match (__8__, __9__, __10__) with
          | (r, (Atom _ as opr), ((Atom _)::p' as p)) ->
              reduce ((opr :: juxOp) :: p)
          | (r, Infix _, (Infix _)::p') ->
              Parsing.error (r, "Consective infix operators")
          | (r, Infix _, (Prefix _)::p') ->
              Parsing.error (r, "Infix operator following prefix operator")
          | (r, Infix _, nil) -> Parsing.error (r, "Leading infix operator")
          | (r, (Prefix _ as opr), ((Atom _)::p' as p)) ->
              (opr :: juxOp) :: p
          | (r, Postfix _, (Infix _)::p') ->
              Parsing.error (r, "Postfix operator following infix operator")
          | (r, Postfix _, (Prefix _)::p') ->
              Parsing.error (r, "Postfix operator following prefix operator")
          | (r, Postfix _, nil) ->
              Parsing.error (r, "Leading postfix operator")
          | (r, opr, p) -> opr :: p(* Postfix/Postfix cannot arise *)
          (* Postfix/Atom: shift, reduced immediately *)
          (* Prefix/Postfix cannot arise *)(* Prefix/{Infix,Prefix,Empty}: shift *)
          (* will be reduced later *)(* insert juxtaposition operator *)
          (* Infix/Postfix cannot arise *)(* Infix/Atom: shift *)
          (* Atom/Empty: shift *)(* Atom/Postfix cannot arise *)
          (* Atom/Prefix: shift *)(* Atom/Infix: shift *)
          (* juxtaposition binds most strongly *)(* insert juxOp operator and reduce *)
        let rec resolve __11__ __12__ __13__ =
          match (__11__, __12__, __13__) with
          | (r, (Infix ((prec, assoc), _) as opr),
             ((Atom _)::(Infix ((prec', assoc'), _))::p' as p)) ->
              (match ((FX.compare (prec, prec')), assoc, assoc') with
               | (GREATER, _, _) -> shift (r, opr, p)
               | (LESS, _, _) -> resolve (r, opr, (reduce p))
               | (EQUAL, FX.Left, FX.Left) -> resolve (r, opr, (reduce p))
               | (EQUAL, FX.Right, FX.Right) -> shift (r, opr, p)
               | _ ->
                   Parsing.error
                     (r,
                       "Ambiguous: infix following infix of identical precedence"))
          | (r, (Infix ((prec, assoc), _) as opr),
             ((Atom _)::(Prefix (prec', _))::p' as p)) ->
              (match FX.compare (prec, prec') with
               | GREATER -> shift (r, opr, p)
               | LESS -> resolve (r, opr, (reduce p))
               | EQUAL ->
                   Parsing.error
                     (r,
                       "Ambiguous: infix following prefix of identical precedence"))
          | (r, (Prefix _ as opr), p) -> shift (r, opr, p)
          | (r, (Postfix (prec, _) as opr),
             ((Atom _)::(Prefix (prec', _))::p' as p)) ->
              (match FX.compare (prec, prec') with
               | GREATER -> reduce (shift (r, opr, p))
               | LESS -> resolve (r, opr, (reduce p))
               | EQUAL ->
                   Parsing.error
                     (r,
                       "Ambiguous: postfix following prefix of identical precedence"))
          | (r, (Postfix (prec, _) as opr),
             ((Atom _)::(Infix ((prec', _), _))::p' as p)) ->
              (match FX.compare (prec, prec') with
               | GREATER -> reduce (shift (r, opr, p))
               | LESS -> resolve (r, opr, (reduce p))
               | EQUAL ->
                   Parsing.error
                     (r,
                       "Ambiguous: postfix following infix of identical precedence"))
          | (r, (Postfix _ as opr), ((Atom _)::nil as p)) ->
              reduce (shift (r, opr, p))
          | (r, opr, p) -> shift (r, opr, p)(* default is shift *)
          (* always reduce postfix *)(* always reduce postfix, possibly after prior reduction *)
          (* always shift prefix *)(* infix/atom/<empty>: shift *)
          (* infix/atom/postfix cannot arise *)(* infix/atom/atom cannot arise *)
      end 
    let rec parseQualId' (Cons (((ID (_, id) as t), r), s') as f) =
      match LS.expose s' with
      | Cons ((L.PATHSEP, _), s'') ->
          let ((ids, (t, r)), f') = parseQualId' (LS.expose s'') in
          (((id :: ids), (t, r)), f')
      | f' -> ((nil, (t, r)), f')
    let rec stripBar =
      function
      | Cons ((ID (_, "|"), r), s') -> LS.expose s'
      | Cons ((L.RPAREN, r), s') as f -> f
      | Cons ((t, r), s') ->
          Parsing.error (r, ((^) "Expected `|', found token " L.toString t))
    let rec parseQualIds1 __14__ __15__ =
      match (__14__, __15__) with
      | (ls, (Cons (((ID (_, id) as t), r0), s') as f)) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          let r = Paths.join (r0, r1) in
          let f'' = stripBar f' in parseQualIds1 (((ids, name) :: ls), f'')
      | (ls, Cons ((L.RPAREN, r), s')) -> (ls, (LS.expose s'))
      | (ls, Cons ((t, r), s)) ->
          Parsing.error
            (r, ((^) "Expected label, found token " L.toString t))
    let rec parseQualIds' =
      function
      | Cons ((L.LPAREN, r), s') -> parseQualIds1 (nil, (LS.expose s'))
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected list of labels, found token " L.toString t))
    let rec stripRParen =
      function
      | Cons ((L.RPAREN, r), s') -> LS.expose s'
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected closing `)', found " L.toString t))(* t = `.' or ? *)
    let rec parseSubordPair2 __16__ __17__ =
      match (__16__, __17__) with
      | ((Cons ((ID _, _), _) as f), qid) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          ((qid, (ids, name)), (stripRParen f'))
      | (Cons ((t, r), s'), qid) ->
          Parsing.error
            (r, ((^) "Expected identifier, found token " L.toString t))
    let rec parseSubordPair1 =
      function
      | Cons ((ID _, _), _) as f ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          parseSubordPair2 (f', (ids, name))
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected identifier, found token " L.toString t))
    let rec parseSubord' __18__ __19__ =
      match (__18__, __19__) with
      | (Cons ((L.LPAREN, r), s'), qidpairs) ->
          let (qidpair, f) = parseSubordPair1 (LS.expose s') in
          parseSubord' (f, (qidpair :: qidpairs))
      | ((Cons ((L.DOT, _), _) as f), qidpairs) -> ((List.rev qidpairs), f)
      | (Cons ((t, r), s'), qidpairs) ->
          Parsing.error
            (r,
              ((^) "Expected a pair of identifiers, found token " L.toString
                 t))
    let rec parseFreeze' __20__ __21__ =
      match (__20__, __21__) with
      | ((Cons ((ID _, _), _) as f), qids) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          parseFreeze' (f', ((ids, name) :: qids))
      | ((Cons ((L.DOT, _), _) as f), qids) -> ((List.rev qids), f)
      | (Cons ((t, r), s'), qids) ->
          Parsing.error
            (r, ((^) "Expected identifier, found token " L.toString t))
    let rec parseThaw' f qids = parseFreeze' (f, qids)(* same syntax as %freeze *)
    let rec parseDeterministic' __22__ __23__ =
      match (__22__, __23__) with
      | ((Cons ((ID _, _), _) as f), qids) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          parseDeterministic' (f', ((ids, name) :: qids))
      | ((Cons ((L.DOT, _), _) as f), qids) -> ((List.rev qids), f)
      | (Cons ((t, r), s'), qids) ->
          Parsing.error
            (r, ((^) "Expected identifier, found token " L.toString t))
    let rec parseCompile' __24__ __25__ =
      match (__24__, __25__) with
      | ((Cons ((ID _, _), _) as f), qids) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          parseCompile' (f', ((ids, name) :: qids))
      | ((Cons ((L.DOT, _), _) as f), qids) -> ((List.rev qids), f)
      | (Cons ((t, r), s'), qids) ->
          Parsing.error
            (r, ((^) "Expected identifier, found token " L.toString t))
    let rec parseExp s p = parseExp' ((LS.expose s), p)
    let rec parseExp' __26__ __27__ =
      match (__26__, __27__) with
      | ((Cons ((ID _, r0), _) as f), p) ->
          let ((ids, (ID (idCase, name), r1)), f') = parseQualId' f in
          let r = Paths.join (r0, r1) in
          let tm = idToTerm (idCase, ids, name, r) in
          ((if isQuoted idCase
            then parseExp' (f', (P.shiftAtom (tm, p)))
            else
              (match Names.fixityLookup (Names.Qid (ids, name)) with
               | FX.Nonfix -> parseExp' (f', (P.shiftAtom (tm, p)))
               | Infix infixity ->
                   parseExp'
                     (f', (P.resolve (r, (infixOp (infixity, tm)), p)))
               | Prefix prec ->
                   parseExp' (f', (P.resolve (r, (prefixOp (prec, tm)), p)))
               | Postfix prec ->
                   parseExp' (f', (P.resolve (r, (postfixOp (prec, tm)), p)))))
            (* Currently, we cannot override fixity status of identifiers *)
            (* Thus isQuoted always returns false *))
      | (Cons ((L.UNDERSCORE, r), s), p) ->
          parseExp (s, (P.shiftAtom ((ExtSyn.omitted r), p)))
      | (Cons ((L.TYPE, r), s), p) ->
          parseExp (s, (P.shiftAtom ((ExtSyn.typ r), p)))
      | (Cons ((L.COLON, r), s), p) ->
          parseExp (s, (P.resolve (r, colonOp, p)))
      | (Cons ((L.BACKARROW, r), s), p) ->
          parseExp (s, (P.resolve (r, backArrowOp, p)))
      | (Cons ((L.ARROW, r), s), p) ->
          parseExp (s, (P.resolve (r, arrowOp, p)))
      | (Cons ((L.LPAREN, r), s), p) ->
          decideRParen (r, (parseExp (s, nil)), p)
      | ((Cons ((L.RPAREN, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | (Cons ((L.LBRACE, r), s), p) -> decideRBrace (r, (parseDec s), p)
      | ((Cons ((L.RBRACE, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | (Cons ((L.LBRACKET, r), s), p) -> decideRBracket (r, (parseDec s), p)
      | ((Cons ((L.RBRACKET, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | ((Cons ((L.EQUAL, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | ((Cons ((L.DOT, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | ((Cons ((L.EOF, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | ((Cons ((L.SOLVE, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | ((Cons ((L.DEFINE, r), s) as f), p) -> ((P.reduceAll (r, p)), f)
      | (Cons ((STRING str, r), s), p) ->
          parseExp (s, (P.shiftAtom ((ExtSyn.scon (str, r)), p)))
      | (Cons ((t, r), s), p) ->
          Parsing.error
            (r,
              (((^) "Unexpected token " L.toString t) ^
                 " found in expression"))(* possible error recovery: insert DOT *)
      (* for some reason, there's no dot after %define decls -kw *)
    let rec parseDec s = parseDec' (LS.expose s)
    let rec parseDec' =
      function
      | Cons ((ID (L.Quoted, name), r), s') ->
          Parsing.error (r, ("Illegal bound quoted identifier " ^ name))
      | Cons ((ID (idCase, name), r), s') ->
          (match Names.fixityLookup (Names.Qid (nil, name)) with
           | FX.Nonfix -> parseDec1 ((Some name), (LS.expose s'))
           | Infix _ ->
               Parsing.error (r, ("Cannot bind infix identifier " ^ name))
           | Prefix _ ->
               Parsing.error (r, ("Cannot bind prefix identifier " ^ name))
           | Postfix _ ->
               Parsing.error (r, ("Cannot bind postfix identifier " ^ name)))
      | Cons ((L.UNDERSCORE, r), s') -> parseDec1 (None, (LS.expose s'))
      | Cons ((L.EOF, r), s') ->
          Parsing.error (r, "Unexpected end of stream in declaration")
      | Cons ((t, r), s') ->
          Parsing.error
            (r, ((^) "Expected variable name, found token " L.toString t))
      (* cannot happen at present *)
    let rec parseDec1 __28__ __29__ =
      match (__28__, __29__) with
      | (x, Cons ((L.COLON, r), s')) ->
          let (tm, f'') = parseExp (s', nil) in ((x, (Some tm)), f'')
      | (x, (Cons ((L.RBRACE, _), _) as f)) -> ((x, None), f)
      | (x, (Cons ((L.RBRACKET, _), _) as f)) -> ((x, None), f)
      | (x, Cons ((t, r), s')) ->
          Parsing.error
            (r,
              ((^) "Expected optional type declaration, found token "
                 L.toString t))
    let rec decideRParen __30__ __31__ __32__ =
      match (__30__, __31__, __32__) with
      | (r0, (tm, Cons ((L.RPAREN, r), s)), p) ->
          parseExp (s, (P.shiftAtom (tm, p)))
      | (r0, (tm, Cons ((_, r), s)), p) ->
          Parsing.error ((Paths.join (r0, r)), "Unmatched open parenthesis")
    let rec decideRBrace __33__ __34__ __35__ =
      match (__33__, __34__, __35__) with
      | (r0, ((x, yOpt), Cons ((L.RBRACE, r), s)), p) ->
          let dec =
            match yOpt with
            | None -> ExtSyn.dec0 (x, (Paths.join (r0, r)))
            | Some y -> ExtSyn.dec (x, y, (Paths.join (r0, r))) in
          let (tm, f') = parseExp (s, nil) in
          parseExp' (f', (P.shiftAtom ((ExtSyn.pi (dec, tm)), p)))
      | (r0, (_, Cons ((_, r), s)), p) ->
          Parsing.error ((Paths.join (r0, r)), "Unmatched open brace")
    let rec decideRBracket __36__ __37__ __38__ =
      match (__36__, __37__, __38__) with
      | (r0, ((x, yOpt), Cons ((L.RBRACKET, r), s)), p) ->
          let dec =
            match yOpt with
            | None -> ExtSyn.dec0 (x, (Paths.join (r0, r)))
            | Some y -> ExtSyn.dec (x, y, (Paths.join (r0, r))) in
          let (tm, f') = parseExp (s, nil) in
          parseExp' (f', (P.shiftAtom ((ExtSyn.lam (dec, tm)), p)))
      | (r0, (dec, Cons ((_, r), s)), p) ->
          Parsing.error ((Paths.join (r0, r)), "Unmatched open bracket")
    let rec stripRBrace =
      function
      | Cons ((L.RBRACE, r), s') -> ((LS.expose s'), r)
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `}', found " L.toString t))
    let rec parseBracedDec r f =
      let ((x, yOpt), f') = parseDec' f in
      let (f'', r2) = stripRBrace f' in
      let d =
        match yOpt with
        | None -> ExtSyn.dec0 (x, (Paths.join (r, r2)))
        | Some y -> ExtSyn.dec (x, y, (Paths.join (r, r2))) in
      (d, f'')
    let rec parseCtx __39__ __40__ __41__ =
      match (__39__, __40__, __41__) with
      | (b, ds, Cons (((L.LBRACE, r), s') as BS)) ->
          let (d, f') = parseBracedDec (r, (LS.expose s')) in
          parseCtx (false, (d :: ds), f')
      | (b, ds, (Cons ((t, r), s') as f)) ->
          if b
          then Parsing.error (r, ((^) "Expected `{', found " L.toString t))
          else (ds, f)
    let parseQualId' = parseQualId'
    let parseQualIds' = parseQualIds'
    let parseSubord' f = parseSubord' (f, nil)
    let parseFreeze' f = parseFreeze' (f, nil)
    let parseThaw' f = parseThaw' (f, nil)
    let parseDeterministic' f = parseDeterministic' (f, nil)
    let parseCompile' f = parseCompile' (f, nil)
    let parseTerm' f = parseExp' (f, nil)
    let parseDec' = parseDec'
    let parseCtx' f = parseCtx (true, nil, f)
  end ;;
