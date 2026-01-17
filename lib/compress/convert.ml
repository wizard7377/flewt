
module Convert =
  struct
    open Syntax
    exception Convert of string 
    exception NotFound of string 
    let (sigma : string list ref) = ref []
    let (sigmat : class__ list ref) = ref []
    let (sigmap : bool list ref) = ref []
    let rec clear () = sigma := []; sigmat := []; sigmap := []
    let rec findn arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ([], (v : string)) -> raise (NotFound v)
      | (v::tl, v') -> if v = v' then 0 else (+) 1 findn tl v'
    let rec findid ctx v =
      try Var (findn ctx v) with | NotFound _ -> Const (findn (!sigma) v)
    let rec modeconvert =
      function
      | Parse.mMINUS -> MINUS
      | Parse.mPLUS -> PLUS
      | Parse.mOMIT -> OMIT
    let rec modesofclass =
      function
      | kclass (Type) -> []
      | kclass (KPi (m, _, k)) -> (::) m modesofclass (kclass k)
      | tclass (TRoot _) -> []
      | tclass (TPi (m, _, a)) -> (::) m modesofclass (tclass a)
    let rec spine_form =
      function
      | (((G)(* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)),
         Id s) ->
          (match findid G s with
           | Var n -> ((Var n), NONE, true__, [])
           | Const n ->
               ((Const n), (SOME (modesofclass (List.nth ((!sigmat), n)))),
                 (List.nth ((!sigmap), n)), []))
      | (G, App (t, u)) ->
          let (h, mopt, p, s) = spine_form (G, t) in (h, mopt, p, (s @ [u]))
      | (G, Lam _) -> raise (Convert "illegal redex")
      | (G, _) -> raise (Convert "level mismatch")
    let rec type_spine_form =
      function
      | (((G)(* similar to spine_form for a type family applied to a list of arguments *)),
         Id s) ->
          let n = findn (!sigma) s in
          (n, (modesofclass (List.nth ((!sigmat), n))), [])
      | (G, App (t, u)) ->
          let (n, m, s) = type_spine_form (G, t) in (n, m, (s @ [u]))
      | (G, _) -> raise (Convert "level mismatch")
    let rec safezip (l1, l2) =
      if (=) (length l1) length l2
      then ListPair.zip (l1, l2)
      else raise (Convert "wrong spine length")
    let rec eltconvert arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((G)(* given a context and an external expression and a mode, return a spine element or raise an exception*)),
         (t, MINUS)) -> Elt (convert (G, t))
      | (G, (Ascribe (t, a), PLUS)) ->
          Ascribe ((nconvert (G, t)), (typeconvert (G, a)))
      | (G, (t, PLUS)) -> AElt (aconvert (G, t))
      | (G, (Parse.Omit, OMIT)) -> Omit
      | (G, (_, OMIT)) -> raise (Convert "found term expected to be omitted")
    let rec aconvert
      (((G)(* given a context and an external expression, return an atomic term or raise an exception*)),
       t)
      =
      match convert (G, t) with
      | ATerm t' -> t'
      | NTerm _ -> raise (Convert "required atomic, found normal")
    let rec nconvert
      (((G)(* given a context and an external expression, return a normal term or raise an exception*)),
       t)
      =
      match convert (G, t) with
      | NTerm t' -> t'
      | ATerm _ -> raise (Convert "required normal, found atomic")
    let rec convert =
      function
      | (((G)(* given a context and an external expression, return a term or raise an exception *)),
         Lam ((v, _), t)) -> NTerm (Lam (convert ((v :: G), t)))
      | (G, t) ->
          let (h, mopt, p, s) = spine_form (G, t) in
          let s' =
            map (eltconvert G)
              (match mopt with
               | NONE -> map (function | elt -> (elt, MINUS)) s
               | SOME m -> safezip (s, m)) in
          if p then ATerm (ARoot (h, s')) else NTerm (NRoot (h, s'))
    let rec typeconvert =
      function
      | (((G)(* given a context and an external expression, return a type or raise an exception *)),
         Pi (m, (v, SOME t), t')) ->
          let ct = typeconvert (G, t) in
          let ct' = typeconvert ((v :: G), t') in
          TPi ((modeconvert m), ct, ct')
      | (G, Pi (m, (_, NONE), _)) ->
          raise (Convert "can't handle implicit pi")
      | (G, Arrow (t, t')) ->
          let ct = typeconvert (G, t) in
          let ct' = typeconvert (("" :: G), t') in TPi (MINUS, ct, ct')
      | (G, PlusArrow (t, t')) ->
          let ct = typeconvert (G, t) in
          let ct' = typeconvert (("" :: G), t') in TPi (PLUS, ct, ct')
      | (G, a) ->
          let (n, m, s) = type_spine_form (G, a) in
          let s' = map (eltconvert G) (safezip (s, m)) in TRoot (n, s')
    let rec kindconvert =
      function
      | (((G)(* given a context and an external expression, return a kind or raise an exception *)),
         Pi (m, (v, SOME t), t')) ->
          let ct = typeconvert (G, t) in
          let ct' = kindconvert ((v :: G), t') in
          KPi ((modeconvert m), ct, ct')
      | (G, Arrow (t, t')) ->
          let ct = typeconvert (G, t) in
          let ct' = kindconvert (("" :: G), t') in KPi (MINUS, ct, ct')
      | (G, PlusArrow (t, t')) ->
          let ct = typeconvert (G, t) in
          let ct' = kindconvert (("" :: G), t') in KPi (PLUS, ct, ct')
      | (G, Pi (m, (_, NONE), _)) ->
          raise (Convert "can't handle implicit pi")
      | (G, Parse.Type) -> Type
      | _ -> raise (Convert "level mismatch")
  end;;
