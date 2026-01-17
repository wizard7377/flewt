
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
      | (((g)(* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)),
         Id s) ->
          (match findid g s with
           | Var n -> ((Var n), NONE, true__, [])
           | Const n ->
               ((Const n), (SOME (modesofclass (List.nth ((!sigmat), n)))),
                 (List.nth ((!sigmap), n)), []))
      | (g, App (t, u)) ->
          let (h, mopt, p, s) = spine_form (g, t) in (h, mopt, p, (s @ [u]))
      | (g, Lam _) -> raise (Convert "illegal redex")
      | (g, _) -> raise (Convert "level mismatch")
    let rec type_spine_form =
      function
      | (((g)(* similar to spine_form for a type family applied to a list of arguments *)),
         Id s) ->
          let n = findn (!sigma) s in
          (n, (modesofclass (List.nth ((!sigmat), n))), [])
      | (g, App (t, u)) ->
          let (n, m, s) = type_spine_form (g, t) in (n, m, (s @ [u]))
      | (g, _) -> raise (Convert "level mismatch")
    let rec safezip (l1, l2) =
      if (=) (length l1) length l2
      then ListPair.zip (l1, l2)
      else raise (Convert "wrong spine length")
    let rec eltconvert arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((g)(* given a context and an external expression and a mode, return a spine element or raise an exception*)),
         (t, MINUS)) -> Elt (convert (g, t))
      | (g, (Ascribe (t, a), PLUS)) ->
          Ascribe ((nconvert (g, t)), (typeconvert (g, a)))
      | (g, (t, PLUS)) -> AElt (aconvert (g, t))
      | (g, (Parse.Omit, OMIT)) -> Omit
      | (g, (_, OMIT)) -> raise (Convert "found term expected to be omitted")
    let rec aconvert
      (((g)(* given a context and an external expression, return an atomic term or raise an exception*)),
       t)
      =
      match convert (g, t) with
      | ATerm t' -> t'
      | NTerm _ -> raise (Convert "required atomic, found normal")
    let rec nconvert
      (((g)(* given a context and an external expression, return a normal term or raise an exception*)),
       t)
      =
      match convert (g, t) with
      | NTerm t' -> t'
      | ATerm _ -> raise (Convert "required normal, found atomic")
    let rec convert =
      function
      | (((g)(* given a context and an external expression, return a term or raise an exception *)),
         Lam ((v, _), t)) -> NTerm (Lam (convert ((v :: g), t)))
      | (g, t) ->
          let (h, mopt, p, s) = spine_form (g, t) in
          let s' =
            map (eltconvert g)
              (match mopt with
               | NONE -> map (function | elt -> (elt, MINUS)) s
               | SOME m -> safezip (s, m)) in
          if p then ATerm (ARoot (h, s')) else NTerm (NRoot (h, s'))
    let rec typeconvert =
      function
      | (((g)(* given a context and an external expression, return a type or raise an exception *)),
         Pi (m, (v, SOME t), t')) ->
          let ct = typeconvert (g, t) in
          let ct' = typeconvert ((v :: g), t') in
          TPi ((modeconvert m), ct, ct')
      | (g, Pi (m, (_, NONE), _)) ->
          raise (Convert "can't handle implicit pi")
      | (g, Arrow (t, t')) ->
          let ct = typeconvert (g, t) in
          let ct' = typeconvert (("" :: g), t') in TPi (MINUS, ct, ct')
      | (g, PlusArrow (t, t')) ->
          let ct = typeconvert (g, t) in
          let ct' = typeconvert (("" :: g), t') in TPi (PLUS, ct, ct')
      | (g, a) ->
          let (n, m, s) = type_spine_form (g, a) in
          let s' = map (eltconvert g) (safezip (s, m)) in TRoot (n, s')
    let rec kindconvert =
      function
      | (((g)(* given a context and an external expression, return a kind or raise an exception *)),
         Pi (m, (v, SOME t), t')) ->
          let ct = typeconvert (g, t) in
          let ct' = kindconvert ((v :: g), t') in
          KPi ((modeconvert m), ct, ct')
      | (g, Arrow (t, t')) ->
          let ct = typeconvert (g, t) in
          let ct' = kindconvert (("" :: g), t') in KPi (MINUS, ct, ct')
      | (g, PlusArrow (t, t')) ->
          let ct = typeconvert (g, t) in
          let ct' = kindconvert (("" :: g), t') in KPi (PLUS, ct, ct')
      | (g, Pi (m, (_, NONE), _)) ->
          raise (Convert "can't handle implicit pi")
      | (g, Parse.Type) -> Type
      | _ -> raise (Convert "level mismatch")
  end;;
