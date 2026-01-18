
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
    (* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)
    let rec spine_form =
      function
      | (__g, Id s) ->
          (match findid __g s with
           | Var n -> ((Var n), None, true__, [])
           | Const n ->
               ((Const n), (Some (modesofclass (List.nth ((!sigmat), n)))),
                 (List.nth ((!sigmap), n)), []))
      | (__g, App (t, u)) ->
          let (h, mopt, p, s) = spine_form (__g, t) in (h, mopt, p, (s @ [u]))
      | (__g, Lam _) -> raise (Convert "illegal redex")
      | (__g, _) -> raise (Convert "level mismatch")
    (* similar to spine_form for a type family applied to a list of arguments *)
    let rec type_spine_form =
      function
      | (__g, Id s) ->
          let n = findn (!sigma) s in
          (n, (modesofclass (List.nth ((!sigmat), n))), [])
      | (__g, App (t, u)) ->
          let (n, m, s) = type_spine_form (__g, t) in (n, m, (s @ [u]))
      | (__g, _) -> raise (Convert "level mismatch")
    let rec safezip (l1, l2) =
      if (=) (length l1) length l2
      then ListPair.zip (l1, l2)
      else raise (Convert "wrong spine length")
    (* given a context and an external expression and a mode, return a spine element or raise an exception*)
    let rec eltconvert arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (__g, (t, MINUS)) -> Elt (convert (__g, t))
      | (__g, (Ascribe (t, a), PLUS)) ->
          Ascribe ((nconvert (__g, t)), (typeconvert (__g, a)))
      | (__g, (t, PLUS)) -> AElt (aconvert (__g, t))
      | (__g, (Parse.Omit, OMIT)) -> Omit
      | (__g, (_, OMIT)) -> raise (Convert "found term expected to be omitted")
    let rec aconvert (__g, t) =
      match convert (__g, t) with
      | ATerm t' -> t'
      | NTerm _ -> raise (Convert "required atomic, found normal")
    let rec nconvert (__g, t) =
      match convert (__g, t) with
      | NTerm t' -> t'
      | ATerm _ -> raise (Convert "required normal, found atomic")
    let rec convert =
      function
      | (__g, Lam ((v, _), t)) -> NTerm (Lam (convert ((v :: __g), t)))
      | (__g, t) ->
          let (h, mopt, p, s) = spine_form (__g, t) in
          let s' =
            map (eltconvert __g)
              (match mopt with
               | None -> map (function | elt -> (elt, MINUS)) s
               | Some m -> safezip (s, m)) in
          if p then ATerm (ARoot (h, s')) else NTerm (NRoot (h, s'))
    let rec typeconvert =
      function
      | (__g, Pi (m, (v, Some t), t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = typeconvert ((v :: __g), t') in
          TPi ((modeconvert m), ct, ct')
      | (__g, Pi (m, (_, None), _)) ->
          raise (Convert "can't handle implicit pi")
      | (__g, Arrow (t, t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = typeconvert (("" :: __g), t') in TPi (MINUS, ct, ct')
      | (__g, PlusArrow (t, t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = typeconvert (("" :: __g), t') in TPi (PLUS, ct, ct')
      | (__g, a) ->
          let (n, m, s) = type_spine_form (__g, a) in
          let s' = map (eltconvert __g) (safezip (s, m)) in TRoot (n, s')
    let rec kindconvert =
      function
      | (__g, Pi (m, (v, Some t), t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = kindconvert ((v :: __g), t') in
          KPi ((modeconvert m), ct, ct')
      | (__g, Arrow (t, t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = kindconvert (("" :: __g), t') in KPi (MINUS, ct, ct')
      | (__g, PlusArrow (t, t')) ->
          let ct = typeconvert (__g, t) in
          let ct' = kindconvert (("" :: __g), t') in KPi (PLUS, ct, ct')
      | (__g, Pi (m, (_, None), _)) ->
          raise (Convert "can't handle implicit pi")
      | (__g, Parse.Type) -> Type
      | _ -> raise (Convert "level mismatch")
  end;;
