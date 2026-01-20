
module Convert =
  struct
    open Syntax
    exception Convert of string 
    exception NotFound of string 
    let (sigma : string list ref) = ref []
    let (sigmat : class__ list ref) = ref []
    let (sigmap : bool list ref) = ref []
    let rec clear () = sigma := []; sigmat := []; sigmap := []
    let rec findn __0__ __1__ =
      match (__0__, __1__) with
      | ([], v) -> raise (NotFound v)
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
    let rec spine_form __2__ __3__ =
      match (__2__, __3__) with
      | (__G, Id s) ->
          (match findid __G s with
           | Var n -> ((Var n), None, true, [])
           | Const n ->
               ((Const n), (Some (modesofclass (List.nth ((!sigmat), n)))),
                 (List.nth ((!sigmap), n)), []))
      | (__G, App (t, u)) ->
          let (h, mopt, p, s) = spine_form (__G, t) in
          (h, mopt, p, (s @ [u]))
      | (__G, Lam _) -> raise (Convert "illegal redex")
      | (__G, _) -> raise (Convert "level mismatch")
    let rec type_spine_form __4__ __5__ =
      match (__4__, __5__) with
      | (__G, Id s) ->
          let n = findn (!sigma) s in
          (n, (modesofclass (List.nth ((!sigmat), n))), [])
      | (__G, App (t, u)) ->
          let (n, m, s) = type_spine_form (__G, t) in (n, m, (s @ [u]))
      | (__G, _) -> raise (Convert "level mismatch")
    let rec safezip l1 l2 =
      if (=) (length l1) length l2
      then ListPair.zip (l1, l2)
      else raise (Convert "wrong spine length")
    let rec eltconvert __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (__G, t, MINUS) -> Elt (convert (__G, t))
      | (__G, Ascribe (t, a), PLUS) ->
          Ascribe ((nconvert (__G, t)), (typeconvert (__G, a)))
      | (__G, t, PLUS) -> AElt (aconvert (__G, t))
      | (__G, Parse.Omit, OMIT) -> Omit
      | (__G, _, OMIT) -> raise (Convert "found term expected to be omitted")
    let rec aconvert (__G) t =
      match convert (__G, t) with
      | ATerm t' -> t'
      | NTerm _ -> raise (Convert "required atomic, found normal")
    let rec nconvert (__G) t =
      match convert (__G, t) with
      | NTerm t' -> t'
      | ATerm _ -> raise (Convert "required normal, found atomic")
    let rec convert __9__ __10__ =
      match (__9__, __10__) with
      | (__G, Lam ((v, _), t)) -> NTerm (Lam (convert ((v :: __G), t)))
      | (__G, t) ->
          let (h, mopt, p, s) = spine_form (__G, t) in
          let s' =
            map (eltconvert __G)
              (match mopt with
               | None -> map (fun elt -> (elt, MINUS)) s
               | Some m -> safezip (s, m)) in
          if p then ATerm (ARoot (h, s')) else NTerm (NRoot (h, s'))
    let rec typeconvert __11__ __12__ =
      match (__11__, __12__) with
      | (__G, Pi (m, (v, Some t), t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = typeconvert ((v :: __G), t') in
          TPi ((modeconvert m), ct, ct')
      | (__G, Pi (m, (_, None), _)) ->
          raise (Convert "can't handle implicit pi")
      | (__G, Arrow (t, t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = typeconvert (("" :: __G), t') in TPi (MINUS, ct, ct')
      | (__G, PlusArrow (t, t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = typeconvert (("" :: __G), t') in TPi (PLUS, ct, ct')
      | (__G, a) ->
          let (n, m, s) = type_spine_form (__G, a) in
          let s' = map (eltconvert __G) (safezip (s, m)) in TRoot (n, s')
    let rec kindconvert __13__ __14__ =
      match (__13__, __14__) with
      | (__G, Pi (m, (v, Some t), t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = kindconvert ((v :: __G), t') in
          KPi ((modeconvert m), ct, ct')
      | (__G, Arrow (t, t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = kindconvert (("" :: __G), t') in KPi (MINUS, ct, ct')
      | (__G, PlusArrow (t, t')) ->
          let ct = typeconvert (__G, t) in
          let ct' = kindconvert (("" :: __G), t') in KPi (PLUS, ct, ct')
      | (__G, Pi (m, (_, None), _)) ->
          raise (Convert "can't handle implicit pi")
      | (__G, Parse.Type) -> Type
      | _ -> raise (Convert "level mismatch")
  end;;
