module Convert =
  struct
    open Syntax
    exception Convert of string 
    exception NotFound of string 
    let (sigma : string list ref) = ref []
    let (sigmat : class_ list ref) = ref []
    let (sigmap : bool list ref) = ref []
    let rec clear () = begin sigma := []; sigmat := []; sigmap := [] end
    let rec findn arg__0 arg__1 =
      begin match (arg__0, arg__1) with
      | ([], (v : string)) -> raise (NotFound v)
      | (v::tl, v') -> if v = v' then begin 0 end
          else begin (+) 1 findn tl v' end end
let rec findid ctx v =
  begin try Var (findn ctx v) with | NotFound _ -> Const (findn !sigma v) end
let rec modeconvert =
  begin function
  | Parse.mMINUS -> MINUS
  | Parse.mPLUS -> PLUS
  | Parse.mOMIT -> OMIT end
let rec modesofclass =
  begin function
  | kclass (Type) -> []
  | kclass (KPi (m, _, k)) -> (::) m modesofclass (kclass k)
  | tclass (TRoot _) -> []
  | tclass (TPi (m, _, a)) -> (::) m modesofclass (tclass a) end
let rec spine_form =
  begin function
  | (g_, Id s) ->
      (begin match findid g_ s with
       | Var n -> ((Var n), None, true, [])
       | Const n ->
           ((Const n), (Some (modesofclass (List.nth (!sigmat, n)))),
             (List.nth (!sigmap, n)), []) end)
  | (g_, App (t, u)) ->
      let (h, mopt, p, s) = spine_form (g_, t) in (h, mopt, p, (s @ [u]))
  | (g_, Lam _) -> raise (Convert "illegal redex")
  | (g_, _) -> raise (Convert "level mismatch") end
let rec type_spine_form =
  begin function
  | (g_, Id s) ->
      let n = findn !sigma s in
      (n, (modesofclass (List.nth (!sigmat, n))), [])
  | (g_, App (t, u)) ->
      let (n, m, s) = type_spine_form (g_, t) in (n, m, (s @ [u]))
  | (g_, _) -> raise (Convert "level mismatch") end
let rec safezip (l1, l2) =
  if (=) (length l1) length l2 then begin ListPair.zip (l1, l2) end
  else begin raise (Convert "wrong spine length") end
let rec eltconvert arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (g_, (t, MINUS)) -> Elt (convert (g_, t))
  | (g_, (Ascribe (t, a), PLUS)) ->
      Ascribe ((nconvert (g_, t)), (typeconvert (g_, a)))
  | (g_, (t, PLUS)) -> AElt (aconvert (g_, t))
  | (g_, (Parse.Omit, OMIT)) -> Omit
  | (g_, (_, OMIT)) -> raise (Convert "found term expected to be omitted") end
let rec aconvert (g_, t) =
  begin match convert (g_, t) with
  | ATerm t' -> t'
  | NTerm _ -> raise (Convert "required atomic, found normal") end
let rec nconvert (g_, t) =
  begin match convert (g_, t) with
  | NTerm t' -> t'
  | ATerm _ -> raise (Convert "required normal, found atomic") end
let rec convert =
  begin function
  | (g_, Lam ((v, _), t)) -> NTerm (Lam (convert ((v :: g_), t)))
  | (g_, t) ->
      let (h, mopt, p, s) = spine_form (g_, t) in
      let s' =
        map (eltconvert g_)
          (begin match mopt with
           | None -> map (begin function | elt -> (elt, MINUS) end) s
          | Some m -> safezip (s, m) end) in
    if p then begin ATerm (ARoot (h, s')) end
      else begin NTerm (NRoot (h, s')) end end
let rec typeconvert =
  begin function
  | (g_, Pi (m, (v, Some t), t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = typeconvert ((v :: g_), t') in TPi ((modeconvert m), ct, ct')
  | (g_, Pi (m, (_, None), _)) -> raise (Convert "can't handle implicit pi")
  | (g_, Arrow (t, t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = typeconvert (("" :: g_), t') in TPi (MINUS, ct, ct')
  | (g_, PlusArrow (t, t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = typeconvert (("" :: g_), t') in TPi (PLUS, ct, ct')
  | (g_, a) ->
      let (n, m, s) = type_spine_form (g_, a) in
      let s' = map (eltconvert g_) (safezip (s, m)) in TRoot (n, s') end
let rec kindconvert =
  begin function
  | (g_, Pi (m, (v, Some t), t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = kindconvert ((v :: g_), t') in KPi ((modeconvert m), ct, ct')
  | (g_, Arrow (t, t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = kindconvert (("" :: g_), t') in KPi (MINUS, ct, ct')
  | (g_, PlusArrow (t, t')) ->
      let ct = typeconvert (g_, t) in
      let ct' = kindconvert (("" :: g_), t') in KPi (PLUS, ct, ct')
  | (g_, Pi (m, (_, None), _)) -> raise (Convert "can't handle implicit pi")
  | (g_, Parse.Type) -> Type
  | _ -> raise (Convert "level mismatch") end
end