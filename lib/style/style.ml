module type STYLECHECK  =
  sig
    exception Error of string 
    val check : unit -> unit
    val checkConDec : IntSyn.cid -> unit
  end


module StyleCheck(StyleCheck:sig
                               module Whnf : WHNF
                               module Index : INDEX
                               module Origins : ORIGINS
                             end) : STYLECHECK =
  struct
    exception Error of string 
    module I = IntSyn
    module P = Paths
    type polarity =
      | Plus 
      | Minus 
    type info =
      | Correct 
      | Incorrect of (string list * string) 
    let rec toggle = begin function | Plus -> Minus | Minus -> Plus end
    let rec wrapMsg (c, occ, msg) err =
      begin match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (err occDec occ))),
              (Origins.linesInfoLookup fileName), msg) end
  let rec denumber =
    begin function
    | [] -> []
    | c::l ->
        let x = ord c in
        let l' = denumber l in
        if ((x >= 65) && (x <= 90)) || ((x >= 97) && (x <= 122))
        then begin c :: l' end else begin l' end end
let rec options =
  begin function | n::[] -> n | n::l -> (n ^ ", ") ^ (options l) end
let rec error c (prefNames, n, occ) err =
  [wrapMsg
     (c, occ,
       (((((^) "Variable naming: expected " options prefNames) ^ " found ") ^
           n)
          ^ "\n")) err]
let rec checkVariablename (n, prefNames) =
  if
    List.exists
      (begin function
       | n' -> (=) (denumber (explode n)) denumber (explode n') end)
    prefNames
  then begin Correct end else begin Incorrect (prefNames, n) end
let rec checkVar =
  begin function
  | (Dec (Some n, v_), pol) ->
      (begin match Names.getNamePref (I.targetFam v_) with
       | None -> Correct
       | Some (prefENames, prefUNames) ->
           (begin match pol with
            | Plus -> checkVariablename (n, prefENames)
            | Minus -> checkVariablename (n, prefUNames) end) end)
  | (Dec (None, v_), pol) -> Correct end
let rec implicitHead =
  begin function
  | BVar k -> 0
  | Const c -> I.constImp c
  | Skonst k -> 0
  | Def d -> I.constImp d
  | NSDef d -> I.constImp d
  | FgnConst _ -> 0 end
let rec checkExp arg__0 arg__1 arg__2 =
  begin match (arg__0, arg__1, arg__2) with
  | (c, ((g_, p_), Uni _, occ), err) -> []
  | (c, ((g_, p_), Lam (d_, u_), occ), err) ->
      checkDec c ((g_, p_), d_, Minus, occ) err
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkExp c ((g'_, p'_), u_, (P.body occ)) err end)
  | (c, ((g_, p_), Root (h_, s_), occ), err) ->
      (@) (checkHead c ((g_, p_), h_, (P.head occ)) err) checkSpine c
        ((g_, p_), 1, (implicitHead h_), s_, (P.body occ)) err
  | (c, ((g_, p_), FgnExp (_, _), occ), err) -> [] end
let rec checkType arg__3 arg__4 arg__5 =
  begin match (arg__3, arg__4, arg__5) with
  | (c, ((g_, p_), Uni _, pol, occ), err) -> []
  | (c, ((g_, p_), Pi ((d_, I.Maybe), v_), pol, occ), err) ->
      checkDec c ((g_, p_), d_, pol, occ) err
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkType c ((g'_, p'_), v_, pol, (P.body occ)) err end)
  | (c, ((g_, p_), Pi ((d_, I.No), v_), pol, occ), err) ->
      checkDec c ((g_, p_), d_, pol, occ) err
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkType c ((g'_, p'_), v_, pol, (P.body occ)) err end)
  | (c, ((g_, p_), Root (h_, s_), pol, occ), err) ->
      (@) (checkHead c ((g_, p_), h_, (P.head occ)) err) checkSpine c
        ((g_, p_), 1, (implicitHead h_), s_, (P.body occ)) err
  | (c, ((g_, p_), FgnExp (_, _), pol, occ), err) -> [] end
let rec checkDecImp ((g_, p_), (Dec (_, v_) as d_), pol) k =
  let i_ = checkVar (d_, pol) in
  k (((I.Decl (g_, d_)), (I.Decl (p_, i_))), [])
let rec checkDec c ((g_, p_), (Dec (_, v_) as d_), pol, occ) err k =
  let i_ = checkVar (d_, pol) in
  let e1_ =
    begin match i_ with
    | Correct -> []
    | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err end in
  let e2_ = checkType c ((g_, p_), v_, (toggle pol), (P.label occ)) err in
  k (((I.Decl (g_, d_)), (I.Decl (p_, i_))), (e1_ @ e2_))
let rec checkHead arg__6 arg__7 arg__8 =
  begin match (arg__6, arg__7, arg__8) with
  | (c, ((g_, p_), BVar k, occ), err) ->
      (begin match I.ctxLookup (p_, k) with
       | Correct -> []
       | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err end)
  | (c, ((g_, p_), Const _, occ), err) -> []
  | (c, ((g_, p_), Skonst k, occ), err) -> []
  | (c, ((g_, p_), Def d, occ), err) -> []
  | (c, ((g_, p_), NSDef d, occ), err) -> []
  | (c, ((g_, p_), FgnConst _, occ), err) -> [] end
let rec checkSpine arg__9 arg__10 arg__11 =
  begin match (arg__9, arg__10, arg__11) with
  | (c, ((g_, p_), n, 0, I.Nil, occ), err) -> []
  | (c, ((g_, p_), n, 0, App (u_, s_), occ), err) ->
      (@) (checkExp c ((g_, p_), u_, (P.arg (n, occ))) err) checkSpine c
        ((g_, p_), (n + 1), 0, s_, occ) err
  | (c, ((g_, p_), n, i, App (u_, s_), occ), err) ->
      checkSpine c ((g_, p_), (n + 1), (i - 1), s_, occ) err end
let rec checkType' arg__12 arg__13 arg__14 =
  begin match (arg__12, arg__13, arg__14) with
  | (c, ((g_, p_), 0, v_, occ), err) ->
      checkType c ((g_, p_), v_, Plus, occ) err
  | (c, ((g_, p_), n, Pi ((d_, I.Maybe), v_), occ), err) ->
      checkDecImp ((g_, p_), d_, Plus)
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkType' c ((g'_, p'_), (n - 1), v_, (P.body occ)) err end) end
let rec checkExp' arg__15 arg__16 arg__17 =
  begin match (arg__15, arg__16, arg__17) with
  | (c, ((g_, p_), Lam (d_, u_), occ), err) ->
      checkDec c ((g_, p_), d_, Plus, occ) err
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkExp' c ((g'_, p'_), u_, (P.body occ)) err end)
  | (c, ((g_, p_), u_, occ), err) -> checkExp c ((g_, p_), u_, occ) err end
let rec checkDef arg__18 arg__19 arg__20 =
  begin match (arg__18, arg__19, arg__20) with
  | (c, ((g_, p_), 0, u_, occ), err) -> checkExp' c ((g_, p_), u_, occ) err
  | (c, ((g_, p_), n, Lam (d_, u_), occ), err) ->
      checkDecImp ((g_, p_), d_, Plus)
        (begin function
         | ((g'_, p'_), l'_) ->
             (@) l'_ checkDef c ((g'_, p'_), (n - 1), u_, (P.body occ)) err end) end
let rec checkConDec arg__21 arg__22 =
  begin match (arg__21, arg__22) with
  | (c, ConDec (_, _, implicit, _, u_, _)) ->
      (begin if !Global.chatter > 3
             then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
       else begin () end;
  checkType' c ((I.Null, I.Null), implicit, u_, P.top) P.occToRegionDec end)
| (c, ConDef (_, _, implicit, u_, v_, I.Type, _)) ->
    (begin if !Global.chatter > 3
           then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
     else begin () end;
(@) (checkType' c ((I.Null, I.Null), implicit, v_, P.top) P.occToRegionDef2)
  checkDef c ((I.Null, I.Null), implicit, u_, P.top) P.occToRegionDef1 end)
| (c, AbbrevDef (_, _, implicit, u_, v_, I.Type)) ->
    (begin if !Global.chatter > 3
           then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
     else begin () end;
checkType' c ((I.Null, I.Null), implicit, v_, P.top) P.occToRegionDef2;
checkDef c ((I.Null, I.Null), implicit, u_, P.top) P.occToRegionDef1 end)
| (c, _) -> [] end(* type level abbreviations ? *)(* type level definitions ? *)
let rec checkAll (c, n) =
  if c <= n
  then begin (@) (checkConDec c (I.sgnLookup c)) checkAll ((c + 1), n) end
  else begin [] end
let rec check () =
  let (n, _) = I.sgnSize () in begin map print (checkAll (0, n)); () end
let checkConDec =
  begin function
  | c -> (begin map print (checkConDec c (I.sgnLookup c)); () end) end
let check = check end



module StyleCheck =
  (StyleCheck)(struct
                      module Whnf = Whnf
                      module Index = Index
                      module Origins = Origins
                    end)