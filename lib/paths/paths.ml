module type PATHS  =
  sig
    type region =
      | Reg of (int * int) 
    type location =
      | Loc of (string * region) 
    type nonrec linesInfo
    val resetLines : unit -> unit
    val newLine : int -> unit
    val getLinesInfo : unit -> linesInfo
    val join : (region * region) -> region
    val toString : region -> string
    val wrap : (region * string) -> string
    val wrapLoc : (location * string) -> string
    val wrapLoc' : (location * linesInfo option * string) -> string
    type path_ =
      | Label of path_ 
      | Body of path_ 
      | Head 
      | Arg of (int * path_) 
      | Here 
    type nonrec occ
    val top : occ
    val label : occ -> occ
    val body : occ -> occ
    val head : occ -> occ
    val arg : (int * occ) -> occ
    type nonrec occExp
    and occSpine
    val leaf : region -> occExp
    val bind : (region * occExp option * occExp) -> occExp
    val root : (region * occExp * int * int * occSpine) -> occExp
    val app : (occExp * occSpine) -> occSpine
    val nils : occSpine
    type nonrec occConDec
    val dec : (int * occExp) -> occConDec
    val def : (int * occExp * occExp option) -> occConDec
    val toRegion : occExp -> region
    val toRegionSpine : (occSpine * region) -> region
    val posToPath : occExp -> int -> path_
    val occToRegionExp : occExp -> occ -> region
    val occToRegionDec : occConDec -> occ -> region
    val occToRegionDef1 : occConDec -> occ -> region
    val occToRegionDef2 : occConDec -> occ -> region
    val occToRegionClause : occConDec -> occ -> region
  end


module Paths() : PATHS =
  struct
    type nonrec pos = int
    type region =
      | Reg of (pos * pos) 
    type location =
      | Loc of (string * region) 
    type nonrec linesInfo = pos list
    let rec posToLineCol' (linesInfo, i) =
      let rec ptlc =
        begin function
        | j::js -> if i >= j then begin ((List.length js), (i - j)) end
            else begin ptlc js end
        | [] -> (0, i) end(* nil means first "line" was not terminated by <newline> *)
    (* first line should start at 0 *) in
  ptlc linesInfo
let linePosList = (ref [] : pos list ref)
let rec resetLines () = linePosList := []
let rec newLine i = (linePosList := i) :: !linePosList
let rec getLinesInfo () = !linePosList
let rec posToLineCol i = posToLineCol' (!linePosList, i)
let rec join (Reg (i1, j1), Reg (i2, j2)) =
  Reg ((Int.min (i1, i2)), (Int.max (j1, j2)))
let rec posInRegion (k, Reg (i, j)) = (i <= k) && (k <= j)
let rec lineColToString (line, col) =
  (^) ((Int.toString (line + 1)) ^ ".") Int.toString (col + 1)
let rec toString (Reg (i, j)) =
  (^) ((lineColToString (posToLineCol i)) ^ "-") lineColToString
    (posToLineCol j)
let rec wrap (r, msg) = ((toString r) ^ " Error: \n") ^ msg
let rec wrapLoc0 (Loc (filename, Reg (i, j)), msg) =
  ((((^) (((^) (filename ^ ":") Int.toString (i + 1)) ^ "-") Int.toString
       (j + 1))
      ^ " ")
     ^ "Error: \n")
    ^ msg
let rec wrapLoc' =
  begin function
  | (Loc (filename, Reg (i, j)), Some linesInfo, msg) ->
      let lcfrom = posToLineCol' (linesInfo, i) in
      let lcto = posToLineCol' (linesInfo, j) in
      let regString =
        (^) ((lineColToString lcfrom) ^ "-") lineColToString lcto in
      ((((filename ^ ":") ^ regString) ^ " ") ^ "Error: \n") ^ msg
  | (loc, None, msg) -> wrapLoc0 (loc, msg) end
let rec wrapLoc (loc, msg) = wrapLoc' (loc, (Some (getLinesInfo ())), msg)
type path_ =
  | Label of path_ 
  | Body of path_ 
  | Head 
  | Arg of (int * path_) 
  | Here 
type occ =
  | top [@sml.renamed "top"][@sml.renamed "top"]
  | label of occ [@sml.renamed "label"][@sml.renamed "label"]
  | body of occ [@sml.renamed "body"][@sml.renamed "body"]
  | head of occ [@sml.renamed "head"][@sml.renamed "head"]
  | arg of (int * occ) [@sml.renamed "arg"][@sml.renamed "arg"]
type occExp =
  | leaf of region [@sml.renamed "leaf"][@sml.renamed "leaf"]
  | bind of (region * occExp option * occExp)
  [@sml.renamed "bind"][@sml.renamed "bind"]
  | root of (region * occExp * int * int * occSpine)
  [@sml.renamed "root"][@sml.renamed "root"]
and occSpine =
  | app of (occExp * occSpine) [@sml.renamed "app"][@sml.renamed "app"]
  | nils [@sml.renamed "nils"][@sml.renamed "nils"]
let rec occToPath =
  begin function
  | (top, path) -> path
  | (label occ, path) -> occToPath (occ, (Label path))
  | (body occ, path) -> occToPath (occ, (Body path))
  | (head occ, path) -> occToPath (occ, Head)
  | (arg (n, occ), path) -> occToPath (occ, (Arg (n, path))) end(* path = Here by invariant *)
type occConDec =
  | dec of (int * occExp) [@sml.renamed "dec"][@sml.renamed "dec"]
  | def of (int * occExp * occExp option)
  [@sml.renamed "def"][@sml.renamed "def"]
let rec posToPath u k =
  let rec inside =
    begin function
    | leaf r -> posInRegion (k, r)
    | bind (r, _, _) -> posInRegion (k, r)
    | root (r, _, _, _, _) -> posInRegion (k, r) end in
let rec toPath =
  begin function
  | leaf (Reg (i, j)) -> Here
  | bind (Reg (i, j), None, u) -> if inside u then begin Body (toPath u) end
      else begin Here end
| bind (Reg (i, j), Some u1, u2) ->
    if inside u1 then begin Label (toPath u1) end
    else begin if inside u2 then begin Body (toPath u2) end
      else begin Here end end
| root (Reg (i, j), h, imp, actual, s) -> if inside h then begin Head end
    else begin
      (begin match toPathSpine (s, 1) with
       | None -> Here
       | Some (n, path) -> Arg ((n + imp), path) end) end end(* check? mark? *)
and toPathSpine =
  begin function
  | (nils, n) -> None
  | (app (u, s), n) -> if inside u then begin Some (n, (toPath u)) end
      else begin toPathSpine (s, (n + 1)) end end in ((toPath u)
(* local functions refer to k but not u *)(* in some situations, whitespace after subexpressions *)
(* might give a larger term than anticipated *))
let rec toRegion =
  begin function
  | leaf r -> r
  | bind (r, _, _) -> r
  | root (r, _, _, _, _) -> r end
let rec toRegionSpine =
  begin function
  | (nils, r) -> r
  | (app (u, s), r) -> join ((toRegion u), (toRegionSpine (s, r))) end
let rec pathToRegion =
  begin function
  | (u, Here) -> toRegion u
  | (bind (r, None, u), Label path) -> r
  | (bind (r, Some u1, u2), Label path) -> pathToRegion (u1, path)
  | (bind (r, _, u), Body path) -> pathToRegion (u, path)
  | (root (r, _, _, _, _), Label path) -> r
  | ((root _ as u), Body path) -> pathToRegion (u, path)
  | (root (r, h, imp, actual, s), Head) -> toRegion h
  | (root (r, h, imp, actual, s), Arg (n, path)) ->
      ((if n <= imp then begin toRegion h end
      else begin ((if (n - imp) > actual then begin r end
        else begin pathToRegionSpine (s, (n - imp), path) end)
  (* addressing argument created by eta expansion
                approximate by the whole root *)) end)
(* addressing implicit argument returns region of head *))
| (leaf r, _) -> r end(* bypassing binder introduced as the result of eta expansion *)
(* addressing binder introduced as the result of eta expansion
           approximate as the eta-expanded root *)
(* addressing implicit type label returns region of binder and its scope *)
let rec pathToRegionSpine =
  begin function
  | (app (u, s), 1, path) -> pathToRegion (u, path)
  | (app (u, s), n, path) -> pathToRegionSpine (s, (n - 1), path) end
let rec occToRegionExp u occ = pathToRegion (u, (occToPath (occ, Here)))
let rec skipImplicit =
  begin function
  | (0, path) -> path
  | (n, Body path) -> skipImplicit ((n - 1), path)
  | (n, Label path) -> Here
  | (n, Here) -> Here end(* addressing body including implicit arguments: approximate by body *)
(* implicit argument: approximate as best possible *)
let rec occToRegionDec (dec (n, v)) occ =
  pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
let rec occToRegionDef1 (def (n, u, vOpt)) occ =
  pathToRegion (u, (skipImplicit (n, (occToPath (occ, Here)))))
let rec occToRegionDef2 arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (def (n, u, Some v), occ) ->
      pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
  | (def (n, u, None), occ) -> pathToRegion (u, Here) end
let rec occToRegionClause arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | ((dec _ as d), occ) -> occToRegionDec d occ
  | ((def _ as d), occ) -> occToRegionDef2 d occ end end 
module Paths = (Paths)(struct  end)


module Origins =
  (Origins)(struct
                   module Global = Global
                   module Table = StringHashTable
                 end)