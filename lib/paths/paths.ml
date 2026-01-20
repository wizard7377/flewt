
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
    val join : region -> region -> region
    val toString : region -> string
    val wrap : region -> string -> string
    val wrapLoc : location -> string -> string
    val wrapLoc' : location -> linesInfo option -> string -> string
    type __Path =
      | Label of __Path 
      | Body of __Path 
      | Head 
      | Arg of (int * __Path) 
      | Here 
    type nonrec occ
    val top : occ
    val label : occ -> occ
    val body : occ -> occ
    val head : occ -> occ
    val arg : int -> occ -> occ
    type nonrec occExp
    and occSpine
    val leaf : region -> occExp
    val bind : region -> occExp option -> occExp -> occExp
    val root : region -> occExp -> int -> int -> occSpine -> occExp
    val app : occExp -> occSpine -> occSpine
    val nils : occSpine
    type nonrec occConDec
    val dec : int -> occExp -> occConDec
    val def : int -> occExp -> occExp option -> occConDec
    val toRegion : occExp -> region
    val toRegionSpine : occSpine -> region -> region
    val posToPath : occExp -> int -> __Path
    val occToRegionExp : occExp -> occ -> region
    val occToRegionDec : occConDec -> occ -> region
    val occToRegionDef1 : occConDec -> occ -> region
    val occToRegionDef2 : occConDec -> occ -> region
    val occToRegionClause : occConDec -> occ -> region
  end;;




module Paths() : PATHS =
  struct
    type nonrec pos = int
    type region =
      | Reg of (pos * pos) 
    type location =
      | Loc of (string * region) 
    type nonrec linesInfo = pos list
    let rec posToLineCol' linesInfo i =
      let rec ptlc =
        function
        | j::js -> if i >= j then ((List.length js), (i - j)) else ptlc js
        | nil -> (0, i)(* nil means first "line" was not terminated by <newline> *)
        (* first line should start at 0 *) in
      ptlc linesInfo
    let linePosList = (ref nil : pos list ref)
    let rec resetLines () = linePosList := nil
    let rec newLine i = (linePosList := i) :: (!linePosList)
    let rec getLinesInfo () = !linePosList
    let rec posToLineCol i = posToLineCol' ((!linePosList), i)
    let rec join (Reg (i1, j1)) (Reg (i2, j2)) =
      Reg ((Int.min (i1, i2)), (Int.max (j1, j2)))
    let rec posInRegion k (Reg (i, j)) = (i <= k) && (k <= j)
    let rec lineColToString line col =
      (^) ((Int.toString (line + 1)) ^ ".") Int.toString (col + 1)
    let rec toString (Reg (i, j)) =
      (^) ((lineColToString (posToLineCol i)) ^ "-") lineColToString
        (posToLineCol j)
    let rec wrap r msg = ((toString r) ^ " Error: \n") ^ msg
    let rec wrapLoc0 (Loc (filename, Reg (i, j))) msg =
      ((((^) (((^) (filename ^ ":") Int.toString (i + 1)) ^ "-") Int.toString
           (j + 1))
          ^ " ")
         ^ "Error: \n")
        ^ msg
    let rec wrapLoc' __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Loc (filename, Reg (i, j)), Some linesInfo, msg) ->
          let lcfrom = posToLineCol' (linesInfo, i) in
          let lcto = posToLineCol' (linesInfo, j) in
          let regString =
            (^) ((lineColToString lcfrom) ^ "-") lineColToString lcto in
          ((((filename ^ ":") ^ regString) ^ " ") ^ "Error: \n") ^ msg
      | (loc, None, msg) -> wrapLoc0 (loc, msg)
    let rec wrapLoc loc msg = wrapLoc' (loc, (Some (getLinesInfo ())), msg)
    type __Path =
      | Label of __Path 
      | Body of __Path 
      | Head 
      | Arg of (int * __Path) 
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
    let rec occToPath __3__ __4__ =
      match (__3__, __4__) with
      | (top, path) -> path
      | (label occ, path) -> occToPath (occ, (Label path))
      | (body occ, path) -> occToPath (occ, (Body path))
      | (head occ, path) -> occToPath (occ, Head)
      | (arg (n, occ), path) -> occToPath (occ, (Arg (n, path)))(* path = Here by invariant *)
    type occConDec =
      | dec of (int * occExp) [@sml.renamed "dec"][@sml.renamed "dec"]
      | def of (int * occExp * occExp option)
      [@sml.renamed "def"][@sml.renamed "def"]
    let rec posToPath u k =
      let rec inside =
        function
        | leaf r -> posInRegion (k, r)
        | bind (r, _, _) -> posInRegion (k, r)
        | root (r, _, _, _, _) -> posInRegion (k, r) in
      let rec toPath =
        function
        | leaf (Reg (i, j)) -> Here
        | bind (Reg (i, j), None, u) ->
            if inside u then Body (toPath u) else Here
        | bind (Reg (i, j), Some u1, u2) ->
            if inside u1
            then Label (toPath u1)
            else if inside u2 then Body (toPath u2) else Here
        | root (Reg (i, j), h, imp, actual, s) ->
            if inside h
            then Head
            else
              (match toPathSpine (s, 1) with
               | None -> Here
               | Some (n, path) -> Arg ((n + imp), path))(* check? mark? *)
      and toPathSpine __5__ __6__ =
        match (__5__, __6__) with
        | (nils, n) -> None
        | (app (u, s), n) ->
            if inside u
            then Some (n, (toPath u))
            else toPathSpine (s, (n + 1)) in
      ((toPath u)
        (* local functions refer to k but not u *)(* in some situations, whitespace after subexpressions *)
        (* might give a larger term than anticipated *))
    let rec toRegion =
      function
      | leaf r -> r
      | bind (r, _, _) -> r
      | root (r, _, _, _, _) -> r
    let rec toRegionSpine __7__ __8__ =
      match (__7__, __8__) with
      | (nils, r) -> r
      | (app (u, s), r) -> join ((toRegion u), (toRegionSpine (s, r)))
    let rec pathToRegion __9__ __10__ =
      match (__9__, __10__) with
      | (u, Here) -> toRegion u
      | (bind (r, None, u), Label path) -> r
      | (bind (r, Some u1, u2), Label path) -> pathToRegion (u1, path)
      | (bind (r, _, u), Body path) -> pathToRegion (u, path)
      | (root (r, _, _, _, _), Label path) -> r
      | ((root _ as u), Body path) -> pathToRegion (u, path)
      | (root (r, h, imp, actual, s), Head) -> toRegion h
      | (root (r, h, imp, actual, s), Arg (n, path)) ->
          ((if n <= imp
            then toRegion h
            else
              ((if (n - imp) > actual
                then r
                else pathToRegionSpine (s, (n - imp), path))
              (* addressing argument created by eta expansion
                approximate by the whole root *)))
          (* addressing implicit argument returns region of head *))
      | (leaf r, _) -> r(* bypassing binder introduced as the result of eta expansion *)
      (* addressing binder introduced as the result of eta expansion
           approximate as the eta-expanded root *)
      (* addressing implicit type label returns region of binder and its scope *)
    let rec pathToRegionSpine __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (app (u, s), 1, path) -> pathToRegion (u, path)
      | (app (u, s), n, path) -> pathToRegionSpine (s, (n - 1), path)
    let rec occToRegionExp u occ = pathToRegion (u, (occToPath (occ, Here)))
    let rec skipImplicit __14__ __15__ =
      match (__14__, __15__) with
      | (0, path) -> path
      | (n, Body path) -> skipImplicit ((n - 1), path)
      | (n, Label path) -> Here
      | (n, Here) -> Here(* addressing body including implicit arguments: approximate by body *)
      (* implicit argument: approximate as best possible *)
    let rec occToRegionDec (dec (n, v)) occ =
      pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
    let rec occToRegionDef1 (def (n, u, vOpt)) occ =
      pathToRegion (u, (skipImplicit (n, (occToPath (occ, Here)))))
    let rec occToRegionDef2 __16__ __17__ =
      match (__16__, __17__) with
      | (def (n, u, Some v), occ) ->
          pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
      | (def (n, u, None), occ) -> pathToRegion (u, Here)
    let rec occToRegionClause __18__ __19__ =
      match (__18__, __19__) with
      | ((dec _ as d), occ) -> occToRegionDec d occ
      | ((def _ as d), occ) -> occToRegionDef2 d occ
  end  module Paths = (Make_Paths)(struct  end);;




module Origins =
  (Make_Origins)(struct
                   module Global = Global
                   module Table = StringHashTable
                 end);;
