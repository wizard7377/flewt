
module type PATHS  =
  sig
    type region =
      | Reg of
      (((int)(* Author: Frank Pfenning *)(* Paths, Occurrences, and Error Locations *))
      * int) 
    type location =
      | Loc of
      (((string)(* r ::= (i,j) is interval [i,j) *)) *
      region) 
    type nonrec linesInfo(* line numbering, used when printing regions *)
    (* loc ::= (filename, region) *)
    val resetLines :
      unit ->
        ((unit)(* mapping from character positions to lines in a file *))
    val newLine : int -> ((unit)(* reset line numbering *))
    val getLinesInfo :
      unit ->
        ((linesInfo)(* new line starts at character i *))
    val join :
      (region * region) ->
        ((region)(* get lines info for current file *))
    val toString :
      region ->
        ((string)(* join(r1,r2) = smallest region enclosing r1 and r2 *))
    val wrap :
      (region * string) ->
        ((string)(* line1.col1-line2.col2, parsable by Emacs *))
    val wrapLoc :
      (location * string) ->
        ((string)(* add region to error message, parsable by Emacs *))
    val wrapLoc' :
      (location * linesInfo option * string) ->
        ((string)(* add location to error message, also parsable *))
    type __Path =
      | Label of
      ((__Path)(* Follow path through a term to obtain subterm *)
      (* In the general case, regions only approximate true source location *)
      (* Paths, occurrences and occurrence trees only work well for normal forms *)
      (* add location to error message in line.col format *))
      
      | Body of ((__Path)(* [x:#] U or {x:#} V *)) 
      | Head 
      | Arg of
      (((int)(* # @ S, term in normal form *)(* [x:V] # or {x:V} # *))
      * __Path) 
      | Here 
    type nonrec occ(*
     Construct an occurrence when traversing a term.
     The resulting occurrence can be translated to a region
     via an occurrence tree stored with the term.

     An occurrence is a path in reverse order.
  *)
    (* #, covers Uni, EVar, Redex(?) *)(* H @ S1; ...; #; ...; Sn; Nil *)
    val top : occ
    val label : occ -> occ
    val body : occ -> occ
    val head : occ -> occ
    val arg : (int * occ) -> occ
    type nonrec occExp(*
     An occurrence tree is a data structure mapping occurrences in a term
     to regions in an input stream.  Occurrence trees are constructed during parsing.
  *)
    and occSpine(* occurrence tree for u expressions *)
    val leaf :
      region -> ((occExp)(* occurrence tree for s spines *))
    val bind :
      (region * occExp option * occExp) ->
        ((occExp)(* could be _ or identifier *))
    val root : (region * occExp * int * int * occSpine) -> occExp
    val app : (occExp * occSpine) -> occSpine
    val nils : occSpine
    type nonrec occConDec
    val dec :
      (int * occExp) ->
        ((occConDec)(* occurrence tree for constant declarations *))
    val def :
      (int * occExp * occExp option) ->
        ((occConDec)(* (#implicit, v) in c : V *))
    val toRegion :
      occExp ->
        ((region)(* (#implicit, u, v) in c : V = U *))
    val toRegionSpine : (occSpine * region) -> region
    val posToPath : occExp -> int -> __Path
    val occToRegionExp : occExp -> occ -> region
    val occToRegionDec : occConDec -> occ -> region
    val occToRegionDef1 :
      occConDec -> occ -> ((region)(* into v for c : V *))
    val occToRegionDef2 :
      occConDec ->
        occ -> ((region)(* into u for c : V = U *))
    val occToRegionClause :
      occConDec ->
        occ -> ((region)(* into v for c : V = U *))
  end;;




module Paths() : PATHS =
  struct
    type nonrec pos = int
    type region =
      | Reg of (pos * pos) 
    type location =
      | Loc of (string * region) 
    type nonrec linesInfo = pos list
    let rec posToLineCol' (linesInfo, i) =
      let ptlc =
        function
        | j::js -> if i >= j then ((List.length js), (i - j)) else ptlc js
        | nil -> (0, i) in
      ptlc linesInfo
    let linePosList = (ref nil : pos list ref)
    let rec resetLines () = linePosList := nil
    let rec newLine i = (linePosList := i) :: (!linePosList)
    let rec getLinesInfo () = !linePosList
    let rec posToLineCol i = posToLineCol' ((!linePosList), i)
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
      function
      | (Loc (filename, Reg (i, j)), SOME linesInfo, msg) ->
          let lcfrom = posToLineCol' (linesInfo, i) in
          let lcto = posToLineCol' (linesInfo, j) in
          let regString =
            (^) ((lineColToString lcfrom) ^ "-") lineColToString lcto in
          ((((filename ^ ":") ^ regString) ^ " ") ^ "Error: \n") ^ msg
      | (loc, NONE, msg) -> wrapLoc0 (loc, msg)
    let rec wrapLoc (loc, msg) =
      wrapLoc' (loc, (SOME (getLinesInfo ())), msg)
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
    let rec occToPath =
      function
      | (top, path) -> path
      | (label occ, path) -> occToPath (occ, (Label path))
      | (body occ, path) -> occToPath (occ, (Body path))
      | (head occ, path) -> occToPath (occ, Head)
      | (arg (n, occ), path) -> occToPath (occ, (Arg (n, path)))
    type occConDec =
      | dec of (int * occExp) [@sml.renamed "dec"][@sml.renamed "dec"]
      | def of (int * occExp * occExp option)
      [@sml.renamed "def"][@sml.renamed "def"]
    let rec posToPath u k =
      let inside =
        function
        | leaf r -> posInRegion (k, r)
        | bind (r, _, _) -> posInRegion (k, r)
        | root (r, _, _, _, _) -> posInRegion (k, r) in
      let toPath =
        function
        | leaf (Reg (i, j)) -> Here
        | bind (Reg (i, j), NONE, u) ->
            if inside u then Body (toPath u) else Here
        | bind (Reg (i, j), SOME u1, u2) ->
            if inside u1
            then Label (toPath u1)
            else if inside u2 then Body (toPath u2) else Here
        | root (Reg (i, j), h, imp, actual, s) ->
            if inside h
            then Head
            else
              (match toPathSpine (s, 1) with
               | NONE -> Here
               | SOME (n, path) -> Arg ((n + imp), path))
      and toPathSpine =
        function
        | (nils, n) -> NONE
        | (app (u, s), n) ->
            if inside u
            then SOME (n, (toPath u))
            else toPathSpine (s, (n + 1)) in
      toPath u
    let rec toRegion =
      function
      | leaf r -> r
      | bind (r, _, _) -> r
      | root (r, _, _, _, _) -> r
    let rec toRegionSpine =
      function
      | (nils, r) -> r
      | (app (u, s), r) -> join ((toRegion u), (toRegionSpine (s, r)))
    let rec pathToRegion =
      function
      | (u, Here) -> toRegion u
      | (bind (r, NONE, u), Label path) -> r
      | (bind (r, SOME u1, u2), Label path) -> pathToRegion (u1, path)
      | (bind (r, _, u), Body path) -> pathToRegion (u, path)
      | (root (r, _, _, _, _), Label path) -> r
      | ((root _ as u), Body path) -> pathToRegion (u, path)
      | (root (r, h, imp, actual, s), Head) -> toRegion h
      | (root (r, h, imp, actual, s), Arg (n, path)) ->
          if n <= imp
          then toRegion h
          else
            if (n - imp) > actual
            then r
            else pathToRegionSpine (s, (n - imp), path)
      | (leaf r, _) -> r
    let rec pathToRegionSpine =
      function
      | (app (u, s), 1, path) -> pathToRegion (u, path)
      | (app (u, s), n, path) -> pathToRegionSpine (s, (n - 1), path)
    let rec occToRegionExp u occ = pathToRegion (u, (occToPath (occ, Here)))
    let rec skipImplicit =
      function
      | (0, path) -> path
      | (n, Body path) -> skipImplicit ((n - 1), path)
      | (n, Label path) -> Here
      | (n, Here) -> Here
    let rec occToRegionDec (dec (n, v)) occ =
      pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
    let rec occToRegionDef1 (def (n, u, vOpt)) occ =
      pathToRegion (u, (skipImplicit (n, (occToPath (occ, Here)))))
    let rec occToRegionDef2 arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (def (n, u, SOME v), occ) ->
          pathToRegion (v, (skipImplicit (n, (occToPath (occ, Here)))))
      | (def (n, u, NONE), occ) -> pathToRegion (u, Here)
    let rec occToRegionClause arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((dec _ as d), occ) -> occToRegionDec d occ
      | ((def _ as d), occ) -> occToRegionDef2 d occ
  end 
module Paths = (Make_Paths)(struct  end)(* functor Paths *)
(* occToRegionClause d occ = r
     where r is the closest region in V including occ for declaration
     c : V or c : V = U.
  *)
(* occToRegionDef2 d occ = r
     where r is the closest region in V including occ for declaration c : V = U
  *)
(* occToRegionDef1 d occ = r
     where r is the closest region in u including occ for declaration c : V = U
  *)
(* occToRegionDec d occ = r
     where r is the closest region in v including occ for declaration c : V
  *)
(* anything else should be impossible *)(* addressing body including implicit arguments: approximate by body *)
(* implicit argument: approximate as best possible *)
(* occToRegionExp u occ = r,
     where r is the closest region including occ in occurrence tree u
  *)
(* anything else should be impossible *)(* other combinations should be impossible *)
(* possible if leaf was _ (underscore) *)(* addressing argument created by eta expansion
                approximate by the whole root *)
(* addressing implicit argument returns region of head *)
(* bypassing binder introduced as the result of eta expansion *)
(* addressing binder introduced as the result of eta expansion
           approximate as the eta-expanded root *)
(* addressing implicit type label returns region of binder and its scope *)
(* pathToRegion (u, p) = r,
     where r is the region identified by path p in occurrence tree u
  *)
(* order? *)(* toRegionSpine (s, r) = r', the join of all regions in s and r *)
(* toRegion (u) = r, the region associated with the whole occurrence tree u *)
(* might give a larger term than anticipated *)(* in some situations, whitespace after subexpressions *)
(* check? mark? *)(* local functions refer to k but not u *)
(* posToPath (u, k) = p
     where p is the path to the innermost expression in u enclosing position i.

     This includes the position immediately at the end of a region [i,j).
     For example, in "f (g x) y",
     0,1 => "f"
     2   => "(g x)"
     3,4 => "g"
     5,6 => "x"
     8,9 => "y"
  *)
(* val posToPath : occExp -> pos -> Path *)(* (#implicit, u, v) in c : V = U *)
(* (#implicit, v) in c : V *)(* occurrence tree for constant declarations *)
(* path = Here by invariant *)(* occToPath (occ, p) = p'(p) and occ corresponds to p' *)
(* nil *)(* u;s *)(* occurrences in spines *)
(* h @ s, # of implicit arguments, # of arguments actually input (as opposed to generated by eta-expansion) *)
(* [x:vOpt] u or {x:vOpt} v' *)(* _ or identifier *)
(* occurrences in expressions *)(* A region in an intermediate node encloses the whole expression *)
(* Simple-minded implementation *)(* Maps occurrences to regions *)
(* Occurrence trees for expressions and spines *)(* could also be: type occ = path -> path *)
(* Occurrences: paths in reverse order *)(* #, covers Uni, EVar, Redex(?) *)
(* C @ S1; ...; #; ...; Sn; Nil *)(* # @ S, term in normal form *)
(* [x:V] # or {x:V} # *)(* [x:#] U or {x:#} V *)
(* Follow path through a term to obtain subterm *)(* In the general case, regions only approximate true source location *)
(* Paths, occurrences and occurrence trees only work well for normal forms *)
(* wrapLoc' ((loc, r), linesInfo, msg) = msg'
     like wrapLoc, but converts character positions to line.col format based
     on linesInfo, if possible
  *)
(* wrapLoc ((loc, r), msg) = msg' which contains region and filename
     This should be used for locations retrieved from origins, where
     the region is given in character positions, rather than lines and columns
  *)
(* wrap (r, msg) = msg' which contains region *)(* toString r = "line1.col1-line2.col2", a format parsable by Emacs *)
(* The right endpoint of the interval counts IN RANGE *)
(* join (r1, r2) = r
     where r is the  smallest region containing both r1 and r2
  *)
(* posToLineCol (i) = (line,column) for character position i *)(* maintained with state *)
(* used to convert character positions into line.column format *)
(* !linePosList is a list of starting character positions for each input line *)
(* nil means first "line" was not terminated by <newline> *)(* first line should start at 0 *)
(* loc ::= (filename, region) *)(* r ::= (i,j) is interval [i,j) *)
(* characters, starting at 0 *)(* Author: Frank Pfenning *)
(* Paths, Occurrences, and Error Locations *);;




module Origins =
  (Make_Origins)(struct
                   module Global =
                     ((Global)(* Now in paths.fun *)
                     (*
structure Paths = Paths ();
*))
                   module Table = StringHashTable
                 end);;
