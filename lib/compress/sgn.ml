
module type SGN  =
  sig
    type nonrec sigent
    type def =
      | DEF_NONE 
      | DEF_TERM of Syntax.term 
      | DEF_TYPE of Syntax.tp 
    val condec : (string * Syntax.tp * Syntax.tp) -> sigent
    val tycondec : (string * Syntax.knd * Syntax.knd) -> sigent
    val defn :
      (string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term) -> sigent
    val tydefn :
      (string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp) -> sigent
    val abbrev :
      (string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term) -> sigent
    val tyabbrev :
      (string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp) -> sigent
    val typeOfSigent : sigent -> Syntax.tp
    val classifier : int -> Syntax.class__
    val o_classifier : int -> Syntax.class__
    val def : int -> def
    val o_def : int -> def
    val update : (int * sigent) -> unit
    val sub : int -> sigent option
    val clear : unit -> unit
    val get_modes : int -> Syntax.mode list option
    val set_modes : (int * Syntax.mode list) -> unit
    val get_p : int -> bool option
    val set_p : (int * bool) -> unit
    val abbreviation : int -> bool
  end
module Sgn =
  struct
    open Syntax
    exception NoSuch of int 
    type def =
      | DEF_NONE 
      | DEF_TERM of term 
      | DEF_TYPE of tp 
    (* o_ means "original", i.e. before compression *)
    type nonrec sigent =
      <
        name: string  ;classifier: class__  ;o_classifier: class__  ;
        def: def  ;o_def: def  ;abbreviation: bool   > 
    let sgn_size = 14000
    (* XXX *)
    let (sigma : sigent option Array.array) = Array.array (sgn_size, None)
    let (all_modes : mode list option Array.array) =
      Array.array (sgn_size, None)
    let (all_ps : bool option Array.array) = Array.array (sgn_size, None)
    let rec split arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (h::tl, 0) -> ([], h, tl)
      | (h::tl, n) ->
          let (pre, thing, post) = split tl (n - 1) in
          ((h :: pre), thing, post)
      | ([], n) -> split [None] n
    let rec clear () =
      Array.modify (function | _ -> None) sigma;
      Array.modify (function | _ -> None) all_modes;
      Array.modify (function | _ -> None) all_ps
    let rec condec (s, a, oa) =
      {
        name = s;
        classifier = (tclass a);
        o_classifier = (tclass oa);
        def = DEF_NONE;
        o_def = DEF_NONE;
        abbreviation = false__
      }
    let rec tycondec (s, k, ok) =
      {
        name = s;
        classifier = (kclass k);
        o_classifier = (kclass ok);
        def = DEF_NONE;
        o_def = DEF_NONE;
        abbreviation = false__
      }
    let rec defn (s, a, oa, m, om) =
      {
        name = s;
        classifier = (tclass a);
        o_classifier = (tclass oa);
        def = (DEF_TERM m);
        o_def = (DEF_TERM om);
        abbreviation = false__
      }
    let rec tydefn (s, k, ok, a, oa) =
      {
        name = s;
        classifier = (kclass k);
        o_classifier = (kclass ok);
        def = (DEF_TYPE a);
        o_def = (DEF_TYPE oa);
        abbreviation = false__
      }
    let rec abbrev (s, a, oa, m, om) =
      {
        name = s;
        classifier = (tclass a);
        o_classifier = (tclass oa);
        def = (DEF_TERM m);
        o_def = (DEF_TERM om);
        abbreviation = true__
      }
    let rec tyabbrev (s, k, ok, a, oa) =
      {
        name = s;
        classifier = (kclass k);
        o_classifier = (kclass ok);
        def = (DEF_TYPE a);
        o_def = (DEF_TYPE oa);
        abbreviation = true__
      }
    let rec typeOfSigent (e : sigent) =
      Syntax.typeOf ((fun r -> r.classifier) e)
    let rec setter table (n, x) = Array.update (table, n, (Some x))
    let rec getter table id = Array.sub (table, id)
    let set_modes = setter all_modes
    let get_modes = getter all_modes
    let set_p = setter all_ps
    let get_p = getter all_ps
    let update = setter sigma
    let sub = getter sigma
    let rec classifier id =
      try (fun r -> r.classifier) (Option.valOf (sub id))
      with | Option -> raise (NoSuch id)
    let rec o_classifier id =
      try (fun r -> r.o_classifier) (Option.valOf (sub id))
      with | Option -> raise (NoSuch id)
    let rec def id =
      try (fun r -> r.def) (Option.valOf (sub id))
      with | Option -> raise (NoSuch id)
    let rec o_def id =
      try (fun r -> r.o_def) (Option.valOf (sub id))
      with | Option -> raise (NoSuch id)
    let rec abbreviation id =
      try (fun r -> r.abbreviation) (Option.valOf (sub id))
      with | Option -> raise (NoSuch id)
  end;;
