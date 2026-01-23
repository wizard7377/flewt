module type SKOLEM  = sig val install : IntSyn.cid list -> unit end


module Skolem(Skolem:sig
                       module Global : GLOBAL
                       module Whnf : WHNF
                       module Abstract : ABSTRACT
                       module IndexSkolem : INDEX
                       module ModeTable : MODETABLE
                       module Print : PRINT
                       module Compile : COMPILE
                       module Timers : TIMERS
                       module Names : NAMES
                     end) : SKOLEM =
  struct
    exception Error of string 
    module I = IntSyn
    module M = ModeSyn
    let rec installSkolem (name, imp, (v_, mS), l_) =
      let rec spine =
        begin function
        | 0 -> I.Nil
        | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1))) end in
    let rec installSkolem' =
      begin function
      | (d, (Pi ((d_, DP), v_), mS), s, k) ->
          (((begin match mS with
             | Mapp (Marg (M.Plus, _), mS') ->
                 installSkolem'
                   ((d + 1), (v_, mS'), (I.dot1 s),
                     (begin function
                      | v_ ->
                          k
                            (Abstract.piDepend
                               (((Whnf.normalizeDec (d_, s)), I.Meta), v_)) end))
          | Mapp (Marg (M.Minus, _), mS') ->
              let Dec (_, v'_) = d_ in
              let V'' = k (Whnf.normalize (v'_, s)) in
              let name' = Names.skonstName (name ^ "#") in
              let SD = I.SkoDec (name', None, imp, V'', l_) in
              let sk = I.sgnAdd SD in
              let h_ = I.Skonst sk in
              let _ = IndexSkolem.install I.Ordinary h_ in
              let _ = Names.installConstName sk in
              let _ =
                Timers.time Timers.compiling Compile.install I.Ordinary sk in
              let s_ = spine d in
              let _ =
                if !Global.chatter >= 3
                then begin TextIO.print ((Print.conDecToString SD) ^ "\n") end
                else begin () end in
              ((installSkolem'
                  (d, (v_, mS'), (I.Dot ((I.Exp (I.Root (h_, s_))), s)), k))
                (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)) end))
      (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *))
      | (_, (Uni _, M.Mnil), _, _) -> () end in
((installSkolem' (0, (v_, mS), I.id, (begin function | v_ -> v_ end)))
(* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
(* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *))
let rec install =
  begin function
  | [] -> ()
  | a::aL ->
      let ConDec (name, _, imp, _, v_, l_) = I.sgnLookup a in
      let Some mS = ModeTable.modeLookup a in
      let _ = installSkolem (name, imp, (v_, mS), I.Type) in install aL end
let install = install end
