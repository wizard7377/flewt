
module type SKOLEM  = sig val install : IntSyn.cid list -> unit end;;




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
    let rec installSkolem name imp (__V, mS) (__L) =
      let rec spine =
        function
        | 0 -> I.Nil
        | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1))) in
      let rec installSkolem' __0__ __1__ __2__ __3__ =
        match (__0__, __1__, __2__, __3__) with
        | (d, (Pi ((__D, DP), __V), mS), s, k) ->
            (((match mS with
               | Mapp (Marg (M.Plus, _), mS') ->
                   installSkolem'
                     ((d + 1), (__V, mS'), (I.dot1 s),
                       (fun (__V) ->
                          k
                            (Abstract.piDepend
                               (((Whnf.normalizeDec (__D, s)), I.Meta), __V))))
               | Mapp (Marg (M.Minus, _), mS') ->
                   let Dec (_, __V') = __D in
                   let V'' = k (Whnf.normalize (__V', s)) in
                   let name' = Names.skonstName (name ^ "#") in
                   let SD = I.SkoDec (name', None, imp, V'', __L) in
                   let sk = I.sgnAdd SD in
                   let __H = I.Skonst sk in
                   let _ = IndexSkolem.install I.Ordinary __H in
                   let _ = Names.installConstName sk in
                   let _ =
                     Timers.time Timers.compiling Compile.install I.Ordinary
                       sk in
                   let __S = spine d in
                   let _ =
                     if (!Global.chatter) >= 3
                     then TextIO.print ((Print.conDecToString SD) ^ "\n")
                     else () in
                   ((installSkolem'
                       (d, (__V, mS'),
                         (I.Dot ((I.Exp (I.Root (__H, __S))), s)), k))
                     (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *))))
            (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *))
        | (_, (Uni _, M.Mnil), _, _) -> () in
      ((installSkolem' (0, (__V, mS), I.id, (fun (__V) -> __V)))
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
      function
      | nil -> ()
      | a::aL ->
          let ConDec (name, _, imp, _, __V, __L) = I.sgnLookup a in
          let Some mS = ModeTable.modeLookup a in
          let _ = installSkolem (name, imp, (__V, mS), I.Type) in install aL
    let install = install
  end ;;
