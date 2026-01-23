module type INTERACTIVE  =
  sig
    module State : STATE
    exception Error of string 
    val init : string list -> unit
    val select : int -> unit
    val print : unit -> unit
    val stats : unit -> unit
    val focus : string -> unit
    val return : unit -> unit
    val reset : unit -> unit
  end


module Interactive(Interactive:sig
                                 module Global : GLOBAL
                                 module State' : STATE
                                 module Formatter : FORMATTER
                                 module Trail : TRAIL
                                 module Ring : RING
                                 module Names : NAMES
                                 module Weaken : WEAKEN
                                 module WorldSyn : WORLDSYN
                                 module Introduce : INTRODUCE
                                 module Elim : ELIM
                                 module Split : SPLIT
                                 module FixedPoint : FIXEDPOINT
                                 module Fill : FILL
                               end) : INTERACTIVE =
  struct
    module State = State'
    exception Error = State'.Error
    module I = IntSyn
    module T = Tomega
    module S = State
    module M = ModeSyn
    module W = WorldSyn
    let rec abort s = begin print (("* " ^ s) ^ "\n"); raise (Error s) end
    let rec convertOneFor cid =
      let v_ =
        begin match I.sgnLookup cid with
        | ConDec (name, _, _, _, v_, I.Kind) -> v_
        | _ -> raise (Error "Type Constant declaration expected") end in
    let mS =
      begin match ModeTable.modeLookup cid with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS end in
    let rec convertFor' =
      begin function
      | (Pi ((d_, _), v_), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
          let (f'_, F'') =
            convertFor'
              (v_, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
          (((begin function
             | f_ ->
                 T.All
                   (((T.UDec (Weaken.strengthenDec (d_, w1))), T.Explicit),
                     (f'_ f_)) end)),
            F'')
      | (Pi ((d_, _), v_), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
          let (f'_, F'') =
            convertFor'
              (v_, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
          (f'_, (T.Ex (((I.decSub (d_, w2)), T.Explicit), F'')))
      | (Uni (I.Type), M.Mnil, _, _, _) ->
          (((begin function | f_ -> f_ end)), T.True)
      | _ -> raise (Error "type family must be +/- moded") end in
  let rec shiftPlus mS =
    let rec shiftPlus' =
      begin function
      | (M.Mnil, n) -> n
      | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
      | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) end in
  shiftPlus' (mS, 0) in
  let n = shiftPlus mS in
  let (f_, f'_) = convertFor' (v_, mS, I.id, (I.Shift n), n) in ((f_ f'_)
    (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *))
let rec convertFor =
  begin function
  | [] -> raise (Error "Empty theorem")
  | a::[] -> convertOneFor a
  | a::l_ -> T.And ((convertOneFor a), (convertFor l_)) end
type menuItem_ =
  | Split of Split.operator 
  | Fill of Fill.operator 
  | Introduce of Introduce.operator 
  | Fix of FixedPoint.operator 
  | Elim of Elim.operator 
let ((Focus) : S.state_ list ref) = ref []
let ((Menu) : menuItem_ list option ref) = ref None
let rec SplittingToMenu (o_, a_) = (Split o_) :: a_
let rec initFocus () = Focus := []
let rec normalize () =
  begin match !Focus with
  | (State (w_, Psi, p_, f_))::Rest ->
      Focus := ((S.State (w_, Psi, (T.derefPrg p_), f_)) :: Rest)
  | _ -> () end
let rec reset () = begin initFocus (); Menu := None end
let rec format k = if k < 10 then begin (Int.toString k) ^ ".  " end
  else begin (Int.toString k) ^ ". " end
let rec menuToString () =
  let rec menuToString' =
    begin function
    | (k, []) -> ""
    | (k, (Split (o_))::m_) ->
        let s = menuToString' ((k + 1), m_) in
        ((s ^ "\n  ") ^ (format k)) ^ (Split.menu o_)
    | (k, (Introduce (o_))::m_) ->
        let s = menuToString' ((k + 1), m_) in
        ((s ^ "\n  ") ^ (format k)) ^ (Introduce.menu o_)
    | (k, (Fill (o_))::m_) ->
        let s = menuToString' ((k + 1), m_) in
        ((s ^ "\n  ") ^ (format k)) ^ (Fill.menu o_)
    | (k, (Fix (o_))::m_) ->
        let s = menuToString' ((k + 1), m_) in
        ((s ^ "\n  ") ^ (format k)) ^ (FixedPoint.menu o_)
    | (k, (Elim (o_))::m_) ->
        let s = menuToString' ((k + 1), m_) in
        ((s ^ "\n  ") ^ (format k)) ^ (Elim.menu o_) end in
((begin match !Menu with
  | None -> raise (Error "Menu is empty")
  | Some (m_) -> menuToString' (1, m_) end)
  (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*))
let rec printStats () =
  let nopen = 0 in
  let nsolved = 0 in
  begin print "Statistics:\n\n";
  print (("Number of goals : " ^ (Int.toString (nopen + nsolved))) ^ "\n");
  print (("     open goals : " ^ (Int.toString nopen)) ^ "\n");
  print (("   solved goals : " ^ (Int.toString nsolved)) ^ "\n") end
let rec printmenu () =
  begin match !Focus with
  | [] -> abort "QED"
  | (State (w_, Psi, p_, f_))::r_ ->
      (begin print "\n=======================";
       print "\n= META THEOREM PROVER =\n";
       print (TomegaPrint.ctxToString Psi);
       print "\n-----------------------\n";
       print (TomegaPrint.forToString (Psi, f_));
       print "\n-----------------------\n";
       print (TomegaPrint.prgToString (Psi, p_));
       print "\n-----------------------";
       print (menuToString ());
       print "\n=======================\n" end)
  | (StateLF (EVar (r, g_, v_, cs_) as x_))::r_ ->
      (begin print "\n=======================";
       print "\n=== THEOREM PROVER ====\n";
       print (Print.ctxToString (I.Null, g_));
       print "\n-----------------------\n";
       print (Print.expToString (g_, v_));
       print "\n-----------------------\n";
       print (Print.expToString (g_, x_));
       print "\n-----------------------";
       print (menuToString ());
       print "\n=======================\n" end) end
let rec menu () =
  begin match !Focus with
  | [] -> print "Please initialize first\n"
  | (State (w_, Psi, p_, f_))::_ ->
      let xs_ = S.collectT p_ in
      let f1_ =
        map
          (begin function
           | EVar (Psi, r, f_, TC, TCs, x_) ->
               (begin Names.varReset I.Null;
                S.Focus
                  ((T.EVar ((TomegaPrint.nameCtx Psi), r, f_, TC, TCs, x_)),
                    w_) end) end)
        xs_ in
    let ys_ = S.collectLF p_ in
    let f2_ = map (begin function | y_ -> S.FocusLF y_ end) ys_ in
    let rec splitMenu =
      begin function
      | [] -> []
      | operators::l -> (@) (map Split operators) splitMenu l end in
    let _ = Global.doubleCheck := true in
    let rec introMenu =
      begin function
      | [] -> []
      | (Some oper)::l -> (::) (Introduce oper) introMenu l
      | (None)::l -> introMenu l end in
    let intro = introMenu (map Introduce.expand f1_) in
    let fill =
      foldr
        (begin function
         | (s_, l) -> (@) l map ((begin function | o_ -> Fill o_ end))
             (Fill.expand s_) end)
      [] f2_ in
    let rec elimMenu =
      begin function
      | [] -> []
      | operators::l -> (@) (map Elim operators) elimMenu l end in
    let elim = elimMenu (map Elim.expand f1_) in
    let split = splitMenu (map Split.expand f1_) in
    (:=) Menu Some (((intro @ split) @ fill) @ elim)
| (StateLF (y_))::_ ->
    let ys_ = Abstract.collectEVars (I.Null, (y_, I.id), []) in
    let f2_ = map (begin function | y_ -> S.FocusLF y_ end) ys_ in
    let fill =
      foldr
        (begin function
         | (s_, l) -> (@) l map ((begin function | o_ -> Fill o_ end))
             (Fill.expand s_) end)
      [] f2_ in
  (:=) Menu Some fill end
let rec select k =
  let rec select' =
    begin function
    | (k, []) -> abort "No such menu item"
    | (1, (Split (o_))::_) -> Timers.time Timers.splitting Split.apply o_
    | (1, (Introduce (o_))::_) -> Introduce.apply o_
    | (1, (Elim (o_))::_) -> Elim.apply o_
    | (1, (Fill (o_))::_) -> Timers.time Timers.filling Fill.apply o_
    | (k, _::m_) -> select' ((k - 1), m_) end(* no timer yet -- cs *)
  (* no timer yet -- cs *) in
begin match !Menu with
| None -> raise (Error "No menu defined")
| Some (m_) ->
    (begin try begin select' (k, m_); normalize (); menu (); printmenu () end
    with | Error s -> () end) end
let rec init names =
  let _ = TomegaPrint.evarReset () in
  let cL =
    map
      (begin function
       | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))) end)
    names in
  let f_ = convertFor cL in
  let ws_ = map W.lookup cL in
  let rec select c = begin try Order.selLookup c with | _ -> Order.Lex [] end in
  let TC = Tomega.transformTC (I.Null, f_, (map select cL)) in
  let (w_)::_ = ws_ in
  let _ = Focus := [S.init (f_, w_)] in
  let p_ =
    begin match !Focus with
    | [] -> abort "Initialization of proof goal failed\n"
    | (State (w_, Psi, p_, f_))::_ -> p_ end in
  let xs_ = S.collectT p_ in
  let f_ =
    map
      (begin function
       | EVar (Psi, r, f_, TC, TCs, x_) ->
           (begin Names.varReset I.Null;
            S.Focus
              ((T.EVar ((TomegaPrint.nameCtx Psi), r, f_, TC, TCs, x_)), w_) end) end)
    xs_ in
  let (Ofix)::[] = map (begin function | f -> FixedPoint.expand (f, TC) end)
    f_ in
  let _ = FixedPoint.apply Ofix in
  let _ = normalize () in
  let _ = menu () in
  let _ = printmenu () in ((())
    (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *))
let rec focus n =
  ((begin match !Focus with
    | [] -> print "Please initialize first\n"
    | (State (w_, Psi, p_, f_))::_ ->
        let rec findIEVar =
          begin function
          | [] -> raise (Error ("cannot focus on " ^ n))
          | (y_)::ys_ ->
              if (Names.evarName ((T.coerceCtx Psi), y_)) = n
              then
                begin (begin Focus := ((!) ((::) (S.StateLF y_)) Focus);
                       normalize ();
                       menu ();
                       printmenu () end) end
          else begin findIEVar ys_ end end in
let rec findTEVar =
  begin function
  | [] -> findIEVar (S.collectLF p_)
  | (EVar (Psi, r, f_, TC, TCs, y_) as x_)::xs_ ->
      if (Names.evarName ((T.coerceCtx Psi), y_)) = n
      then
        begin (begin Focus :=
                       ((!) ((::) (S.State
                                     (w_, (TomegaPrint.nameCtx Psi), x_, f_)))
                          Focus);
               normalize ();
               menu ();
               printmenu () end) end
  else begin findTEVar xs_ end end in findTEVar (S.collectT p_)
| (StateLF (u_))::_ ->
    (begin match Names.getEVarOpt n with
     | None -> raise (Error ("cannot focus on " ^ n))
     | Some (y_) ->
         (begin Focus := ((!) ((::) (S.StateLF y_)) Focus);
          normalize ();
          menu ();
          printmenu () end) end) end)
(* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *))
let rec return () =
  begin match !Focus with
  | (s_)::[] -> if S.close s_ then begin print "[Q.E.D.]\n" end
      else begin () end
  | (s_)::Rest ->
      (begin Focus := Rest; normalize (); menu (); printmenu () end) end
let init = init
let select = select
let print = printmenu
let stats = printStats
let reset = reset
let focus = focus
let return = return end
