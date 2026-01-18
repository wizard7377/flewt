
open FunSyn open FunTypeCheck module I = IntSyn
let _ = Twelf.loadFile "cp.elf"
let exp = I.Root ((I.Const (valOf (Names.nameLookup "exp"))), I.Nil)
let exp' = I.Root ((I.Const (valOf (Names.nameLookup "exp'"))), I.Nil)
let cp = I.Const (valOf (Names.nameLookup "cp"))
let lam = I.Const (valOf (Names.nameLookup "lam"))
let lam' = I.Const (valOf (Names.nameLookup "lam'"))
let cp_lam = I.Const (valOf (Names.nameLookup "cp_lam"))
let app = I.Const (valOf (Names.nameLookup "app"))
let app' = I.Const (valOf (Names.nameLookup "app'"))
let cp_app = I.Const (valOf (Names.nameLookup "cp_app"))
let one = I.Root ((I.BVar 1), I.Nil) let two = I.Root ((I.BVar 2), I.Nil)
let three = I.Root ((I.BVar 3), I.Nil) let four = I.Root ((I.BVar 4), I.Nil)
let five = I.Root ((I.BVar 5), I.Nil) let six = I.Root ((I.BVar 6), I.Nil)
let cpt_theorem =
  All
    ((Prim (I.Dec ((Some "E"), exp))),
      (Ex
         ((I.Dec ((Some "E'"), exp')),
           (Ex
              ((I.Dec
                  ((Some "__d"),
                    (I.Root (cp, (I.App (two, (I.App (one, I.Nil)))))))),
                True)))))
let rec union =
  function
  | (__g, I.Null) -> __g
  | (__g, Decl (__g', __d)) -> I.Decl ((union (__g, __g')), __d)
let rec makectx =
  function
  | I.Null -> I.Null
  | Decl (__g, Prim (__d)) -> I.Decl ((makectx __g), __d)
  | Decl (__g, Block (CtxBlock (l, __g'))) -> union ((makectx __g), __g')
let rec printCtx =
  function
  | I.Null -> ()
  | Decl (__g, Prim (__d)) ->
      (printCtx __g; TextIO.print ((Print.decToString ((makectx __g), __d)) ^ "\n"))
  | Decl (__g, _) -> (printCtx __g; TextIO.print "BLOCK\n")
let rec print (Psi, __u) =
  TextIO.print ((Print.expToString ((makectx Psi), __u)) ^ "\n")
let cpt_proof =
  Rec
    ((MDec ((Some "IH"), cpt_theorem)),
      (Lam
         ((Prim (I.Dec ((Some "E"), exp))),
           (Case
              (Opts
                 [((I.Decl
                      (I.Null,
                        (Block
                           (CtxBlock
                              ((Some 1),
                                (I.Decl
                                   ((I.Decl
                                       ((I.Decl
                                           (I.Null,
                                             (I.Dec ((Some "x"), exp)))),
                                         (I.Dec ((Some "y"), exp')))),
                                     (I.Dec
                                        ((Some "u"),
                                          (I.Root
                                             (cp,
                                               (I.App
                                                  (two, (I.App (one, I.Nil))))))))))))))),
                    (I.Dot ((I.Idx 3), I.id)),
                    (Inx (two, (Inx (one, Unit)))));
                 ((I.Decl
                     (I.Null,
                       (Prim
                          (I.Dec
                             ((Some "E1"),
                               (I.Pi (((I.Dec ((Some "x"), exp)), I.No), exp))))))),
                   (I.Dot
                      ((I.Exp ((I.Root (lam, (I.App (one, I.Nil)))), exp)),
                        (I.Shift 1))),
                   (Let
                      ((New
                          ((CtxBlock
                              ((Some 1),
                                (I.Decl
                                   ((I.Decl
                                       ((I.Decl
                                           (I.Null,
                                             (I.Dec ((Some "x"), exp)))),
                                         (I.Dec ((Some "y"), exp')))),
                                     (I.Dec
                                        ((Some "u"),
                                          (I.Root
                                             (cp,
                                               (I.App
                                                  (two, (I.App (one, I.Nil)))))))))))),
                            (App
                               ((1, (I.Redex (four, (I.App (three, I.Nil))))),
                                 (Split (1, (Split (1, Empty)))))))),
                        (Inx
                           ((I.Root (lam', (I.App (two, I.Nil)))),
                             (Inx
                                ((I.Root
                                    (cp_lam,
                                      (I.App
                                         (three,
                                           (I.App (two, (I.App (one, I.Nil)))))))),
                                  Unit)))))));
                 ((I.Decl
                     ((I.Decl (I.Null, (Prim (I.Dec ((Some "E1"), exp))))),
                       (Prim (I.Dec ((Some "E2"), exp))))),
                   (I.Dot
                      ((I.Exp
                          ((I.Root (app, (I.App (two, (I.App (one, I.Nil)))))),
                            exp)), (I.Shift 2))),
                   (Let
                      ((App
                          ((1, two),
                            (Split
                               (1,
                                 (Split
                                    (1,
                                      (App
                                         ((4, three),
                                           (Split (1, (Split (1, Empty)))))))))))),
                        (Inx
                           ((I.Root
                               (app', (I.App (four, (I.App (two, I.Nil)))))),
                             (Inx
                                ((I.Root
                                    (cp_app,
                                      (I.App
                                         (five,
                                           (I.App
                                              (two,
                                                (I.App
                                                   (six,
                                                     (I.App
                                                        (four,
                                                          (I.App
                                                             (one,
                                                               (I.App
                                                                  (three,
                                                                    I.Nil)))))))))))))),
                                  Unit)))))))])))))
(* the copy function theorem, internal format *)
(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------- *)
let print = print let printCtx = printCtx let cpt_proof = cpt_proof
let cpt_theorem = cpt_theorem
let _ =
  try check (cpt_proof, cpt_theorem)
  with | Error s -> TextIO.print (s ^ "\n")
  | Error s -> TextIO.print (s ^ "\n");;
