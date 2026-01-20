
(* (Outdated) Regression test - *)
(* Author: Frank Pfenning *)
(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)
(* Twelf.chatter := 5; *) ;;Twelf.doubleCheck := true
let rec test file =
  match Twelf.make file with
  | Twelf.OK -> Twelf.OK
  | Twelf.ABORT -> raise Domain
let rec testUnsafe file =
  let _ = Twelf.unsafe := true in
  let stat =
    try Twelf.make file with | e -> (Twelf.unsafe := false; raise e) in
  let _ = Twelf.unsafe := false in
  match stat with | Twelf.OK -> Twelf.OK | Twelf.ABORT -> raise Domain
let rec conclude () = () ;;use "TEST/regression.sml";;
