
let rec test file =
  match Twelf.Config.load (Twelf.Config.read file) with
  | Twelf.OK -> Twelf.OK
  | Twelf.ABORT -> raise Domain ;;Twelf.unsafe := true
;;test "examples/church-rosser/test-unsafe.cfg" ;;Twelf.unsafe := false;;
