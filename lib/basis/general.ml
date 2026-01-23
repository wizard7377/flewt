
exception Bind
exception Match
exception Chr
exception Div
exception Domain
exception Fail of string
exception Overflow
exception Size
exception Span
exception Subscript

let exnName : exn -> string = Printexc.exn_slot_name ;;
let exnMessage : exn -> string = Printexc.to_string
;;
type order = LESS | EQUAL | GREATER
let order_to_int = function | LESS -> -1 | EQUAL -> 0 | GREATER -> 1
let int_to_order = function
  | n when n < 0 -> LESS
  | 0 -> EQUAL
  | _ -> GREATER


let before (x, _) = x

let ignore _ = ()