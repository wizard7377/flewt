module type NETSERVER  =
  sig
    val flashServer : int -> unit
    val humanServer : int -> unit
    val httpServer : int -> string -> unit
    val setExamplesDir : string -> unit
  end
module NetServer(NetServer:sig
                             module Timing : TIMING
                             module Twelf : TWELF
                             module Msg : MSG
                           end) : NETSERVER =
  struct
    let rec join arg__0 arg__1 =
      begin match (arg__0, arg__1) with
      | (delim, []) -> ""
      | (delim, x::[]) -> x
      | (delim, h::tl) -> (h ^ delim) ^ (join delim tl) end
    type nonrec server = < send: string -> unit  ;exec: string -> unit   > 
    type nonrec protocol =
      <
        init: unit -> unit  ;reset: unit -> unit  ;recv: server ->
                                                           string -> unit  ;
        send: server -> string -> unit  ;done_: unit -> unit   > 
    module S = Socket
    let maxConnections = 128
    let rec loop f = begin f (); loop f end
  let rec vec2str v =
    String.implode
      (map (Char.chr o Word8.toInt) (Word8Vector.foldr (::) [] v))
  let rec str2vec l =
    Word8Vector.fromList (map (Word8.fromInt o Char.ord) (String.explode l))
  let rec fileText fname =
    let s = TextIO.openIn fname in
    let txt = TextIO.inputAll s in let _ = TextIO.closeIn s in txt
  let rec fileData fname =
    let s = BinIO.openIn fname in
    let data = BinIO.inputAll s in let _ = BinIO.closeIn s in vec2str data
  exception EOF 
  exception Quit 
  let rec send conn str =
    begin Compat.SocketIO.sendVec (conn, (str2vec str)); () end
module SS = Substring
let rec parseCmd s =
  let (c, a) = SS.position " " (Compat.Substring.full s) in
  ((SS.string c), (SS.string (SS.dropl Char.isSpace a)))
let rec quote string = ("`" ^ string) ^ "'"
let (examplesDir : string option ref) = ref None
let rec setExamplesDir s = (:=) examplesDir Some s
exception Error of string 
let rec error msg = raise (Error msg)
let rec serveExample e =
  if
    begin match e with
    | "ccc" -> true
    | "cut-elim" -> true
    | "handbook" -> true
    | "lp-horn" -> true
    | "prop-calc" -> true
    | "units" -> true
    | "church-rosser" -> true
    | "fj" -> true
    | "incll" -> true
    | "mini-ml" -> true
    | "small-step" -> true
    | "alloc-sem" -> true
    | "compile" -> true
    | "fol" -> true
    | "kolm" -> true
    | "modal" -> true
    | "tabled" -> true
    | "arith" -> true
    | "cpsocc" -> true
    | "guide" -> true
    | "lp" -> true
    | "polylam" -> true
    | "tapl-ch13" -> true
    | _ -> false end
  then
    begin begin try
                  begin OS.FileSys.chDir
                          (((Option.valOf !examplesDir) ^ "/") ^ e);
                  Twelf.make "sources.cfg" end
    with | e -> raise (Error (((^) "Exception " exnName e) ^ " raised.")) end end
else begin raise (Error ((^) "Unknown example " quote e)) end
let rec getNat =
  begin function
  | t::[] ->
      (begin try Lexer.stringToNat t
       with | NotDigit char -> error ((quote t) ^ " is not a natural number") end)
  | [] -> error "Missing natural number" | ts -> error "Extraneous arguments" end
let rec getExample =
  begin function
  | t::[] -> t
  | [] -> error "Missing example"
  | ts -> error "Extraneous arguments" end
let rec setParm =
  begin function
  | "chatter"::ts -> (:=) Twelf.chatter getNat ts
  | t::ts -> error ((^) "Unknown parameter " quote t)
  | [] -> error "Missing parameter" end
let rec exec' arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (conn, ("quit", args)) -> (begin Msg.message "goodbye.\n"; raise Quit end)
  | (conn, ("set", args)) ->
      (begin setParm (String.tokens Char.isSpace args); Twelf.OK end)
  | (conn, ("readDecl", args)) -> Twelf.loadString args
  | (conn, ("decl", args)) -> Twelf.decl args
  | (conn, ("example", args)) ->
      serveExample (getExample (String.tokens Char.isSpace args))
  | (conn, (t, args)) -> raise (Error ((^) "Unrecognized command " quote t)) end
let rec exec conn str =
  begin match begin try exec' conn (parseCmd str)
              with
              | Error s ->
                  (begin Msg.message (("Server Error: " ^ s) ^ "\n");
                   Twelf.ABORT end) end
  with | Twelf.OK -> Msg.message "%%% OK %%%\n"
  | Twelf.ABORT -> Msg.message "%%% ABORT %%%\n" end
let rec stripcr s =
  Substring.string (Substring.dropr (begin function | x -> x = 'r' end)
    (Compat.Substring.full s))
let rec flashProto () =
  let (buf : string ref) = ref "" in
  let rec isnull = begin function | '\000' -> true | _ -> false end in
  let rec recv (u : server) s =
    let _ = ((!) ((:=) buf) buf) ^ s in
    let rem::cmds = rev (String.fields isnull !buf) in
    let _ = app ((fun r -> r.exec) u) (rev cmds) in buf := rem in
  let rec send (u : server) s = (fun r -> r.send) u (s ^ "\000") in
  {
    init =
      (begin function | () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n") end);
  reset = (begin function | () -> buf := "" end); send; recv;
    done_ = (begin function | () -> () end) }
let rec humanProto () =
  let (buf : string ref) = ref "" in
  let rec isnewl =
    begin function | '\n' -> true | 'r' -> false | _ -> false end in
  let rec recv (u : server) s =
    let _ = ((!) ((:=) buf) buf) ^ s in
    let rem::cmds = rev (String.fields isnewl !buf) in
    let _ = app ((fun r -> r.exec) u) (map stripcr (rev cmds)) in buf := rem in
  let rec send (u : server) s = (fun r -> r.send) u ("> " ^ s) in
  {
    init =
      (begin function | () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n") end);
  reset = (begin function | () -> buf := "" end); send; recv;
    done_ = (begin function | () -> () end) }
let rec httpProto dir =
  let (ibuf : string ref) = ref "" in
  let (obuf : string ref) = ref "" in
  let parsingHeaders = ref true in
  let contentLength = ref 0 in
  let (method_ : string ref) = ref "" in
  let (url : string ref) = ref "" in
  let (headers : string list ref) = ref [] in
  let rec isnewl = begin function | '\n' -> true | _ -> false end in
  let rec handlePostRequest (u : server) =
    let shouldQuit = begin try begin ((fun r -> r.exec)) u !ibuf; false end
      with | Quit -> true end in
  let response = !obuf in
  let clmsg = ((^) "Content-Length: " Int.toString (size response)) ^ "\n" in
  begin ((fun r -> r.send)) u
          (("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg) ^ "\n");
  ((fun r -> r.send)) u response;
  if shouldQuit then begin raise Quit end
  else begin raise EOF end end in
  let rec handleGetRequest (u : server) =
    let ok = "200 OK" in
    let missing = "404 Not Found" in
    let (content, ctype, rcode) =
      begin match !url with
      | "/" ->
          ((fileText (dir ^ "/server.html")), "application/xhtml+xml", ok)
      | "/server.js" -> ((fileText (dir ^ "/server.js")), "text/plain", ok)
      | "/server.css" -> ((fileText (dir ^ "/server.css")), "text/css", ok)
      | "/grad.png" -> ((fileData (dir ^ "/grad.png")), "image/png", ok)
      | "/twelfguy.png" ->
          ((fileData (dir ^ "/twelfguy.png")), "image/png", ok)
      | "/input.png" -> ((fileData (dir ^ "/input.png")), "image/png", ok)
      | "/output.png" -> ((fileData (dir ^ "/output.png")), "image/png", ok)
      | "/floral.png" -> ((fileData (dir ^ "/floral.png")), "image/png", ok)
      | _ -> ("Error 404", "text/plain", missing) end in
    let clmsg = ((^) "Content-Length: " Int.toString (size content)) ^ "\r\n" in
    let ctmsg = ("Content-Type: " ^ ctype) ^ "\r\n" in
    let resp = ("HTTP/1.1 " ^ rcode) ^ "\r\n" in
    begin ((fun r -> r.send)) u (((resp ^ ctmsg) ^ clmsg) ^ "\r\n");
    ((fun r -> r.send)) u content;
    raise EOF;
    () end in
  let rec handleRequest (u : server) =
    if !method_ = "GET" then begin handleGetRequest u end
    else begin if !method_ = "POST" then begin handlePostRequest u end
      else begin ((fun r -> r.send)) u "HTTP/1.1 500 Server Error\n\n" end end in
let rec headerExec s = headers := ((!) ((::) s) headers) in
let rec recvContent u =
  if (!) ((>=) (size !ibuf)) contentLength then begin handleRequest u end
  else begin () end in
let rec parseHeaders () =
  begin try
          let request::headers = rev !headers in
          let m::u::httpVersion::[] =
            String.tokens (begin function | x -> x = ' ' end) request in
          let _ = method_ := m in
          let _ = url := u in
          let rec getField s =
            let k::v = String.fields (begin function | x -> x = ':' end) s in
          let v = join ":" v in (k, (substring (v, 1, ((size v) - 1)))) in
          let rec proc_one s =
            let (k, v) = getField s in
            if k = "Content-Length"
            then
              begin contentLength :=
                      (begin match Int.fromString v with
                       | None -> 0
                       | Some n -> n end) end
            else begin () end in
          let () = app proc_one headers in parsingHeaders := false
with | Bind -> raise EOF end in
let rec interp arg__4 arg__5 =
begin match (arg__4, arg__5) with
| ((u : server), []) -> raise Match
| (u, x::[]) -> ibuf := x
| (u, h::tl) ->
    let sch = stripcr h in
    if sch = ""
    then
      begin (begin (:=) ibuf join "\n" tl; parseHeaders (); recvContent u end) end
    else begin (begin headerExec (stripcr h); interp u tl end) end end in
let rec recv (u : server) s =
begin ((!) ((:=) ibuf) ibuf) ^ s;
if !parsingHeaders then begin interp u (String.fields isnewl !ibuf) end
else begin recvContent u end end in
let rec send (u : server) s = ((!) ((:=) obuf) obuf) ^ s in
let rec reset () =
begin parsingHeaders := true;
ibuf := "";
obuf := "";
contentLength := 0;
headers := [];
url := "";
method_ := "" end in
{ init = (begin function | () -> () end);
reset;
send;
recv;
done_ = (begin function | () -> () end)
}
let rec protoServer (proto : protocol) portNum =
  let sock = INetSock.TCP.socket () in
  let _ = S.Ctl.setREUSEADDR (sock, true) in
  let _ = S.bind (sock, (INetSock.any portNum)) in
  let _ = S.listen (sock, maxConnections) in
  let rec read_one conn u () =
    let v = S.recvVec (conn, 1024) in
    ((if (Word8Vector.length v) = 0 then begin raise EOF end
      else begin ((fun r -> r.recv)) proto u (vec2str v) end)
    (* arbitrary buffer size *)) in
  let rec accept_one () =
    let (conn, addr) = S.accept sock in
    let _ = (fun r -> r.reset) proto () in
    let u = { send = (send conn); exec = (exec conn) } in
    let _ = Msg.setMessageFunc ((fun r -> r.send) proto u) in
    let _ = (fun r -> r.init) proto () in
    begin try loop (read_one conn u)
    with | EOF -> (begin ((fun r -> r.done_)) proto (); S.close conn end)
    | Quit ->
        (begin ((fun r -> r.done_)) proto (); S.close conn; raise Quit end) end in
  begin try loop accept_one with | Quit -> S.close sock end
let rec flashServer port = protoServer (flashProto ()) port
let rec humanServer port = protoServer (humanProto ()) port
let rec httpServer port dir = protoServer (httpProto dir) port end 
module NetServer =
  (NetServer)(struct
                     module Timing = Timing
                     module Twelf = Twelf
                     module Msg = Msg
                   end)