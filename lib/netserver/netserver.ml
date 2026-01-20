
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
    let rec join __0__ __1__ =
      match (__0__, __1__) with
      | (delim, []) -> ""
      | (delim, x::[]) -> x
      | (delim, h::tl) -> (h ^ delim) ^ (join delim tl)
    type nonrec server = < send: string -> unit  ;exec: string -> unit   > 
    type nonrec protocol =
      <
        init: unit -> unit  ;reset: unit -> unit  ;recv: server ->
                                                           string -> unit  ;
        send: server -> string -> unit  ;done__: unit -> unit   > 
    module S = Socket
    let maxConnections = 128
    let rec loop f = f (); loop f
    let rec vec2str v =
      String.implode
        (map (Char.chr o Word8.toInt) (Word8Vector.foldr (::) nil v))
    let rec str2vec l =
      Word8Vector.fromList
        (map (Word8.fromInt o Char.ord) (String.explode l))
    let rec fileText fname =
      let s = TextIO.openIn fname in
      let txt = TextIO.inputAll s in let _ = TextIO.closeIn s in txt
    let rec fileData fname =
      let s = BinIO.openIn fname in
      let data = BinIO.inputAll s in let _ = BinIO.closeIn s in vec2str data
    exception EOF 
    exception Quit 
    let rec send conn str = Compat.SocketIO.sendVec (conn, (str2vec str)); ()
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
        match e with
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
        | _ -> false
      then
        try
          OS.FileSys.chDir (((Option.valOf (!examplesDir)) ^ "/") ^ e);
          Twelf.make "sources.cfg"
        with | e -> raise (Error (((^) "Exception " exnName e) ^ " raised."))
      else raise (Error ((^) "Unknown example " quote e))
    let rec getNat =
      function
      | t::nil ->
          (try Lexer.stringToNat t
           with
           | NotDigit char -> error ((quote t) ^ " is not a natural number"))
      | nil -> error "Missing natural number"
      | ts -> error "Extraneous arguments"
    let rec getExample =
      function
      | t::nil -> t
      | nil -> error "Missing example"
      | ts -> error "Extraneous arguments"
    let rec setParm =
      function
      | "chatter"::ts -> (:=) Twelf.chatter getNat ts
      | t::ts -> error ((^) "Unknown parameter " quote t)
      | nil -> error "Missing parameter"
    let rec exec' __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (conn, "quit", args) -> (Msg.message "goodbye.\n"; raise Quit)
      | (conn, "set", args) ->
          (setParm (String.tokens Char.isSpace args); Twelf.OK)
      | (conn, "readDecl", args) -> Twelf.loadString args
      | (conn, "decl", args) -> Twelf.decl args
      | (conn, "example", args) ->
          serveExample (getExample (String.tokens Char.isSpace args))
      | (conn, t, args) ->
          raise (Error ((^) "Unrecognized command " quote t))
    let rec exec conn str =
      match try exec' conn (parseCmd str)
            with
            | Error s ->
                (Msg.message (("Server Error: " ^ s) ^ "\n"); Twelf.ABORT)
      with
      | Twelf.OK -> Msg.message "%%% OK %%%\n"
      | Twelf.ABORT -> Msg.message "%%% ABORT %%%\n"
    let rec stripcr s =
      Substring.string
        (Substring.dropr (fun x -> x = '\r') (Compat.Substring.full s))
    let rec flashProto () =
      let (buf : string ref) = ref "" in
      let rec isnull = function | '\000' -> true | _ -> false in
      let rec recv u s =
        let _ = ((!) ((:=) buf) buf) ^ s in
        let rem::cmds = rev (String.fields isnull (!buf)) in
        let _ = app ((fun r -> r.exec) u) (rev cmds) in buf := rem in
      let rec send u s = (fun r -> r.send) u (s ^ "\000") in
      {
        init = (fun () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n"));
        reset = (fun () -> buf := "");
        send;
        recv;
        done__ = (fun () -> ())
      }
    let rec humanProto () =
      let (buf : string ref) = ref "" in
      let rec isnewl =
        function | '\n' -> true | '\r' -> false | _ -> false in
      let rec recv u s =
        let _ = ((!) ((:=) buf) buf) ^ s in
        let rem::cmds = rev (String.fields isnewl (!buf)) in
        let _ = app ((fun r -> r.exec) u) (map stripcr (rev cmds)) in
        buf := rem in
      let rec send u s = (fun r -> r.send) u ("> " ^ s) in
      {
        init = (fun () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n"));
        reset = (fun () -> buf := "");
        send;
        recv;
        done__ = (fun () -> ())
      }
    let rec httpProto dir =
      let (ibuf : string ref) = ref "" in
      let (obuf : string ref) = ref "" in
      let parsingHeaders = ref true in
      let contentLength = ref 0 in
      let (method__ : string ref) = ref "" in
      let (url : string ref) = ref "" in
      let (headers : string list ref) = ref [] in
      let rec isnewl = function | '\n' -> true | _ -> false in
      let rec handlePostRequest u =
        let shouldQuit =
          try ((fun r -> r.exec)) u (!ibuf); false with | Quit -> true in
        let response = !obuf in
        let clmsg =
          ((^) "Content-Length: " Int.toString (size response)) ^ "\n" in
        ((fun r -> r.send)) u
          (("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg) ^ "\n");
        ((fun r -> r.send)) u response;
        if shouldQuit then raise Quit else raise EOF in
      let rec handleGetRequest u =
        let ok = "200 OK" in
        let missing = "404 Not Found" in
        let (content, ctype, rcode) =
          match !url with
          | "/" ->
              ((fileText (dir ^ "/server.html")), "application/xhtml+xml",
                ok)
          | "/server.js" ->
              ((fileText (dir ^ "/server.js")), "text/plain", ok)
          | "/server.css" ->
              ((fileText (dir ^ "/server.css")), "text/css", ok)
          | "/grad.png" -> ((fileData (dir ^ "/grad.png")), "image/png", ok)
          | "/twelfguy.png" ->
              ((fileData (dir ^ "/twelfguy.png")), "image/png", ok)
          | "/input.png" ->
              ((fileData (dir ^ "/input.png")), "image/png", ok)
          | "/output.png" ->
              ((fileData (dir ^ "/output.png")), "image/png", ok)
          | "/floral.png" ->
              ((fileData (dir ^ "/floral.png")), "image/png", ok)
          | _ -> ("Error 404", "text/plain", missing) in
        let clmsg =
          ((^) "Content-Length: " Int.toString (size content)) ^ "\r\n" in
        let ctmsg = ("Content-Type: " ^ ctype) ^ "\r\n" in
        let resp = ("HTTP/1.1 " ^ rcode) ^ "\r\n" in
        ((fun r -> r.send)) u (((resp ^ ctmsg) ^ clmsg) ^ "\r\n");
        ((fun r -> r.send)) u content;
        raise EOF;
        () in
      let rec handleRequest u =
        if (!method__) = "GET"
        then handleGetRequest u
        else
          if (!method__) = "POST"
          then handlePostRequest u
          else ((fun r -> r.send)) u "HTTP/1.1 500 Server Error\n\n" in
      let rec headerExec s = headers := ((!) ((::) s) headers) in
      let rec recvContent u =
        if (!) ((>=) (size (!ibuf))) contentLength
        then handleRequest u
        else () in
      let rec parseHeaders () =
        try
          let request::headers = rev (!headers) in
          let m::u::httpVersion::[] =
            String.tokens (fun x -> x = ' ') request in
          let _ = method__ := m in
          let _ = url := u in
          let rec getField s =
            let k::v = String.fields (fun x -> x = ':') s in
            let v = join ":" v in (k, (substring (v, 1, ((size v) - 1)))) in
          let rec proc_one s =
            let (k, v) = getField s in
            if k = "Content-Length"
            then
              contentLength :=
                (match Int.fromString v with | None -> 0 | Some n -> n)
            else () in
          let () = app proc_one headers in parsingHeaders := false
        with | Bind -> raise EOF in
      let rec interp __5__ __6__ =
        match (__5__, __6__) with
        | (u, []) -> raise Match
        | (u, x::[]) -> ibuf := x
        | (u, h::tl) ->
            let sch = stripcr h in
            if sch = ""
            then ((:=) ibuf join "\n" tl; parseHeaders (); recvContent u)
            else (headerExec (stripcr h); interp u tl) in
      let rec recv u s =
        ((!) ((:=) ibuf) ibuf) ^ s;
        if !parsingHeaders
        then interp u (String.fields isnewl (!ibuf))
        else recvContent u in
      let rec send u s = ((!) ((:=) obuf) obuf) ^ s in
      let rec reset () =
        parsingHeaders := true;
        ibuf := "";
        obuf := "";
        contentLength := 0;
        headers := [];
        url := "";
        method__ := "" in
      { init = (fun () -> ()); reset; send; recv; done__ = (fun () -> ()) }
    let rec protoServer proto portNum =
      let sock = INetSock.TCP.socket () in
      let _ = S.Ctl.setREUSEADDR (sock, true) in
      let _ = S.bind (sock, (INetSock.any portNum)) in
      let _ = S.listen (sock, maxConnections) in
      let rec read_one conn u () =
        let v = S.recvVec (conn, 1024) in
        ((if (Word8Vector.length v) = 0
          then raise EOF
          else ((fun r -> r.recv)) proto u (vec2str v))
          (* arbitrary buffer size *)) in
      let rec accept_one () =
        let (conn, addr) = S.accept sock in
        let _ = (fun r -> r.reset) proto () in
        let u = { send = (send conn); exec = (exec conn) } in
        let _ = Msg.setMessageFunc ((fun r -> r.send) proto u) in
        let _ = (fun r -> r.init) proto () in
        try loop (read_one conn u)
        with | EOF -> (((fun r -> r.done__)) proto (); S.close conn)
        | Quit -> (((fun r -> r.done__)) proto (); S.close conn; raise Quit) in
      try loop accept_one with | Quit -> S.close sock
    let rec flashServer port = protoServer (flashProto ()) port
    let rec humanServer port = protoServer (humanProto ()) port
    let rec httpServer port dir = protoServer (httpProto dir) port
  end 
module NetServer =
  (Make_NetServer)(struct
                     module Timing = Timing
                     module Twelf = Twelf
                     module Msg = Msg
                   end);;
