(* TextPrimIO module - Primitive text I/O *)
(* See https://smlfamily.github.io/Basis/text-prim-io.html *)

type elem = char
type vector = string
type vector_slice = string * int * int  (* string, start, length *)
type array = bytes
type array_slice = bytes * int * int    (* bytes, start, length *)
type pos = int

type order = LESS | EQUAL | GREATER

let compare (p1, p2) =
  if p1 < p2 then LESS
  else if p1 > p2 then GREATER
  else EQUAL

type reader = {
  name : string;
  chunkSize : int;
  readVec : (int -> string) option;
  readArr : (array_slice -> int) option;
  readVecNB : (int -> string option) option;
  readArrNB : (array_slice -> int option) option;
  block : (unit -> unit) option;
  canInput : (unit -> bool) option;
  avail : unit -> int option;
  getPos : (unit -> pos) option;
  setPos : (pos -> unit) option;
  endPos : (unit -> pos) option;
  verifyPos : (unit -> pos) option;
  close : unit -> unit;
  ioDesc : Unix.file_descr option;
}

type writer = {
  name : string;
  chunkSize : int;
  writeVec : (vector_slice -> int) option;
  writeArr : (array_slice -> int) option;
  writeVecNB : (vector_slice -> int option) option;
  writeArrNB : (array_slice -> int option) option;
  block : (unit -> unit) option;
  canOutput : (unit -> bool) option;
  getPos : (unit -> pos) option;
  setPos : (pos -> unit) option;
  endPos : (unit -> pos) option;
  verifyPos : (unit -> pos) option;
  close : unit -> unit;
  ioDesc : Unix.file_descr option;
}

let openVector s =
  let pos = ref 0 in
  let len = Stdlib.String.length s in
  let readVec n =
    let available = len - !pos in
    let to_read = min n available in
    let result = Stdlib.String.sub s !pos to_read in
    pos := !pos + to_read;
    result
  in
  {
    name = "<string>";
    chunkSize = 1024;
    readVec = Some readVec;
    readArr = None;
    readVecNB = Some (fun n -> Some (readVec n));
    readArrNB = None;
    block = Some (fun () -> ());
    canInput = Some (fun () -> !pos < len);
    avail = (fun () -> Some (len - !pos));
    getPos = Some (fun () -> !pos);
    setPos = Some (fun p -> pos := p);
    endPos = Some (fun () -> len);
    verifyPos = Some (fun () -> !pos);
    close = (fun () -> ());
    ioDesc = None;
  }

let nullRd () =
  {
    name = "<null>";
    chunkSize = 1;
    readVec = Some (fun _ -> "");
    readArr = None;
    readVecNB = Some (fun _ -> Some "");
    readArrNB = None;
    block = Some (fun () -> ());
    canInput = Some (fun () -> true);
    avail = (fun () -> Some 0);
    getPos = None;
    setPos = None;
    endPos = None;
    verifyPos = None;
    close = (fun () -> ());
    ioDesc = None;
  }

let nullWr () =
  {
    name = "<null>";
    chunkSize = 1;
    writeVec = Some (fun (_, _, len) -> len);
    writeArr = Some (fun (_, _, len) -> len);
    writeVecNB = Some (fun (_, _, len) -> Some len);
    writeArrNB = Some (fun (_, _, len) -> Some len);
    block = Some (fun () -> ());
    canOutput = Some (fun () -> true);
    getPos = None;
    setPos = None;
    endPos = None;
    verifyPos = None;
    close = (fun () -> ());
    ioDesc = None;
  }

let stdInReader () =
  {
    name = "<stdin>";
    chunkSize = 1024;
    readVec = Some (fun n ->
        let buf = Bytes.create n in
        let read = input stdin buf 0 n in
        Bytes.sub_string buf 0 read
      );
    readArr = Some (fun (buf, start, len) ->
        input stdin buf start len
      );
    readVecNB = None;
    readArrNB = None;
    block = None;
    canInput = None;
    avail = (fun () -> None);
    getPos = None;
    setPos = None;
    endPos = None;
    verifyPos = None;
    close = (fun () -> ());
    ioDesc = Some Unix.stdin;
  }

let stdOutWriter () =
  {
    name = "<stdout>";
    chunkSize = 1024;
    writeVec = Some (fun (s, start, len) ->
        output_substring stdout s start len;
        len
      );
    writeArr = Some (fun (buf, start, len) ->
        output stdout buf start len;
        len
      );
    writeVecNB = None;
    writeArrNB = None;
    block = None;
    canOutput = None;
    getPos = None;
    setPos = None;
    endPos = None;
    verifyPos = None;
    close = (fun () -> flush stdout);
    ioDesc = Some Unix.stdout;
  }

let stdErrWriter () =
  {
    name = "<stderr>";
    chunkSize = 1024;
    writeVec = Some (fun (s, start, len) ->
        output_substring stderr s start len;
        len
      );
    writeArr = Some (fun (buf, start, len) ->
        output stderr buf start len;
        len
      );
    writeVecNB = None;
    writeArrNB = None;
    block = None;
    canOutput = None;
    getPos = None;
    setPos = None;
    endPos = None;
    verifyPos = None;
    close = (fun () -> flush stderr);
    ioDesc = Some Unix.stderr;
  }

let openRd filename =
  let ic = open_in filename in
  {
    name = filename;
    chunkSize = 1024;
    readVec = Some (fun n ->
        let buf = Bytes.create n in
        let read = input ic buf 0 n in
        Bytes.sub_string buf 0 read
      );
    readArr = Some (fun (buf, start, len) ->
        input ic buf start len
      );
    readVecNB = None;
    readArrNB = None;
    block = None;
    canInput = None;
    avail = (fun () -> None);
    getPos = Some (fun () -> pos_in ic);
    setPos = Some (fun p -> seek_in ic p);
    endPos = Some (fun () -> in_channel_length ic);
    verifyPos = Some (fun () -> pos_in ic);
    close = (fun () -> close_in ic);
    ioDesc = None;
  }

let openWr filename =
  let oc = open_out filename in
  {
    name = filename;
    chunkSize = 1024;
    writeVec = Some (fun (s, start, len) ->
        output_substring oc s start len;
        len
      );
    writeArr = Some (fun (buf, start, len) ->
        output oc buf start len;
        len
      );
    writeVecNB = None;
    writeArrNB = None;
    block = None;
    canOutput = None;
    getPos = Some (fun () -> pos_out oc);
    setPos = Some (fun p -> seek_out oc p);
    endPos = Some (fun () -> out_channel_length oc);
    verifyPos = Some (fun () -> pos_out oc);
    close = (fun () -> close_out oc);
    ioDesc = None;
  }

let openApp filename =
  let oc = open_out_gen [Open_wronly; Open_append; Open_creat] 0o666 filename in
  {
    name = filename;
    chunkSize = 1024;
    writeVec = Some (fun (s, start, len) ->
        output_substring oc s start len;
        len
      );
    writeArr = Some (fun (buf, start, len) ->
        output oc buf start len;
        len
      );
    writeVecNB = None;
    writeArrNB = None;
    block = None;
    canOutput = None;
    getPos = Some (fun () -> pos_out oc);
    setPos = Some (fun p -> seek_out oc p);
    endPos = Some (fun () -> out_channel_length oc);
    verifyPos = Some (fun () -> pos_out oc);
    close = (fun () -> close_out oc);
    ioDesc = None;
  }
