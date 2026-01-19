(* TextIO module - High-level text I/O implementation *)
(* See https://smlfamily.github.io/Basis/text-io.html *)

open Base

type substring = Substring.Substring.substring

(** Module type for text I/O operations *)
module type TEXT_IO = sig
  type vector = string
  type elem = char

  type instream
  type outstream

  module StreamIO : TextStreamIO.TEXT_STREAM_IO

  (** Read from input stream *)
  val input : instream -> vector

  (** Read single element from input stream *)
  val input1 : instream -> elem option

  (** Read n elements from input stream *)
  val inputN : instream * int -> vector

  (** Read all remaining input *)
  val inputAll : instream -> vector

  (** Check if n elements can be read without blocking *)
  val canInput : instream * int -> int option

  (** Look at next element without consuming it *)
  val lookahead : instream -> elem option

  (** Close input stream *)
  val closeIn : instream -> unit

  (** Test if at end of stream *)
  val endOfStream : instream -> bool

  (** Write vector to output stream *)
  val output : outstream * vector -> unit

  (** Write single element to output stream *)
  val output1 : outstream * elem -> unit

  (** Flush output stream *)
  val flushOut : outstream -> unit

  (** Close output stream *)
  val closeOut : outstream -> unit

  (** Create imperative input stream from functional stream *)
  val mkInstream : StreamIO.instream -> instream

  (** Get underlying functional stream *)
  val getInstream : instream -> StreamIO.instream

  (** Set underlying functional stream *)
  val setInstream : instream * StreamIO.instream -> unit

  (** Create imperative output stream from functional stream *)
  val mkOutstream : StreamIO.outstream -> outstream

  (** Get underlying functional output stream *)
  val getOutstream : outstream -> StreamIO.outstream

  (** Set underlying functional output stream *)
  val setOutstream : outstream * StreamIO.outstream -> unit

  (** Get current output position *)
  val getPosOut : outstream -> StreamIO.out_pos

  (** Set output position *)
  val setPosOut : outstream * StreamIO.out_pos -> unit

  (** Read a line (including newline if present) *)
  val inputLine : instream -> string option

  (** Write a substring to output stream *)
  val outputSubstr : outstream * substring -> unit

  (** Open file for reading *)
  val openIn : string -> instream

  (** Open file for writing *)
  val openOut : string -> outstream

  (** Open file for appending *)
  val openAppend : string -> outstream

  (** Open string as input stream *)
  val openString : string -> instream

  (** Standard input stream *)
  val stdIn : instream

  (** Standard output stream *)
  val stdOut : outstream

  (** Standard error stream *)
  val stdErr : outstream

  (** Print string to stdout and flush *)
  val print : string -> unit

  (** Scan using a reader-based scanner *)
  val scanStream : ((Base.Char.t, StreamIO.instream) StringCvt.StringCvt.reader
                    -> ('a, StreamIO.instream) StringCvt.StringCvt.reader)
    -> instream -> 'a option
end

module TextIO : TEXT_IO = struct
  module StreamIO = TextStreamIO.TextStreamIO

  type vector = string
  type elem = char

  (* Imperative streams with mutable state *)
  type instream = StreamIO.instream ref
  type outstream = StreamIO.outstream ref

  let input ins =
    let (vec, ins') = StreamIO.input !ins in
    ins := ins';
    vec

  let input1 ins =
    match StreamIO.input1 !ins with
    | None -> None
    | Some (c, ins') ->
      ins := ins';
      Some c

  let inputN (ins, n) =
    let (vec, ins') = StreamIO.inputN (!ins, n) in
    ins := ins';
    vec

  let inputAll ins =
    let (vec, ins') = StreamIO.inputAll !ins in
    ins := ins';
    vec

  let canInput (ins, n) =
    StreamIO.canInput (!ins, n)

  let lookahead ins =
    match StreamIO.input1 !ins with
    | None -> None
    | Some (c, _) -> Some c

  let closeIn ins =
    StreamIO.closeIn !ins

  let endOfStream ins =
    StreamIO.endOfStream !ins

  let output (outs, vec) =
    StreamIO.output (!outs, vec)

  let output1 (outs, c) =
    StreamIO.output1 (!outs, c)

  let flushOut outs =
    StreamIO.flushOut !outs

  let closeOut outs =
    StreamIO.closeOut !outs

  let mkInstream sins =
    ref sins

  let getInstream ins = !ins

  let setInstream (ins, sins) =
    ins := sins

  let mkOutstream souts =
    ref souts

  let getOutstream outs = !outs

  let setOutstream (outs, souts) =
    outs := souts

  let getPosOut outs =
    StreamIO.getPosOut !outs

  let setPosOut (outs, pos) =
    outs := StreamIO.setPosOut pos

  (* TextIO-specific functions *)

  let inputLine ins =
    match StreamIO.inputLine !ins with
    | None -> None
    | Some (line, ins') ->
      ins := ins';
      Some line

  let outputSubstr (outs, ss) =
    StreamIO.outputSubstr (!outs, ss)

  let openIn filename =
    let reader = TextPrimIO.openRd filename in
    let sins = StreamIO.mkInstream (reader, "") in
    mkInstream sins

  let openOut filename =
    let writer = TextPrimIO.openWr filename in
    let souts = StreamIO.mkOutstream (writer, TextStreamIO.LINE_BUF) in
    mkOutstream souts

  let openAppend filename =
    let writer = TextPrimIO.openApp filename in
    let souts = StreamIO.mkOutstream (writer, TextStreamIO.LINE_BUF) in
    mkOutstream souts

  let openString s =
    let reader = TextPrimIO.openVector s in
    let sins = StreamIO.mkInstream (reader, "") in
    mkInstream sins

  (* Standard streams *)
  let stdIn =
    let reader = TextPrimIO.stdInReader () in
    let sins = StreamIO.mkInstream (reader, "") in
    mkInstream sins

  let stdOut =
    let writer = TextPrimIO.stdOutWriter () in
    let souts = StreamIO.mkOutstream (writer, TextStreamIO.LINE_BUF) in
    mkOutstream souts

  let stdErr =
    let writer = TextPrimIO.stdErrWriter () in
    let souts = StreamIO.mkOutstream (writer, TextStreamIO.NO_BUF) in
    mkOutstream souts

  let print s =
    output (stdOut, s);
    flushOut stdOut

  let scanStream f ins =
    match f StreamIO.input1 (getInstream ins) with
    | None -> None
    | Some (v, s') ->
      setInstream (ins, s');
      Some v
end
