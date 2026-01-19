(* TextStreamIO module - Text stream I/O implementation *)
(* See https://smlfamily.github.io/Basis/text-stream-io.html *)

open Base

type substring = Substring.Substring.substring

(** Buffer mode for output streams *)
type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF

(** Module type for text stream I/O - extends STREAM_IO with text-specific operations *)
module type TEXT_STREAM_IO = sig
  type elem = char
  type vector = string

  type instream
  type outstream
  type out_pos

  type reader = TextPrimIO.reader
  type writer = TextPrimIO.writer
  type pos = TextPrimIO.pos

  (** Read from input stream *)
  val input : instream -> vector * instream

  (** Read single element from input stream *)
  val input1 : instream -> (elem * instream) option

  (** Read n elements from input stream *)
  val inputN : instream * int -> vector * instream

  (** Read all remaining input *)
  val inputAll : instream -> vector * instream

  (** Check if n elements can be read without blocking *)
  val canInput : instream * int -> int option

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

  (** Create input stream from reader and initial data *)
  val mkInstream : reader * vector -> instream

  (** Get underlying reader and remaining data from input stream *)
  val getReader : instream -> reader * vector

  (** Get current position in input stream *)
  val filePosIn : instream -> pos

  (** Set buffer mode for output stream *)
  val setBufferMode : outstream * buffer_mode -> unit

  (** Get buffer mode for output stream *)
  val getBufferMode : outstream -> buffer_mode

  (** Create output stream from writer and buffer mode *)
  val mkOutstream : writer * buffer_mode -> outstream

  (** Get underlying writer and buffer mode from output stream *)
  val getWriter : outstream -> writer * buffer_mode

  (** Get current output position *)
  val getPosOut : outstream -> out_pos

  (** Set output position *)
  val setPosOut : out_pos -> outstream

  (** Get file position from output position *)
  val filePosOut : out_pos -> pos

  (** Read a line (including newline if present) *)
  val inputLine : instream -> (string * instream) option

  (** Write a substring to output stream *)
  val outputSubstr : outstream * substring -> unit
end

module TextStreamIO : TEXT_STREAM_IO = struct
  type elem = char
  type vector = string
  type pos = TextPrimIO.pos
  type reader = TextPrimIO.reader
  type writer = TextPrimIO.writer

  type instream = {
    reader : reader;
    buffer : string;
    buf_pos : int;
  }

  type outstream = {
    writer : writer;
    buffer_mode : buffer_mode;
  }

  type out_pos = outstream * pos

  let input ins =
    let remaining = String.length ins.buffer - ins.buf_pos in
    if remaining > 0 then
      let data = String.sub ins.buffer ~pos:ins.buf_pos ~len:remaining in
      (data, { ins with buffer = ""; buf_pos = 0 })
    else
      match ins.reader.TextPrimIO.readVec with
      | None -> ("", ins)
      | Some read_fn ->
        let data = read_fn ins.reader.TextPrimIO.chunkSize in
        (data, { ins with buffer = ""; buf_pos = 0 })

  let input1 ins =
    let remaining = String.length ins.buffer - ins.buf_pos in
    if remaining > 0 then
      let c = String.get ins.buffer ins.buf_pos in
      Some (c, { ins with buf_pos = ins.buf_pos + 1 })
    else
      match ins.reader.TextPrimIO.readVec with
      | None -> None
      | Some read_fn ->
        let data = read_fn 1 in
        if String.is_empty data then None
        else Some (String.get data 0, ins)

  let inputN (ins, n) =
    let remaining = String.length ins.buffer - ins.buf_pos in
    if remaining >= n then
      let data = String.sub ins.buffer ~pos:ins.buf_pos ~len:n in
      (data, { ins with buf_pos = ins.buf_pos + n })
    else
      match ins.reader.TextPrimIO.readVec with
      | None ->
        if remaining > 0 then
          let data = String.sub ins.buffer ~pos:ins.buf_pos ~len:remaining in
          (data, { ins with buffer = ""; buf_pos = 0 })
        else
          ("", ins)
      | Some read_fn ->
        let from_buf = if remaining > 0 then String.sub ins.buffer ~pos:ins.buf_pos ~len:remaining else "" in
        let needed = n - remaining in
        let from_reader = read_fn needed in
        (from_buf ^ from_reader, { ins with buffer = ""; buf_pos = 0 })

  let inputAll ins =
    let remaining = String.length ins.buffer - ins.buf_pos in
    let from_buf = if remaining > 0 then String.sub ins.buffer ~pos:ins.buf_pos ~len:remaining else "" in
    match ins.reader.TextPrimIO.readVec with
    | None -> (from_buf, { ins with buffer = ""; buf_pos = 0 })
    | Some read_fn ->
      let rec loop acc =
        let data = read_fn 4096 in
        if String.is_empty data then String.concat ~sep:"" (List.rev acc)
        else loop (data :: acc)
      in
      (from_buf ^ loop [], { ins with buffer = ""; buf_pos = 0 })

  let canInput (_ins, _n) = None  (* Simplified *)

  let closeIn ins = ins.reader.TextPrimIO.close ()

  let endOfStream ins =
    let remaining = String.length ins.buffer - ins.buf_pos in
    if remaining > 0 then false
    else
      match ins.reader.TextPrimIO.canInput with
      | Some f -> not (f ())
      | None -> false

  let output (outs, vec) =
    match outs.writer.TextPrimIO.writeVec with
    | None -> ()
    | Some write_fn ->
      let _ = write_fn (vec, 0, String.length vec) in
      ()

  let output1 (outs, c) =
    output (outs, String.make 1 c)

  let flushOut _outs = ()  (* Simplified *)

  let closeOut outs = outs.writer.TextPrimIO.close ()

  let mkInstream (reader, vec) =
    { reader; buffer = vec; buf_pos = 0 }

  let getReader ins =
    let remaining = String.length ins.buffer - ins.buf_pos in
    let data = if remaining > 0 then String.sub ins.buffer ~pos:ins.buf_pos ~len:remaining else "" in
    (ins.reader, data)

  let filePosIn ins =
    match ins.reader.TextPrimIO.getPos with
    | Some f -> f () - (String.length ins.buffer - ins.buf_pos)
    | None -> 0

  let setBufferMode (_outs, _mode) = ()  (* Simplified *)

  let getBufferMode outs = outs.buffer_mode

  let mkOutstream (writer, mode) =
    { writer; buffer_mode = mode }

  let getWriter outs =
    (outs.writer, outs.buffer_mode)

  let getPosOut outs =
    let pos = match outs.writer.TextPrimIO.getPos with
      | Some f -> f ()
      | None -> 0
    in
    (outs, pos)

  let setPosOut (outs, pos) =
    (match outs.writer.TextPrimIO.setPos with
     | Some f -> f pos
     | None -> ());
    outs

  let filePosOut (_outs, pos) = pos

  let inputLine ins =
    match ins.reader.TextPrimIO.readVec with
    | None -> None
    | Some read_fn ->
      let rec loop acc =
        let data = read_fn 1 in
        if String.is_empty data then
          if List.is_empty acc then None
          else Some (String.concat ~sep:"" (List.rev acc), ins)
        else
          let c = String.get data 0 in
          if Char.(c = '\n') then
            Some (String.concat ~sep:"" (List.rev (data :: acc)), ins)
          else
            loop (data :: acc)
      in
      loop []

  let outputSubstr (outs, ss) =
    let s = Substring.Substring.string ss in
    output (outs, s)
end
