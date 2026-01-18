module type IO =
  sig
    exception Io of (string * string * exn)
    exception BlockingNotSupported
    exception NonblockingNotSupported
    exception RandomAccessNotSupported
    exception ClosedStream
    type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF 

end