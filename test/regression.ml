
(* Quiet regression test *)
(* Does not call "use", exits when it is done: suitable for mlton or sml/nj *)
(* Author: Robert J. Simmons *)
module RegressionTest =
  struct
    let _ = Twelf.chatter := 0
    let errors = ref 0
    let rec reportError file =
      ((!) ((:=) errors) errors) + 1;
      print (("Regression test failed on " ^ file) ^ "\n")
    let rec test file =
      let _ = print ("Test:        " ^ file) in
      let stat = try Twelf.make file with | _ -> Twelf.ABORT in
      match stat with
      | Twelf.OK -> Twelf.OK
      | Twelf.ABORT -> (reportError file; Twelf.ABORT)
    let rec testUnsafe file =
      let _ = print ("Test Unsafe: " ^ file) in
      let _ = Twelf.unsafe := true in
      let stat = try Twelf.make file with | e -> Twelf.ABORT in
      let _ = Twelf.unsafe := false in
      match stat with
      | Twelf.OK -> Twelf.OK
      | Twelf.ABORT -> (reportError file; Twelf.ABORT)
    let (conclude : unit -> OS.Process.status) =
      function
      | () ->
          let err = !errors in
          (errors := 0;
           (match err with
            | 0 ->
                (print "Test complete with no errors\n"; OS.Process.success)
            | 1 -> (print "Test complete with 1 error\n"; OS.Process.failure)
            | n ->
                (print
                   (("Test complete with " ^ (Int.toString n)) ^ " errors\n");
                 OS.Process.failure)))
    let rec process filename =
      let file = TextIO.openIn filename in
      let rec runline (str : string) =
        if String.isPrefix "#" str
        then None
        else
          if String.isPrefix "testUnsafe" str
          then
            Some
              (testUnsafe
                 (String.extract (str, 11, (Some ((String.size str) - 12)))))
          else
            if String.isPrefix "test" str
            then
              Some
                (test
                   (String.extract (str, 5, (Some ((String.size str) - 6)))))
            else None in
      let exception Aborted  in
        let rec getstatus (status, msg) =
          match status with
          | None -> ()
          | Some (Twelf.OK) -> print ("..." ^ msg)
          | Some (Twelf.ABORT) -> print ("...ABORT!\n"; raise Aborted) in
        let rec readfile () =
          match TextIO.inputLine file with
          | None -> (TextIO.closeIn file; conclude ())
          | Some s ->
              (try
                 Twelf.doubleCheck := false;
                 getstatus ((runline s), "OK.\n");
                 Twelf.doubleCheck := true;
                 getstatus ((runline s), "Double checked.\n");
                 readfile ()
               with | Aborted -> readfile ()) in
        ((readfile ())(* Ignore any non-standard line *))
  end;;
