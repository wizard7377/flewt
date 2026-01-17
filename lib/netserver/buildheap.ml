
;;NetServer.setExamplesDir "/usr0/stuff/twelf-cvs/examples"
let rec httpServer _ =
  NetServer.httpServer 1066 "/usr0/stuff/twelf-cvs/src/netserver/htdocs";
  OS.Process.success ;;SMLofNJ.exportFn ("netserver.heap", httpServer);;
