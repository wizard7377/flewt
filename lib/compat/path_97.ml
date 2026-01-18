
(* Compatibility shim from Basis-current OS.Path to Basis-97 OS.Path *)
(* Author: Christopher Richards *)
module CompatPath97 : COMPAT_PATH =
  struct
    let rec mkAbsolute { path; relativeTo; relativeTo } =
      OS.Path.mkAbsolute (path, relativeTo)
  end ;;
