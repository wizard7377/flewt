
module CompatPath97 : COMPAT_PATH =
  struct
    let rec mkAbsolute { path; relativeTo; relativeTo } =
      OS.Path.mkAbsolute (path, relativeTo)
  end ;;
