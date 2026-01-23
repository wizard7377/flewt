module type COMPAT_PATH  =
  sig val mkAbsolute : < path: string  ;relativeTo: string   >  -> string end