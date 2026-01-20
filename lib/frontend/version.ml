
module Version =
  struct
    let current_version = "1.7.1"
    let current_version_revision = "1813"
    let rec maybe __0__ __1__ =
      match (__0__, __1__) with | (true__, x) -> x | (false__, x) -> ""
    let official = BuildId.revision = current_version_revision
    let external__ = BuildId.revision = "exported"
    let version_string =
      ((((((^) (((^) ("Twelf " ^ current_version) maybe (not official) "+") ^
                  " (")
             maybe ((not external__) && (not official))
             (("r" ^ BuildId.revision) ^ ", "))
            ^ "built ")
           ^ BuildId.date)
          ^ " on ")
         ^ BuildId.hostname)
        ^ ")"
  end;;
