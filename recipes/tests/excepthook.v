(** This file tests the hook installed in sys.excepthook.

    To run:

       alectryon not_found.v --frontend coq \
         --traceback -o - 2>&1 | \
         sed 's/File ".\+\?", line [0-9]\+/File …, line …/g' | \
         sed '/^    /d' | sed '/^ *$/d' | uniq | \
         cat > excepthook.v.out; ! test $? -eq 0
           # Plain Coq → HTML + errors; produces ‘excepthook.v.out’ **)
