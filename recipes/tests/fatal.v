(** This file tests for immediate exit: when not going through the
    Docutils pipeline, all errors are immediately fatal.

    To run:
       alectryon fatal.v --frontend coq -o - > /dev/null \
         2> fatal.v.out; echo "exit: $?" >> fatal.v.out
           # Plain Coq → HTML + errors; produces ‘fatal.v.out’ **)

Goal not_found = 1.
