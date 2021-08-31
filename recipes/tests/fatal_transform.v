(** This file tests for immediate exit: when not going through the
    Docutils pipeline, all errors are immediately fatal.

    To run:
       alectryon fatal_transform.v --frontend coq -o - > /dev/null \
         2> fatal_transform.v.out; echo "exit: $?" >> fatal_transform.v.out
           # Plain Coq → HTML + errors; produces ‘fatal_transform.v.out’ **)

Goal True. (* -.g#4 *)
