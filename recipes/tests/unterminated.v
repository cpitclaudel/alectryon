(* This tests the parse error returned by the literate parser:

   (** abc "xyz" *)

   To run:
      alectryon unterminated.v --backend rst > unterminated.v.out 2>&1;\
        echo "exit: $?" >> unterminated.v.out
          # Coq → reST; produces ‘unterminated.v.out’

   "This string is unterminated. *)
