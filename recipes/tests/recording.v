(* To compile:
     alectryon recording.v --frontend coq --backend json
       # Coq → JSON; produces ‘recording.v.io.json’ *)
Goal True.
  idtac "test".
  exact I.
Qed.
