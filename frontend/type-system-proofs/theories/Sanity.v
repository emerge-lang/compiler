(** Placeholder theory, only here so that the build and the CI job have something to chew on
    before the first real theory exists. Delete it once [theories/] holds actual content. *)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
