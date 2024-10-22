Require Import Coq.Reals.Reals.

Theorem le_equiv : forall (n m : nat), (exists (k : nat), (n + k)%nat = m) <-> (n <= m)%nat.
Proof.
  split.
  - intros.
    destruct H.
    rewrite <- H.
    apply Nat.le_add_r.
  - intros.
    admit.
Admitted.
