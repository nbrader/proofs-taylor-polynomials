Require Import Coq.Arith.Arith.

Theorem le_equiv : forall (n m : nat), (exists (k : nat), (n + k)%nat = m) <-> (n <= m)%nat.
Proof.
  split.
  - (* -> *) intros [k H].
    rewrite <- H.
    apply Nat.le_add_r.
  - (* <- *) intros H.
    induction H.
    + (* Base case: n = m *)
      exists 0%nat.
      rewrite <- plus_n_O.
      reflexivity.
    + (* Inductive case: n <= m -> n <= S m *)
      destruct IHle as [k Hk].
      exists (S k).
      rewrite <- Hk.
      rewrite plus_n_Sm.
      reflexivity.
Qed.
