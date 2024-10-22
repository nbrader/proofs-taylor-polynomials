Require Import Coq.Reals.Reals.
Require Import Psatz.


Theorem le_equiv : forall (n m : nat), (exists (k : nat), (n + k)%nat = m) <-> (n <= m)%nat.
Proof.
  split.
  - intros.
    destruct H.
    rewrite <- H.
    apply Nat.le_add_r.
  - intros.
    induction n, m.
    + simpl.
      exists 0%nat.
      reflexivity.
    + simpl.
      exists (S m).
      reflexivity.
    + inversion H.
    + apply le_S_n in H.
      apply le_S in H as H0.
      apply IHn in H0. clear IHn.
      destruct H0 as [k H0].
      assert (k <> 0%nat).
      {
        lia.
        (* unfold not.
        intros.
        rewrite H1 in H0. clear H1.
        replace (n + 0)%nat with n in H0 by ring.
        rewrite H0 in H. *)
      }
      destruct k.
      * contradiction.
      * clear H1.
        exists k.
        rewrite <- H0. clear H0.
        rewrite (Nat.add_comm n (S k)).
        simpl.
        rewrite (Nat.add_comm k n).
        reflexivity.
Qed.
