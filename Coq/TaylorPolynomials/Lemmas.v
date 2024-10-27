Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Arith.

Require Import TaylorPolynomials.Product.
Require Import Psatz.

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

Lemma fact_product_equiv : forall (i : nat), fact i = product_nat (fun x => S x) i.
Proof.
  intros.
  induction i.
  - simpl.
    reflexivity.
  - replace (fact (S i)) with ((S i) * fact i)%nat by (simpl; reflexivity).
    rewrite IHi. clear IHi.
    reflexivity.
Qed.

Lemma split_factorial_lt : forall (i m : nat), (i < m)%nat -> ((fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m).
Proof.
  intros.
  rewrite !fact_product_equiv.
  induction i, m.
  - reflexivity.
  - simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - inversion H.
  - apply le_S in H.
    apply le_S_n in H.
    apply IHi in H as H2. clear IHi.
    rewrite <- H2.
    rewrite product_nat_expand_upper at 1.
    rewrite (Nat.mul_comm (S i) (product_nat (fun x : nat => S x) i)).
    rewrite <- Nat.mul_assoc.
    f_equal.
    replace (S m - i)%nat with (S (S m - S i)).
    + rewrite product_nat_expand_lower at 1.
      replace (i + 1)%nat with (S i) by lia.
      rewrite Nat.mul_comm.
      replace (fun x : nat => (S i + S x)%nat) with (fun i0 : nat => (i + S (S i0))%nat).
      -- reflexivity.
      -- apply functional_extensionality.
         intros.
         lia.
    + destruct i.
      * simpl.
        rewrite Nat.sub_0_r.
        reflexivity.
      * apply le_S_n in H.
        simpl.
        rewrite Nat.sub_succ_r.
        rewrite Nat.succ_pred.
        --reflexivity.
        --lia.
Qed.

Lemma split_factorial_eq : forall (i m : nat), (i = m)%nat -> (fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m.
Proof.
  intros.
  rewrite H.
  replace (m - m)%nat with 0%nat by lia.
  simpl.
  replace (fact m * 1)%nat with (fact m)%nat by lia.
  reflexivity.
Qed.

Lemma le_split : forall (i m : nat), (i <= m)%nat <-> ((i < m)%nat \/ (i = m)%nat).
Proof.
    intros.
    split.
    - intros.
      destruct H.
      + right.
        reflexivity.
      + left.
        unfold lt.
        apply le_n_S.
        exact H.
    - intros.
      destruct H.
      + unfold lt in H.
        apply le_S in H.
        apply le_S_n in H.
        exact H.
      + rewrite H.
        apply le_n.
Qed.

Lemma split_factorial_le : forall (i m : nat), (i <= m)%nat -> ((fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m).
Proof.
    intros.
    apply le_split in H.
    destruct H.
    - apply split_factorial_lt.
      exact H.
    - apply split_factorial_eq.
      exact H.
Qed.

Lemma nat_total_ord : forall n m : nat, n <= m \/ n > m.
Proof.
  intros n m.
  destruct (Nat.lt_total n m) as [Hlt | [Heq | Hgt]].
  - (* Case n < m *)
    left. apply Nat.lt_le_incl. assumption.
  - (* Case n = m *)
    left. rewrite Heq. apply Nat.le_refl.
  - (* Case m < n *)
    right. assumption.
Qed.
