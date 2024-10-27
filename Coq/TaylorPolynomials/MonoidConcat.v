Require Import Coq.Logic.FunctionalExtensionality.
Require Import Arith.
Require Import Ring.
Require Import Coq.ssr.ssrfun.

Require Import FreeMonoid.StructMonoid.


(*
  Make mconcat taking monoid, a function from the naturals to the monoid and the successor of the last input to that function and use it instead of product.
  Define the monoid of reals under addition, the monoid of functions from the reals to the reals under point-wise addition.
*)

Fixpoint mconcat (A : Type) `{Hmon : Monoid A} (c_ : nat -> A) (n : nat) : A :=
  match n with
    | O => mn_id
    | S n' => m_op (c_ n') (mconcat A c_ n')
  end.

Lemma mconcat_expand_lower :
  forall (A : Type) `{Hmon : Monoid A} (F_ : nat -> A) (n : nat),
    mconcat A F_ (S n) = m_op (mconcat A (fun i => F_ (S i)) n) (F_ O).
Proof.
  intros.
  induction n.
  - simpl.
    rewrite mn_left_id.
    rewrite mn_right_id.
    reflexivity.
  - replace (mconcat A (fun (i : nat) => F_ (S i)) (S n)) with (m_op (F_ (S n)) (mconcat A (fun (i : nat) => F_ (S i)) n)) by auto.
    rewrite <- sg_assoc.
    rewrite <- IHn. clear IHn.
    reflexivity.
Qed.

Lemma mconcat_irrelevance_of_large_coeffs :
  forall (A : Type) `{Hmon : Monoid A} (n : nat) (F_ G_ : nat -> A),
  (forall (i : nat), (i <= n)%nat -> F_ i = G_ i) ->
    mconcat A F_ (S n) = mconcat A G_ (S n).
Proof.
  intros.
  simpl.
  rewrite (H1 n) by auto.
  f_equal.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    + rewrite (H1 n) by auto.
      reflexivity.
    + intros.
      rewrite H1 by auto.
      reflexivity.
Qed.

Lemma mconcat_n_identities (A : Type) `{Hmon : Monoid A} (n : nat) :
  mconcat A (fun _ => mn_id) n = mn_id.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    simpl.
    rewrite mn_left_id.
    reflexivity.
Qed.

Lemma split_mconcat (A : Type) `{Hmon : Monoid A} (c_ : nat -> A) (i n : nat) :
   (i <= n)%nat -> mconcat A c_ n  = m_op (mconcat A (fun j => c_ (j+i)) (n-i)) (mconcat A c_ i).
Proof.
    intros max_i_is_n.
    induction i.
    - simpl.
      rewrite mn_right_id.
      assert ((fun j : nat => c_ (j + 0)) = c_).
      {
        apply functional_extensionality.
        intros.
        replace (x+0) with x by ring.
        reflexivity.
      }
      rewrite H1. clear H1.
      rewrite Nat.sub_0_r.
      reflexivity.
    - apply le_S in max_i_is_n as H1.
      apply le_S_n in H1.
      apply IHi in H1 as H1. clear IHi.

      simpl.
      rewrite H1.
      rewrite <- Nat.sub_succ.
      rewrite Nat.sub_succ_l by apply max_i_is_n.
      rewrite mconcat_expand_lower.

      rewrite <- sg_assoc.

      replace (0 + i) with i by ring.
      replace (fun i0 : nat => c_ (S i0 + i)) with (fun j : nat => c_ (j + S i)).
      + reflexivity.
      + apply functional_extensionality. intros.
        replace (x + S i) with (S x + i) by ring.
        reflexivity.
Qed.
