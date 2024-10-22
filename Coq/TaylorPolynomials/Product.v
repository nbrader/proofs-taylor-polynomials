Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.
Require Import CoqUtilLib.Iteration.

(*
  Make mconcat taking monoid, a function from the naturals to the monoid and the successor of the last input to that function and use it instead of product.
  Define the monoid of reals under addition, the monoid of functions from the reals to the reals under point-wise addition.
*)
Fixpoint product (F_ : nat -> nat -> nat) (n : nat) : nat -> nat := fun (x : nat) =>
  match n with
    | O => 1
    | S n' => (F_ n' x * product F_ n' x)
  end.

Fixpoint product_nat (c_ : nat -> nat) (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => c_ n' * product_nat c_ n'
  end.

Lemma product_app :
  forall (F_ : nat -> nat -> nat) (n : nat) (x : nat),
    product F_ n x = product_nat (fun i => F_ i x) n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma product_expand_lower :
  forall (F_ : nat -> nat -> nat) (n : nat) (x : nat),
    product F_ (S n) x = product (fun i x' => F_ (S i) x') n x * F_ O x.
Proof.
  intros.
  induction n.
  - simpl.
    ring.
  (* - replace (product F_ (S (S n)) x) with (F_ (S n) x + product F_ (S n) x) by auto. *)
  - replace (product (fun (i : nat) (x' : nat) => F_ (S i) x') (S n) x) with (F_ (S n) x * product (fun (i : nat) (x' : nat) => F_ (S i) x') n x) by auto.
    rewrite <- Nat.mul_assoc.
    rewrite <- IHn. clear IHn.
    reflexivity.
Qed.

Lemma product_expand_lower_extensional :
  forall (F_ : nat -> nat -> nat) (n : nat),
    product F_ (S n) = fun x => product (fun i x' => F_ (S i) x') n x * F_ O x.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply product_expand_lower.
Qed.

Lemma product_irrelavance_of_large_coeffs :
  forall (n : nat) (F_ G_ : nat -> nat -> nat),

  (forall (i : nat), (i <= n)%nat -> F_ i = G_ i) ->
    product F_ (S n) = product G_ (S n).
Proof.
  intros.
  simpl.
  rewrite (H n) by auto.
  apply functional_extensionality.
  intros.
  f_equal.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    + rewrite (H n) by auto.
      reflexivity.
    + intros.
      rewrite H by auto.
      reflexivity.
Qed.
