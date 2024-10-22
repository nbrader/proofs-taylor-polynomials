Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.
Require Import CoqUtilLib.Iteration.

(*
  Make mconcat taking monoid, a function from the naturals to the monoid and the successor of the last input to that function and use it instead of summation.
  Define the monoid of reals under addition, the monoid of functions from the reals to the reals under point-wise addition.
*)
Fixpoint summation (F_ : nat -> R -> R) (n : nat) : R -> R := fun (x : R) =>
  match n with
    | O => 0
    | S n' => F_ n' x + summation F_ n' x
  end.

Fixpoint summation_R (c_ : nat -> R) (n : nat) : R :=
  match n with
    | O => 0
    | S n' => c_ n' + summation_R c_ n'
  end.

Lemma summation_app :
  forall (F_ : nat -> R -> R) (n : nat) (x : R),
    summation F_ n x = summation_R (fun i => F_ i x) n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma summation_expand_lower :
  forall (F_ : nat -> R -> R) (n : nat) (x : R),
    summation F_ (S n) x = summation (fun i x' => F_ (S i) x') n x + F_ O x.
Proof.
  intros.
  induction n.
  - simpl.
    ring.
  (* - replace (summation F_ (S (S n)) x) with (F_ (S n) x + summation F_ (S n) x) by auto. *)
  - replace (summation (fun (i : nat) (x' : R) => F_ (S i) x') (S n) x) with (F_ (S n) x + summation (fun (i : nat) (x' : R) => F_ (S i) x') n x) by auto.
    rewrite Rplus_assoc.
    rewrite <- IHn. clear IHn.
    reflexivity.
Qed.

Lemma summation_expand_lower_extensional :
  forall (F_ : nat -> R -> R) (n : nat),
    summation F_ (S n) = fun x => summation (fun i x' => F_ (S i) x') n x + F_ O x.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply summation_expand_lower.
Qed.
Lemma distr_over_summation :
  forall (n : nat) (F_ : nat -> R -> R) (s x : R),
    s * (summation F_ n) x = summation (fun i x' => s * (F_ i x')) n x.
Proof.
  intros.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl.
    field.
  
  - (* Inductive step: n -> S n *)
    simpl.
    rewrite <- IH.
    field.
Qed.

Lemma summation_irrelavance_of_large_coeffs :
  forall (n : nat) (F_ G_ : nat -> R -> R),

  (forall (i : nat), (i <= n)%nat -> F_ i = G_ i) ->
    summation F_ (S n) = summation G_ (S n).
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
