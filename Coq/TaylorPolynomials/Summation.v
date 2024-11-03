Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Reals.

Require Import FreeMonoid.MonoidExampleRealsPlus.
Require Import FreeMonoid.MonoidExampleExtendToFunction.

Require Import TaylorPolynomials.MonoidConcat.

Definition FunctionToRealsMonoid (A : Type) := @ExtendToFunctionMonoid A R RplusMagma RplusSemigroup RplusMonoid.

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

Definition summation_R_from_and_to (c_ : nat -> R) (n_first : nat) (n_last : nat) : R := summation_R (fun i => c_ (n_first + i)%nat) (n_last - n_first + 1)%nat.

Lemma summation_R_mconcat_equiv :
  summation_R = @mconcat _ _ _ RplusMonoid.
Proof.
  apply functional_extensionality.
  intros f.
  apply functional_extensionality.
  intros x.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma summation_mconcat_equiv :
  summation = @mconcat _ _ _ (FunctionToRealsMonoid R).
Proof.
  apply functional_extensionality.
  intros f.
  apply functional_extensionality.
  intros x.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
Qed.

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
  rewrite summation_mconcat_equiv.
  rewrite mconcat_expand_lower.
  simpl.
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

Lemma summation_R_expand_lower :
  forall (c_ : nat -> R) (n : nat),
    summation_R c_ (S n) = summation_R (fun i => c_ (S i)) n + c_ O.
Proof.
  intros.
  rewrite summation_R_mconcat_equiv.
  rewrite mconcat_expand_lower.
  simpl.
  reflexivity.
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

Lemma summation_irrelevance_of_large_coeffs :
  forall (n : nat) (F_ G_ : nat -> R -> R),

  (forall (i : nat), (i <= n)%nat -> F_ i = G_ i) ->
    summation F_ (S n) = summation G_ (S n).
Proof.
  intros.
  rewrite summation_mconcat_equiv.
  apply mconcat_irrelevance_of_large_coeffs.
  apply H.
Qed.

Lemma summation_R_irrelevance_of_large_coeffs :
  forall (n : nat) (c_ d_ : nat -> R),

  (forall (i : nat), (i <= n)%nat -> c_ i = d_ i) ->
    summation_R c_ (S n) = summation_R d_ (S n).
Proof.
  intros.
  rewrite summation_R_mconcat_equiv.
  apply mconcat_irrelevance_of_large_coeffs.
  apply H.
Qed.

Lemma summation_n_zeros (n : nat):
  summation_R (fun _ => 0) n = 0.
Proof.
  intros.
  rewrite summation_R_mconcat_equiv.
  apply mconcat_n_identities.
Qed.

Lemma split_summation_R (c_ : nat -> R) (i n : nat) :
   (i <= n)%nat -> summation_R c_ n  = summation_R (fun j => c_ (j+i)%nat) (n-i) + summation_R c_ i.
Proof.
  intros.
  rewrite summation_R_mconcat_equiv.
  apply split_mconcat.
  apply H.
Qed.
