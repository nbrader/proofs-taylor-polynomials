Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Reals.
Require Import Psatz.

Require Import FreeMonoid.MonoidExampleRealsPlus.
Require Import FreeMonoid.MonoidExampleExtendToFunction.

Require Import FreeMonoid.MonoidConcat.

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

(* ====== Summation Rearrangement Lemmas ====== *)

(* Summation with a constant factor *)
Lemma summation_R_mult_const : forall (c : R) (f : nat -> R) (n : nat),
  summation_R (fun i => c * f i) n = c * summation_R f n.
Proof.
  intros c f n.
  induction n as [|n IHn].
  - simpl. ring.
  - simpl. rewrite IHn. ring.
Qed.

(* Summation of sum equals sum of summations *)
Lemma summation_R_plus : forall (f g : nat -> R) (n : nat),
  summation_R (fun i => f i + g i) n = summation_R f n + summation_R g n.
Proof.
  intros f g n.
  induction n as [|n IHn].
  - simpl. ring.
  - simpl. rewrite IHn. ring.
Qed.

(* Double summation exchange (Fubini's theorem for finite sums) *)
Lemma summation_R_exchange : forall (f : nat -> nat -> R) (n m : nat),
  summation_R (fun i => summation_R (fun j => f i j) m) n =
  summation_R (fun j => summation_R (fun i => f i j) n) m.
Proof.
  intros f n m.
  induction n as [|n IHn].
  - (* Base case: n = 0 *)
    simpl.
    symmetry.
    apply summation_n_zeros.
  - (* Inductive step *)
    simpl.
    rewrite IHn.
    clear IHn.
    (* Now we have: summation_R (fun j => summation_R (fun i => f i j) n) m + summation_R (fun j => f n j) m *)
    (* Goal: summation_R (fun j => summation_R (fun i => f i j) (S n)) m *)
    (* Since summation_R g (S n) = g n + summation_R g n, we need to show:
       summation_R (fun j => summation_R (fun i => f i j) n + f n j) m *)
    symmetry.
    rewrite summation_R_plus.
    reflexivity.
Qed.

(* Index shift: summation from k to n+k *)
Lemma summation_R_shift_range : forall (f : nat -> R) (n k : nat),
  summation_R (fun i => f (i + k)%nat) n =
  summation_R (fun i => f i) (n + k) - summation_R (fun i => f i) k.
Proof.
  intros f n k.
  assert (H_split: summation_R f (n + k) = summation_R (fun j => f (j + k)%nat) ((n + k) - k) + summation_R f k).
  { apply split_summation_R. lia. }
  replace ((n + k) - k)%nat with n in H_split by lia.
  (* H_split: summation_R f (n + k) = summation_R (fun j => f (j + k)%nat) n + summation_R f k *)
  (* Rearrange to: summation_R (fun j => f (j + k)%nat) n = summation_R f (n + k) - summation_R f k *)
  assert (H_rearranged: summation_R (fun j => f (j + k)%nat) n = summation_R f (n + k) - summation_R f k).
  { rewrite H_split. ring. }
  exact H_rearranged.
Qed.

(* Triangular summation: sum of (i, j) where i + j <= n *)
Lemma summation_R_triangular : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n) =
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n).
Proof.
  intros f n.
  (* This requires careful index manipulation *)
  (* Let's prove it by induction on n *)
  induction n as [|n IHn].
  - (* Base case: n = 0 *)
    simpl.
    replace (1 - 0)%nat with 1%nat by lia.
    replace (0 - 0)%nat with 0%nat by lia.
    simpl.
    ring.
  - (* Inductive step *)
    (* This is complex - we'll need auxiliary lemmas *)
Admitted.

(* Rectangular to triangular summation conversion *)
Lemma summation_R_rect_to_tri : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun i => summation_R (fun j => f i j) (S n)) (S n) =
  summation_R (fun i => summation_R (fun j => f i j) (i + 1)) (S n) +
  summation_R (fun i => summation_R (fun j => f j i) (n - i + 1)) n.
Proof.
  intros f n.
  (* Split the rectangular region into lower and upper triangular parts *)
Admitted.

(* Change of variable in double sum *)
Lemma summation_R_change_of_var : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (min k n + 1)) (S n) =
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n).
Proof.
  intros f n.
  (* This is the key lemma for binomial expansion *)
  (* We need to show that summing over pairs (i, k-i) where 0 <= i <= k <= n *)
  (* is the same as summing over pairs (i, j) where 0 <= i <= n and 0 <= j <= n-i *)
Admitted.
