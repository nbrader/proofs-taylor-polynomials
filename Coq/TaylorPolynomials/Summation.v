Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Psatz.

Import ListNotations.

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

(* Triangular summation: sum of (i, j) where i + j <= n

   Proof strategy: Both sides sum f(i,j) over the same triangular region {(i,j) : i+j ≤ n},
   just enumerated differently:
   - LHS: row-by-row (i, then j)
   - RHS: diagonal-by-diagonal (k = i+j, then i)

   The bijection is: (i,j) ↔ (k=i+j, i)

   Since addition is associative and commutative, the order of summation doesn't matter,
   so both orderings yield the same result. *)

(* Step 1: ASSUME a general lemma about rearranging sums

   Key insight: If two double sums enumerate the same sequence of terms (possibly in
   different orders), then by commutativity and associativity of addition, they must
   be equal.

   For our specific case: both sides sum exactly the terms {f(i,j) : i+j ≤ n}, just
   enumerated differently (row-by-row vs diagonal-by-diagonal). *)

(* Proof that permutations preserve sums.
   Strategy: Induction on the Permutation relation.
   - Empty lists: trivial
   - Equal prefix (perm_skip): uses inductive hypothesis
   - Swap: uses commutativity and associativity of Rplus
   - Transitivity: uses transitivity of equality *)
Theorem sum_permutation_invariant : forall (terms1 terms2 : list R),
  Permutation terms1 terms2 ->
  fold_right Rplus 0 terms1 = fold_right Rplus 0 terms2.
Proof.
  intros terms1 terms2 H_perm.
  induction H_perm as [ | x l1 l2 H_perm IH | x y l | l1 l2 l3 H_perm12 IH12 H_perm23 IH23].

  - (* Case: perm_nil - empty lists *)
    simpl.
    reflexivity.

  - (* Case: perm_skip - equal prefix x, remainder l1 and l2 are permutations *)
    simpl.
    rewrite IH.
    reflexivity.

  - (* Case: perm_swap - swap x and y *)
    simpl.
    (* Goal: x + (y + fold_right Rplus 0 l) = y + (x + fold_right Rplus 0 l) *)
    ring.

  - (* Case: perm_trans - transitivity *)
    (* We have: l1 permutes to l2, l2 permutes to l3 *)
    (* IH12: fold_right Rplus 0 l1 = fold_right Rplus 0 l2 *)
    (* IH23: fold_right Rplus 0 l2 = fold_right Rplus 0 l3 *)
    rewrite IH12.
    rewrite IH23.
    reflexivity.
Qed.

(* If two lists have the same count for all elements, they are permutations.
   This is a general result about multisets - we axiomatize it for now but it
   can be proved constructively using induction on the structure of lists. *)
Axiom count_occ_eq_impl_Permutation : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
  (forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x) ->
  Permutation l1 l2.

(* Theorem: If two lists contain the same multiset of elements (same count_occ),
   then their sums are equal.
   Proof: Equal count_occ implies permutation, permutations preserve sums. *)
Theorem sum_enumeration_invariant : forall (terms1 terms2 : list R),
  (* If two lists contain the same multiset of elements *)
  (forall x, count_occ Req_EM_T terms1 x = count_occ Req_EM_T terms2 x) ->
  (* Then their sums are equal *)
  fold_right Rplus 0 terms1 = fold_right Rplus 0 terms2.
Proof.
  intros terms1 terms2 H_count_eq.
  (* First, show that equal count_occ implies the lists are permutations *)
  assert (H_perm: Permutation terms1 terms2).
  { apply (count_occ_eq_impl_Permutation R Req_EM_T). apply H_count_eq. }
  (* Then apply our permutation invariance theorem *)
  apply sum_permutation_invariant.
  exact H_perm.
Qed.

(* Step 2: USE the assumed lemma to prove summation_R_triangular *)

Lemma summation_R_triangular : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n) =
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n).
Proof.
  intros f n.
  (* This will be proved below using permutation invariance *)
Admitted.

(* Step 3: Now REMOVE the axiom by actually proving it.
   The proof will show both sides sum the same terms by enumerating the bijection. *)

(* Helper lemma: When we extend the inner sum from (n-i+1) to (Sn-i+1), we add exactly one term *)
Lemma extend_inner_sum : forall (f : nat -> nat -> R) (i n : nat),
  (i <= S n)%nat ->
  summation_R (fun j => f i j) (S n - i + 1) =
  summation_R (fun j => f i j) (n - i + 1) + f i (S n - i)%nat.
Proof.
  intros f i n Hi.
  destruct (le_lt_dec i n) as [Hi_le_n | Hi_gt_n].
  - (* Case: i <= n, so both sums are non-empty and the second is one element larger *)
    replace (S n - i + 1)%nat with (S (n - i + 1))%nat by lia.
    simpl.
    replace (n - i)%nat with (S n - i - 1)%nat at 2 by lia.
    (* Hmm, this is getting messy with the indices *)
Admitted.

Lemma prove_reindex_triangular : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n) =
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n).
Proof.
  intros f n.
  (* Proof by induction on n *)
  induction n as [|n IHn].
  - (* Base case: n = 0, both sides sum only f(0,0) *)
    simpl.
    replace (1 - 0)%nat with 1%nat by lia.
    replace (0 - 0)%nat with 0%nat by lia.
    simpl.
    ring.
  - (* Inductive step: Going from n to S n, both sides add the diagonal i+j = S n *)

    (* Expand LHS: summation_R ... (S (S n)) *)
    simpl summation_R at 1.
    (* LHS = (term for i = S n) + (sum for i = 0 to n with updated bounds) *)

    replace (S n - S n + 1)%nat with 1%nat by lia.
    simpl summation_R at 1.
    replace (S n - S n)%nat with 0%nat by lia.
    (* Now LHS = f (S n) 0 + summation_R (fun i => summation_R (fun j => f i j) (S n - i + 1)) (S n) *)

    (* Expand RHS: summation_R ... (S (S n)) *)
    simpl summation_R at 2.
    (* RHS = (term for k = S n) + (sum for k = 0 to n) *)
    (* Term for k = S n is: summation_R (fun i => f i (S n - i)) (S n + 1) *)

    (* Key observation: The term summation_R (fun i => f i (S n - i)) (S n + 1)
       sums the entire diagonal i+j = S n.

       But on the LHS, this diagonal is split across:
       - f (S n) 0 (the new row)
       - Plus one new element in each existing row i=0...n

       We need to show these are the same. *)

    (* This requires showing:
       f (S n) 0 + [sum of new elements from extending each row] = summation_R (fun i => f i (S n - i)) (S n + 1) *)

    (* The "new elements from extending each row" need to be extracted from the updated LHS sum.
       This is getting complex - we need auxiliary lemmas about splitting sums. *)
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
