Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rfunctions.
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
   Proof strategy: Induction on l1.
   - Base case: l1 = [] implies l2 = [] (since count 0 for all elements)
   - Inductive case: l1 = a :: l1'
     * a appears in l2 (since count > 0)
     * Remove one occurrence of a from both lists
     * Apply inductive hypothesis to remainder
     * Use Permutation_cons to conclude *)

(* Helper: if count_occ is 0 for all elements, the list is empty *)
Lemma count_occ_zero_impl_nil : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
  (forall x, count_occ eq_dec l x = 0%nat) ->
  l = [].
Proof.
  intros A eq_dec l H.
  destruct l as [|a l'].
  - reflexivity.
  - (* l = a :: l', but count_occ for a should be > 0 *)
    specialize (H a).
    simpl in H.
    destruct (eq_dec a a) as [_ | Hneq].
    + (* a = a, so count_occ is S _, contradicts H *)
      discriminate H.
    + (* a <> a is absurd *)
      contradiction.
Qed.

(* Helper: if count_occ l1 a > 0, then a is in l1 *)
Lemma count_occ_pos_impl_In : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (a : A),
  (count_occ eq_dec l a > 0)%nat ->
  In a l.
Proof.
  intros A eq_dec l a H.
  induction l as [|b l' IH].
  - simpl in H. lia.
  - simpl in H.
    destruct (eq_dec b a) as [Heq | Hneq].
    + (* b = a, so a = b by symmetry *)
      left. exact Heq.
    + (* b <> a, so a must be in l' *)
      right. apply IH. exact H.
Qed.

(* Main theorem: equal count_occ implies Permutation *)
Theorem count_occ_eq_impl_Permutation : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
  (forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x) ->
  Permutation l1 l2.
Proof.
  intros A eq_dec l1.
  induction l1 as [|a l1' IH]; intros l2 H_count.

  - (* Base case: l1 = [] *)
    (* All counts in l2 must be 0, so l2 = [] *)
    assert (H_l2_nil: l2 = []).
    { apply (count_occ_zero_impl_nil A eq_dec).
      intros x. specialize (H_count x). simpl in H_count. symmetry. exact H_count. }
    rewrite H_l2_nil.
    apply perm_nil.

  - (* Inductive case: l1 = a :: l1' *)
    (* a must appear in l2 since count_occ (a :: l1') a > 0 *)
    assert (H_a_in_l2: In a l2).
    { apply (count_occ_pos_impl_In A eq_dec).
      rewrite <- (H_count a).
      simpl. destruct (eq_dec a a) as [_ | Hneq].
      - lia.
      - contradiction. }

    (* Split l2 into before and after a *)
    apply in_split in H_a_in_l2.
    destruct H_a_in_l2 as [l2_before [l2_after H_l2_split]].
    rewrite H_l2_split.

    (* Show that a :: l1' is a permutation of a :: (l2_before ++ l2_after) *)
    (* First, show l1' is a permutation of (l2_before ++ l2_after) *)
    assert (H_perm_rest: Permutation l1' (l2_before ++ l2_after)).
    { apply IH.
      intros x.
      specialize (H_count x).
      simpl in H_count.
      rewrite H_l2_split in H_count.
      rewrite count_occ_app in H_count.
      simpl in H_count.
      destruct (eq_dec a x) as [Heq | Hneq].
      - (* x = a: subtract 1 from both sides *)
        rewrite count_occ_app.
        rewrite <- Heq.
        rewrite <- Heq in H_count.
        simpl in H_count.
        destruct (eq_dec a a) as [_ | Hneq'].
        + lia.
        + contradiction.
      - (* x <> a: equation holds directly *)
        rewrite count_occ_app.
        exact H_count. }

    (* Use Permutation_middle to permute a to its position *)
    (* We have: Permutation l1' (l2_before ++ l2_after) *)
    (* We want: Permutation (a :: l1') (l2_before ++ a :: l2_after) *)
    (* Strategy: a :: l1' ~ a :: (l2_before ++ l2_after) ~ l2_before ++ a :: l2_after *)
    apply perm_trans with (a :: (l2_before ++ l2_after)).
    + apply perm_skip. exact H_perm_rest.
    + apply Permutation_middle.
Qed.

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

(* Step 2: Triangular summation reindexing will be proved below after helper lemmas *)

(* Helper lemma: When we extend the inner sum from (n-i+1) to (Sn-i+1), we add exactly one term *)
Lemma extend_inner_sum : forall (f : nat -> nat -> R) (i n : nat),
  (i <= n)%nat ->
  summation_R (fun j => f i j) (S n - i + 1) =
  summation_R (fun j => f i j) (n - i + 1) + f i (S n - i)%nat.
Proof.
  intros f i n Hi.
  (* Key insight: S n - i + 1 = S (n - i + 1) when i <= n *)
  replace (S n - i + 1)%nat with (S (n - i + 1))%nat by lia.
  (* Expand summation_R (S m) = (m-th term) + summation_R m *)
  simpl.
  (* The index of the new term is (n - i + 1), which equals S n - i when i <= n *)
  replace (n - i + 1)%nat with (S n - i)%nat by lia.
  (* Now both sides are equal by commutativity of addition *)
  rewrite Rplus_comm.
  reflexivity.
Qed.

(* Helper: Convert double summation to flat list via concatenation *)
Fixpoint double_sum_to_list_rows (f : nat -> nat -> R) (i_max : nat) (j_func : nat -> nat) : list R :=
  match i_max with
  | O => []
  | S i' => double_sum_to_list_rows f i' j_func ++
            map (fun j => f i' j) (seq 0 (j_func i'))
  end.

Fixpoint double_sum_to_list_diags (f : nat -> nat -> R) (k_max : nat) : list R :=
  match k_max with
  | O => []
  | S k' => double_sum_to_list_diags f k' ++
            map (fun i => f i (k' - i)%nat) (seq 0 (k' + 1))
  end.

(* Helper: fold_right with different initial values *)
Lemma fold_right_Rplus_init : forall (l : list R) (a : R),
  fold_right Rplus a l = fold_right Rplus 0 l + a.
Proof.
  intros l a.
  induction l as [|x xs IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(* Helper: fold_right over append splits into sum *)
Lemma fold_right_Rplus_app : forall (l1 l2 : list R),
  fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(* Helper: sum of map equals summation_R *)
Lemma sum_map_seq : forall (g : nat -> R) (n : nat),
  fold_right Rplus 0 (map g (seq 0 n)) = summation_R g n.
Proof.
  intros g n.
  induction n as [|n IHn].
  - simpl. reflexivity.
  - rewrite seq_S.
    rewrite map_app.
    rewrite fold_right_app.
    simpl fold_right.
    rewrite Rplus_0_r.
    rewrite fold_right_Rplus_init.
    rewrite IHn.
    simpl summation_R.
    ring.
Qed.

(* Helper: Unfolding lemma for double_sum_to_list_rows *)
Lemma double_sum_to_list_rows_unfold : forall (f : nat -> nat -> R) (n : nat) (j_func : nat -> nat),
  double_sum_to_list_rows f (S n) j_func =
  double_sum_to_list_rows f n j_func ++ map (fun j => f n j) (seq 0 (j_func n)).
Proof.
  intros f n j_func.
  unfold double_sum_to_list_rows at 1.
  reflexivity.
Qed.

(* General version: Row-by-row enumeration for arbitrary j_func *)
Lemma row_list_sum_general : forall (f : nat -> nat -> R) (n : nat) (j_func : nat -> nat),
  fold_right Rplus 0 (double_sum_to_list_rows f n j_func) =
  summation_R (fun i => summation_R (fun j => f i j) (j_func i)) n.
Proof.
  intros f n j_func.
  induction n as [|n IHn].

  - (* Base case: n = 0 *)
    unfold double_sum_to_list_rows.
    simpl.
    reflexivity.

  - (* Inductive case: n -> S n *)
    rewrite (double_sum_to_list_rows_unfold f n j_func).
    rewrite fold_right_Rplus_app.
    rewrite IHn.
    rewrite sum_map_seq.
    simpl summation_R.
    ring.
Qed.

(* Key lemma: Row-by-row enumeration equals nested summation_R

   This is now a simple corollary of the general version.
*)
Lemma row_list_sum_correct : forall (f : nat -> nat -> R) (n : nat),
  fold_right Rplus 0 (double_sum_to_list_rows f (S n) (fun i => (n - i + 1)%nat)) =
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n).
Proof.
  intros f n.
  apply row_list_sum_general.
Qed.

(* Helper: Unfolding lemma for double_sum_to_list_diags *)
Lemma double_sum_to_list_diags_unfold : forall (f : nat -> nat -> R) (n : nat),
  double_sum_to_list_diags f (S n) =
  double_sum_to_list_diags f n ++ map (fun i => f i (n - i)%nat) (seq 0 (n + 1)).
Proof.
  intros f n.
  unfold double_sum_to_list_diags at 1.
  reflexivity.
Qed.

(* Key lemma: Diagonal-by-diagonal enumeration equals nested summation_R

   Similar to row_list_sum_correct, but for diagonal enumeration.
   The structure is actually simpler because diagonals have a uniform
   indexing pattern using Cantor pairing.

   Strategy:
   - Base case (n=0): Both sides equal f(0,0)
   - Inductive case: Show that appending a new diagonal corresponds
     to adding a new summation term for k = n
   - Use sum_map_seq for the inner summation over i
*)
Lemma diag_list_sum_correct : forall (f : nat -> nat -> R) (n : nat),
  fold_right Rplus 0 (double_sum_to_list_diags f (S n)) =
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n).
Proof.
  intros f n.
  induction n as [|n IHn].

  - (* Base case: n = 0 *)
    unfold double_sum_to_list_diags.
    simpl fold_right.
    rewrite Rplus_0_r.
    simpl summation_R.
    replace (0 - 0)%nat with 0%nat by lia.
    simpl.
    ring.

  - (* Inductive case: n -> S n *)
    (* Manual construction using transitivity *)
    transitivity (fold_right Rplus 0 (double_sum_to_list_diags f (S n)) +
                  fold_right Rplus 0 (map (fun i => f i (S n - i)%nat) (seq 0 (S n + 1)))).

    { (* Prove LHS = intermediate form *)
      rewrite (double_sum_to_list_diags_unfold f (S n)).
      rewrite fold_right_Rplus_app.
      reflexivity.
    }

    transitivity (summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n) +
                  summation_R (fun i => f i (S n - i)%nat) (S n + 1)).

    { (* Prove intermediate = another intermediate using IH and sum_map_seq *)
      rewrite IHn.
      rewrite sum_map_seq.
      reflexivity.
    }

    { (* Prove final intermediate = RHS *)
      simpl.
      ring.
    }
Qed.

(* Helper: count_occ distributes over append *)
Lemma count_occ_app : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) (x : A),
  count_occ eq_dec (l1 ++ l2) x = (count_occ eq_dec l1 x + count_occ eq_dec l2 x)%nat.
Proof.
  intros A eq_dec l1 l2 x.
  induction l1 as [|a l1' IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec a x); simpl.
    + rewrite IH. reflexivity.
    + apply IH.
Qed.

(* ===== Bijection-based approach to proving summation_R_triangular =====

   Strategy: Prove that row and diagonal enumerations are permutations via bijection

   For the triangular region {(i,j) : 0 ≤ i ≤ n, 0 ≤ j ≤ n-i}, we have:
   - Row enumeration: for each i in 0..n, enumerate j in 0..(n-i)
   - Diagonal enumeration: for each k in 0..n, enumerate i in 0..k, with j = k-i

   These are related by the bijection: (i,j) ↔ (k=i+j, i)

   Proof outline:
   1. Define pair lists matching double_sum_to_list_* structure
   2. Prove the bijection between pairs
   3. Prove pair lists are permutations (via count_occ equality)
   4. Lift to value lists via map
   5. Use in summation_R_triangular
*)

(* Helper: Natural number summation *)
Fixpoint sum_nat (g : nat -> nat) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => g n' + sum_nat g n'
  end.

(* Pair list versions matching the structure of double_sum_to_list_* *)

(* General version: pairs enumerated row-by-row with variable row lengths *)
Fixpoint pairs_by_rows (i_max : nat) (j_func : nat -> nat) : list (nat * nat) :=
  match i_max with
  | O => []
  | S i' => pairs_by_rows i' j_func ++
            map (fun j => (i', j)) (seq 0 (j_func i'))
  end.

(* General version: pairs enumerated diagonal-by-diagonal *)
Fixpoint pairs_by_diags (k_max : nat) : list (nat * nat) :=
  match k_max with
  | O => []
  | S k' => pairs_by_diags k' ++
            map (fun i => (i, k' - i)%nat) (seq 0 (k' + 1))
  end.

(* The bijection on pairs: (i,j) ↔ (k=i+j, i) *)
Definition pair_row_to_diag (p : nat * nat) : (nat * nat) :=
  let '(i, j) := p in
  ((i + j)%nat, i).

Definition pair_diag_to_row (p : nat * nat) : (nat * nat) :=
  let '(k, i) := p in
  (i, (k - i)%nat).

(* These are inverses *)
Lemma pair_bijection_inverse_1 : forall p,
  pair_diag_to_row (pair_row_to_diag p) = p.
Proof.
  intros [i j].
  unfold pair_row_to_diag, pair_diag_to_row.
  simpl.
  f_equal.
  lia.
Qed.

Lemma pair_bijection_inverse_2 : forall p,
  let '(k, i) := p in (i <= k)%nat ->
  pair_row_to_diag (pair_diag_to_row p) = p.
Proof.
  intros [k i] Hik.
  unfold pair_diag_to_row, pair_row_to_diag.
  simpl.
  f_equal.
  lia.
Qed.

(* Key property: map preserves permutations *)
Lemma Permutation_map : forall (A B : Type) (f : A -> B) (l1 l2 : list A),
  Permutation l1 l2 ->
  Permutation (map f l1) (map f l2).
Proof.
  intros A B f l1 l2 Hperm.
  induction Hperm as [| x l1 l2 Hp IH | x y l | l1 l2 l3 Hp12 IH12 Hp23 IH23].
  - apply perm_nil.
  - simpl. apply perm_skip. exact IH.
  - simpl. apply perm_swap.
  - apply perm_trans with (map f l2); assumption.
Qed.

(* Prove value lists equal mapped pair lists *)

(* Helper: map composition *)
Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  intros A B C f g l.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Row-by-row value list equals mapped pair list *)
Lemma row_value_list_eq_mapped_pairs : forall (f : nat -> nat -> R) (n : nat) (j_func : nat -> nat),
  double_sum_to_list_rows f n j_func =
  map (fun p => f (fst p) (snd p)) (pairs_by_rows n j_func).
Proof.
  intros f n j_func.
  induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl.
    rewrite map_app.
    rewrite <- IHn.
    f_equal.
    rewrite map_map.
    reflexivity.
Qed.

(* Diagonal-by-diagonal value list equals mapped pair list *)
Lemma diag_value_list_eq_mapped_pairs : forall (f : nat -> nat -> R) (n : nat),
  double_sum_to_list_diags f n =
  map (fun p => f (fst p) (snd p)) (pairs_by_diags n).
Proof.
  intros f n.
  induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl.
    rewrite map_app.
    rewrite <- IHn.
    f_equal.
    rewrite map_map.
    reflexivity.
Qed.

(* Now prove the pair lists are permutations *)

(* Decidable equality for nat pairs *)
Definition nat_pair_eq_dec : forall (p1 p2 : nat * nat), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [i1 j1] [i2 j2].
  destruct (Nat.eq_dec i1 i2); destruct (Nat.eq_dec j1 j2).
  - left. subst. reflexivity.
  - right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
Defined.

(* The key lemma: pair lists have the same multiset

   Strategy: Prove by showing that:
   - Row enumeration contains pair (i,j) iff i ≤ n and j ≤ (n-i)
   - Diagonal enumeration contains pair (i,j) iff i+j ≤ n
   - These conditions are equivalent
   - Therefore both lists contain the same pairs with the same multiplicities
*)

(* Helper lemma: generalized version with explicit row size bounds *)
Lemma pair_in_row_list_gen : forall (i_max : nat) (j_func : nat -> nat) (i j : nat),
  (i < i_max)%nat ->
  (j < j_func i)%nat ->
  In (i, j) (pairs_by_rows i_max j_func).
Proof.
  intros i_max j_func i j.
  revert i j.
  induction i_max as [|i_max' IH]; intros i j Hi Hj.

  - (* i_max = 0: impossible since i < 0 *)
    lia.

  - (* i_max = S i_max' *)
    unfold pairs_by_rows; fold pairs_by_rows.
    apply in_or_app.

    destruct (Nat.eq_dec i i_max') as [Heq | Hneq].

    + (* i = i_max': this is the row being added *)
      right.
      subst i.
      apply in_map_iff.
      exists j.
      split.
      * reflexivity.
      * apply in_seq. lia.

    + (* i < i_max': in previous rows *)
      left.
      apply IH; lia.
Qed.

(* Now the specific lemma follows easily *)
Lemma pair_in_row_list : forall (n i j : nat),
  (i <= n)%nat -> (j < n - i + 1)%nat ->
  In (i, j) (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat)).
Proof.
  intros n i j Hi Hj.
  apply pair_in_row_list_gen; lia.
Qed.

Lemma pair_in_diag_list : forall (n i j : nat),
  (i + j <= n)%nat ->
  In (i, j) (pairs_by_diags (S n)).
Proof.
  intros n i j Hij.

  (* Identify which diagonal k contains (i,j) *)
  remember (i + j)%nat as k.

  (* Induction on n *)
  induction n as [|n' IHn].

  - (* Base case: n = 0 *)
    (* Only pair is (0,0) *)
    assert (i = 0%nat /\ j = 0%nat) as [Hi Hj] by lia.
    subst.
    unfold pairs_by_diags. simpl. left. reflexivity.

  - (* Inductive case: n' -> S n' *)
    unfold pairs_by_diags; fold pairs_by_diags.
    apply in_or_app.

    destruct (Nat.eq_dec k (S n')) as [Heq | Hneq].

    + (* k = S n': pair is on the NEW diagonal being added *)
      right.
      subst k.
      apply in_map_iff.
      exists i.
      split.
      * (* Show map produces (i, j) *)
        f_equal. lia.
      * (* Show i is in seq 0 (S n' + 1) *)
        apply in_seq. lia.

    + (* k < S n': pair is in previous diagonals *)
      left.
      apply IHn. lia.
Qed.

(* ===== NoDup (no duplicates) proofs =====

   Strategy: Show both pair enumerations have no duplicate pairs.
   This is needed to prove they are permutations via count_occ.

   Key insights:
   - Diagonals: Pairs from different diagonals have different sums (i+j)
   - Rows: Pairs from different rows have different first components (i)
*)

(* Helper: NoDup preservation through map with injective function *)
Lemma NoDup_map_injective : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros A B f l Hinj Hnodup.
  induction Hnodup as [|a l' Hnotin Hnodup' IH].
  - simpl. constructor.
  - simpl. constructor.
    + (* Show ~In (f a) (map f l') *)
      intros Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [x [Hfx Hin]].
      assert (Heq: a = x).
      { apply Hinj.
        - left. reflexivity.
        - right. exact Hin.
        - symmetry. exact Hfx. }
      subst. contradiction.
    + (* Show NoDup (map f l') *)
      apply IH.
      intros x y Hx Hy Hfxy.
      apply (Hinj x y).
      * right. exact Hx.
      * right. exact Hy.
      * exact Hfxy.
Qed.

(* Helper: seq has no duplicates *)
Lemma seq_NoDup : forall start len,
  NoDup (seq start len).
Proof.
  intros start len.
  generalize dependent start.
  induction len as [|len' IH]; intros start.
  - simpl. constructor.
  - simpl. constructor.
    + (* Show start not in seq (S start) len' *)
      intros Hcontra.
      apply in_seq in Hcontra.
      lia.
    + (* Show NoDup (seq (S start) len') *)
      apply IH.
Qed.

(* Helper: NoDup of append when lists are disjoint *)
Lemma NoDup_app_disjoint : forall (A : Type) (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> ~In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction H1 as [|a l1' Hnotin Hnodup' IH].
  - simpl. exact H2.
  - simpl. constructor.
    + intros Hcontra.
      apply in_app_or in Hcontra.
      destruct Hcontra as [Hin1 | Hin2].
      * contradiction.
      * apply (Hdisj a).
        -- left. reflexivity.
        -- exact Hin2.
    + apply IH.
      intros x Hx.
      apply Hdisj.
      right. exact Hx.
Qed.

(* Helper lemma: pairs in pairs_by_diags n have sum at most n-1 *)
Lemma pairs_by_diags_sum_bound : forall n i j,
  In (i, j) (pairs_by_diags n) ->
  (i + j <= n - 1)%nat.
Proof.
  intros n i j Hin.
  induction n as [|n' IH].

  - (* n = 0: empty list *)
    simpl in Hin. contradiction.

  - (* n = S n' *)
    unfold pairs_by_diags in Hin; fold pairs_by_diags in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin_old | Hin_new].

    + (* Pair from old diagonals: i + j ≤ n' - 1 *)
      destruct n' as [|n''].
      * simpl in Hin_old. contradiction.
      * apply IH in Hin_old. lia.

    + (* Pair from new diagonal: i + j = n' *)
      apply in_map_iff in Hin_new.
      destruct Hin_new as [i' [Heq Hin']].
      injection Heq as Hi Hj.
      subst i j.
      apply in_seq in Hin'.
      lia.
Qed.

(* Now retry NoDup for diagonal enumeration *)
Lemma pairs_by_diags_NoDup : forall (n : nat),
  NoDup (pairs_by_diags n).
Proof.
  intros n.
  induction n as [|n' IH].

  - (* Base case: n = 0 *)
    simpl. constructor.

  - (* Inductive case: n = S n' *)
    unfold pairs_by_diags; fold pairs_by_diags.
    apply NoDup_app_disjoint.

    + (* NoDup (pairs_by_diags n') *)
      exact IH.

    + (* NoDup (new diagonal) *)
      apply NoDup_map_injective.
      * (* Injectivity of (fun i => (i, n' - i)) on seq 0 (n' + 1) *)
        intros x y Hx Hy Heq.
        injection Heq as Heq1 Heq2.
        exact Heq1.
      * (* NoDup (seq 0 (n' + 1)) *)
        apply seq_NoDup.

    + (* Disjointness: pairs from old diagonals don't appear in new diagonal *)
      intros [i j] Hin Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [i' [Heq Hin']].
      injection Heq as Hi Hj.
      subst i j.
      apply in_seq in Hin'.
      (* Pair (i', n' - i') has sum n' *)
      (* But pairs in pairs_by_diags n' have sum ≤ n' - 1 *)
      destruct n' as [|n''].
      * simpl in Hin. contradiction.
      * apply pairs_by_diags_sum_bound in Hin. lia.
Qed.

(* Helper lemma: pairs in pairs_by_rows have first component < n *)
Lemma pairs_by_rows_first_bound : forall n j_func i j,
  In (i, j) (pairs_by_rows n j_func) ->
  (i < n)%nat.
Proof.
  intros n j_func i j Hin.
  induction n as [|n' IH].

  - (* n = 0: empty list *)
    simpl in Hin. contradiction.

  - (* n = S n' *)
    unfold pairs_by_rows in Hin; fold pairs_by_rows in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin_old | Hin_new].

    + (* Pair from old rows: i < n' *)
      apply IH in Hin_old. lia.

    + (* Pair from new row: i = n' *)
      apply in_map_iff in Hin_new.
      destruct Hin_new as [j' [Heq Hin']].
      injection Heq as Hi Hj.
      subst i. lia.
Qed.

(* NoDup for row enumeration *)
Lemma pairs_by_rows_NoDup : forall (n : nat) (j_func : nat -> nat),
  NoDup (pairs_by_rows n j_func).
Proof.
  intros n j_func.
  induction n as [|n' IH].

  - (* Base case: n = 0 *)
    simpl. constructor.

  - (* Inductive case: n = S n' *)
    unfold pairs_by_rows; fold pairs_by_rows.
    apply NoDup_app_disjoint.

    + (* NoDup (pairs_by_rows n' j_func) *)
      exact IH.

    + (* NoDup (new row) *)
      apply NoDup_map_injective.
      * (* Injectivity of (fun j => (n', j)) on seq 0 (j_func n') *)
        intros x y Hx Hy Heq.
        injection Heq. intros. assumption.
      * (* NoDup (seq 0 (j_func n') *)
        apply seq_NoDup.

    + (* Disjointness: pairs from old rows don't appear in new row *)
      intros [i j] Hin Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [j' [Heq Hin']].
      injection Heq as Hi Hj.
      subst i.
      (* Pair (n', j) has first component n' *)
      (* But pairs in pairs_by_rows n' j_func have first component < n' *)
      apply pairs_by_rows_first_bound in Hin. lia.
Qed.

(* Bound lemmas for checking membership *)
Lemma pairs_by_diags_bound : forall n i j,
  In (i, j) (pairs_by_diags n) ->
  (i + j <= n - 1)%nat.
Proof.
  intros n i j.
  apply pairs_by_diags_sum_bound.
Qed.

Lemma pairs_by_rows_bound : forall n j_func i j,
  In (i, j) (pairs_by_rows n j_func) ->
  (i <= n - 1 /\ j <= j_func i - 1)%nat.
Proof.
  intros n j_func i j Hin.
  induction n as [|n' IH].

  - (* n = 0: empty list *)
    simpl in Hin. contradiction.

  - (* n = S n' *)
    unfold pairs_by_rows in Hin; fold pairs_by_rows in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin_old | Hin_new].

    + (* Pair from old rows *)
      apply IH in Hin_old.
      destruct Hin_old as [Hi Hj].
      split; lia.

    + (* Pair from new row: i = n' *)
      apply in_map_iff in Hin_new.
      destruct Hin_new as [j' [Heq Hin']].
      injection Heq as Hi Hj.
      subst i j.
      apply in_seq in Hin'.
      split; lia.
Qed.

(* The main theorem: pair lists are permutations *)
Lemma pairs_row_diag_permutation : forall (n : nat),
  Permutation
    (pairs_by_rows (S n) (fun i => (n - i + 1)%nat))
    (pairs_by_diags (S n)).
Proof.
  intros n.
  (* Strategy: Use count_occ_eq_impl_Permutation *)
  apply (count_occ_eq_impl_Permutation (nat * nat) nat_pair_eq_dec).
  intros [i j].

  (* Key equivalence: i+j <= n iff i <= n /\ j <= n-i *)
  assert (Equiv: (i + j <= n)%nat <-> (i <= n /\ j <= n - i)%nat) by lia.

  destruct (le_dec (i + j) n) as [Hij_le | Hij_gt].

  - (* Case: i + j <= n, so pair is in both lists with count = 1 *)
    (* Both lists have NoDup, so count is at most 1 *)
    (* Show pair is In both lists, so count = 1 *)
    assert (Hin_row: In (i, j) (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat))).
    { apply pair_in_row_list. lia. lia. }

    assert (Hin_diag: In (i, j) (pairs_by_diags (S n))).
    { apply pair_in_diag_list. exact Hij_le. }

    (* Convert In to count_occ = 1 using NoDup *)
    assert (Hc_row: count_occ nat_pair_eq_dec (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat)) (i, j) = 1%nat).
    { apply NoDup_count_occ'.
      - apply pairs_by_rows_NoDup.
      - exact Hin_row.
    }

    assert (Hc_diag: count_occ nat_pair_eq_dec (pairs_by_diags (S n)) (i, j) = 1%nat).
    { apply NoDup_count_occ'.
      - apply pairs_by_diags_NoDup.
      - exact Hin_diag.
    }

    rewrite Hc_row. rewrite Hc_diag. reflexivity.

  - (* Case: i + j > n, so pair is not in either list, count = 0 *)
    assert (Hout_row: ~ In (i, j) (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat))).
    { intros Hcontra.
      apply pairs_by_rows_bound in Hcontra.
      lia.
    }

    assert (Hout_diag: ~ In (i, j) (pairs_by_diags (S n))).
    { intros Hcontra.
      apply pairs_by_diags_bound in Hcontra.
      lia.
    }

    assert (Hc_row: count_occ nat_pair_eq_dec (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat)) (i, j) = 0%nat).
    { apply count_occ_not_In. exact Hout_row. }

    assert (Hc_diag: count_occ nat_pair_eq_dec (pairs_by_diags (S n)) (i, j) = 0%nat).
    { apply count_occ_not_In. exact Hout_diag. }

    rewrite Hc_row. rewrite Hc_diag. reflexivity.
Qed.

(* Use the pair permutation to get value list permutation *)
Lemma row_diag_lists_permutation : forall (f : nat -> nat -> R) (n : nat),
  Permutation
    (double_sum_to_list_rows f (S n) (fun i => (n - i + 1)%nat))
    (double_sum_to_list_diags f (S n)).
Proof.
  intros f n.
  (* Rewrite both sides as mapped pair lists *)
  rewrite row_value_list_eq_mapped_pairs.
  rewrite diag_value_list_eq_mapped_pairs.
  (* Apply Permutation_map with the pair permutation *)
  apply Permutation_map.
  apply pairs_row_diag_permutation.
Qed.

(* Derive the permutation from count_occ equality *)

(* Main theorem: Triangular summation reindexing

   Proof strategy using bijection and permutations:

   1. row_list_sum_correct: LHS = fold_right (row list)
   2. diag_list_sum_correct: RHS = fold_right (diagonal list)
   3. row_diag_lists_permutation: The lists are permutations
   4. sum_permutation_invariant: Permutations preserve sums
   5. QED
*)
Lemma summation_R_triangular : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n) =
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n).
Proof.
  intros f n.

  (* Step 1: Convert LHS to list sum via row_list_sum_correct *)
  rewrite <- row_list_sum_correct.

  (* Step 2: Convert RHS to list sum via diag_list_sum_correct *)
  rewrite <- diag_list_sum_correct.

  (* Step 3: Apply sum_permutation_invariant using row_diag_lists_permutation *)
  apply sum_permutation_invariant.
  apply row_diag_lists_permutation.
Qed.

(* ===== Additional lemmas for summation_R manipulations ===== *)

(* Change of variable in double sum *)
Lemma summation_R_change_of_var : forall (f : nat -> nat -> R) (n : nat),
  summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (min k n + 1)) (S n) =
  summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n).
Proof.
  intros f n.
  (* This is the key lemma for binomial expansion *)
  (* We need to show that summing over pairs (i, k-i) where 0 <= i <= k <= n *)
  (* is the same as summing over pairs (i, j) where 0 <= i <= n and 0 <= j <= n-i *)

  (* Key insight: For k <= n, we have min k n = k, so min k n + 1 = k + 1
     This means the inner sum behaves exactly as in summation_R_triangular *)

  (* First, show that we can replace (min k n + 1) with (k + 1) in the sum *)
  assert (H_min_eq: forall k, (k <= n)%nat -> (min k n + 1)%nat = (k + 1)%nat).
  {
    intros k Hk.
    rewrite Nat.min_l by assumption.
    reflexivity.
  }

  (* Rewrite LHS to use (k + 1) instead of (min k n + 1) *)
  assert (H_rewrite:
    summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (min k n + 1)) (S n) =
    summation_R (fun k => summation_R (fun i => f i (k - i)%nat) (k + 1)) (S n)).
  {
    apply summation_R_irrelevance_of_large_coeffs.
    intros k Hk.
    (* For k <= n, min k n = k *)
    rewrite H_min_eq by assumption.
    reflexivity.
  }

  rewrite H_rewrite.

  (* Now apply summation_R_triangular directly *)
  symmetry.
  apply summation_R_triangular.
Qed.

(* ===== Bridging between Coq.Reals notation and project notation ===== *)

(* Lemma: summation_R and sum_f_R0 are equivalent (after accounting for indexing) *)
Lemma summation_R_sum_f_R0_equiv : forall (f : nat -> R) (n : nat),
  summation_R f (S n) = sum_f_R0 f n.
Proof.
  intros f n.
  induction n as [|n' IH].
  - (* Base case: n = 0 *)
    simpl. ring.
  - (* Inductive case *)
    unfold summation_R at 1; fold summation_R.
    unfold sum_f_R0 at 1; fold sum_f_R0.
    rewrite <- IH.
    (* Goal: f (S n') + (f n' + summation_R f n') = summation_R f (S n') + f (S n') *)
    (* Unfold summation_R f (S n') on RHS to get f n' + summation_R f n' *)
    unfold summation_R at 2; fold summation_R.
    ring.
Qed.

(* Binomial theorem in summation_R notation *)
Theorem binomial_summation_R : forall (x y : R) (n : nat),
  (x + y) ^ n = summation_R (fun i => C n i * x ^ i * y ^ (n - i)) (S n).
Proof.
  intros x y n.
  rewrite summation_R_sum_f_R0_equiv.
  apply binomial.
Qed.

(* Corollary: Expansion of (x - a)^n *)
Corollary binomial_diff_expansion : forall (x a : R) (n : nat),
  (x - a) ^ n = summation_R (fun i => C n i * x ^ i * (- a) ^ (n - i)) (S n).
Proof.
  intros x a n.
  replace (x - a) with (x + (- a)) by ring.
  apply binomial_summation_R.
Qed.

(* Lemma: Distributing a function over summation with binomial expansion *)
Lemma summation_binomial_expansion : forall (f : nat -> R) (x a : R) (n : nat),
  summation_R (fun i => f i * (x - a) ^ i) (S n) =
  summation_R (fun j =>
    summation_R (fun i => f i * C i j * (- a) ^ (i - j)) (n - j + 1) * x ^ j) (S n).
Proof.
  intros f x a n.

  (* Step 1: Expand each (x-a)^i using binomial_diff_expansion *)
  assert (H_expand: forall i,
    f i * (x - a) ^ i = f i * summation_R (fun j => C i j * x ^ j * (- a) ^ (i - j)) (S i)).
  {
    intros i.
    rewrite binomial_diff_expansion.
    reflexivity.
  }

  (* Apply the expansion to each term *)
  assert (H_sum_expand:
    summation_R (fun i => f i * (x - a) ^ i) (S n) =
    summation_R (fun i => f i * summation_R (fun j => C i j * x ^ j * (- a) ^ (i - j)) (S i)) (S n)).
  {
    apply summation_R_irrelevance_of_large_coeffs.
    intros i Hi.
    rewrite H_expand.
    reflexivity.
  }

  rewrite H_sum_expand. clear H_sum_expand H_expand.

  (* Step 2: Distribute f i through the inner summation *)
  assert (H_dist: forall i,
    f i * summation_R (fun j => C i j * x ^ j * (- a) ^ (i - j)) (S i) =
    summation_R (fun j => f i * (C i j * x ^ j * (- a) ^ (i - j))) (S i)).
  {
    intros i.
    rewrite <- summation_R_mult_const.
    reflexivity.
  }

  (* Apply distribution to each term in outer sum *)
  assert (H_apply_dist:
    summation_R (fun i => f i * summation_R (fun j => C i j * x ^ j * (- a) ^ (i - j)) (S i)) (S n) =
    summation_R (fun i => summation_R (fun j => f i * (C i j * x ^ j * (- a) ^ (i - j))) (S i)) (S n)).
  {
    apply summation_R_irrelevance_of_large_coeffs.
    intros i Hi.
    rewrite H_dist.
    reflexivity.
  }

  rewrite H_apply_dist. clear H_apply_dist H_dist.

  (* Step 3: Now we have a double sum that needs rearranging
     Current: ∑_{i=0}^{n} ∑_{j=0}^{i} f(i) * C(i,j) * x^j * (-a)^(i-j)
     Goal: ∑_{j=0}^{n} [∑_{i=j}^{n} f(i) * C(i,j) * (-a)^(i-j)] * x^j

     The issue is that the inner sum goes from 0 to i (which changes with i),
     but summation_R_triangular expects the inner sum to go from 0 to (n-i).
     We need to adjust the indexing.
  *)

Admitted.
