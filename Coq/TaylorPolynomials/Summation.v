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

(* ==== Bijection-based approach to triangular summation ====

   Strategy: Use Cantor's pairing function to establish bijections between ℕ and
   pairs in the triangular region. The diagonal enumeration uses Cantor pairing
   directly, while the row enumeration uses a composed bijection.
*)

(* Cantor pairing function: maps pairs (i,j) to a unique natural number *)
Definition cantor_pair (i j : nat) : nat :=
  (i + j) * (i + j + 1) / 2 + i.

(* Inverse of Cantor pairing - returns the diagonal k = i + j *)
Definition cantor_diag (n : nat) : nat :=
  let k := Nat.sqrt (2 * n) in
  if (k * (k + 1) / 2 <=? n) then k else k - 1.

(* Cantor pairing inverse - returns i from the encoding *)
Definition cantor_i (n : nat) : nat :=
  let k := cantor_diag n in
  n - (k * (k + 1) / 2).

(* Cantor pairing inverse - returns j from the encoding *)
Definition cantor_j (n : nat) : nat :=
  let k := cantor_diag n in
  k - (n - (k * (k + 1) / 2)).

(* Transform from diagonal to row enumeration for triangular region *)
(* For a pair (i,j) with i+j ≤ n, we map it based on which row it's in *)
Definition diag_to_row_index (n : nat) (i j : nat) : nat :=
  (* Row i contains (n - i + 1) elements, so the index is:
     sum of previous row sizes + position in current row *)
  let prev_rows := summation_R (fun k => INR (n - k + 1)) i in
  Z.to_nat (Int_part prev_rows) + j.

(* Transform from row to diagonal enumeration *)
(* This is the inverse: given a linear index, find (i,j) such that it's
   the j-th element in row i *)
Fixpoint row_index_to_pair (n remaining_idx current_i : nat) {struct current_i} : (nat * nat) :=
  match current_i with
  | O => (0%nat, 0%nat) (* Shouldn't reach here if properly bounded *)
  | S i' =>
      let row_size := (n - i' + 1)%nat in
      if (remaining_idx <? row_size) then
        (i', remaining_idx)
      else
        row_index_to_pair n (remaining_idx - row_size) i'
  end.

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

(* Alternative direct approach: Prove by showing both equal a rectangular sum minus upper triangle *)

(* Helper: Rectangular sum can be expressed in both row and column order *)
Lemma summation_R_rectangular_symmetric : forall (f : nat -> nat -> R) (m n : nat),
  summation_R (fun i => summation_R (fun j => f i j) n) m =
  summation_R (fun j => summation_R (fun i => f i j) m) n.
Proof.
  intros f m n.
  (* This is just summation_R_exchange with swapped indices *)
  apply summation_R_exchange.
Qed.

(* Alternative: Prove via explicit construction of terms and sum_enumeration_invariant *)

(* Helper: Given n, construct the list of all (i,j) pairs in triangular region *)
Fixpoint triangular_pairs (n : nat) : list (nat * nat) :=
  match n with
  | O => [(0%nat, 0%nat)]
  | S n' => triangular_pairs n' ++
            map (fun i => (i, (S n' - i)%nat)) (seq 0 (S (S n')))
  end.

(* Helper: Apply function to pair and collect as list of R *)
Definition eval_pairs (f : nat -> nat -> R) (pairs : list (nat * nat)) : list R :=
  map (fun p => f (fst p) (snd p)) pairs.

(* Critical helper: fold_right over nested appends *)
Lemma fold_right_double_append : forall (l1 l2 l3 : list R),
  fold_right Rplus 0 ((l1 ++ l2) ++ l3) =
  fold_right Rplus 0 l1 + fold_right Rplus 0 l2 + fold_right Rplus 0 l3.
Proof.
  intros l1 l2 l3.
  (* Apply fold_right_Rplus_app twice: first to split (l1++l2)++l3, then to split l1++l2 *)
  rewrite fold_right_Rplus_app.
  rewrite fold_right_Rplus_app.
  ring.
Qed.

(* Critical missing lemma: Both list enumerations produce the same multiset of values

   This is the KEY lemma that was missing from the original framework!
   Without this, we can't apply sum_enumeration_invariant.

   Strategy: Prove by induction that both lists enumerate exactly the pairs
   {(i,j) : 0 ≤ i ≤ n, 0 ≤ j ≤ n-i}, which means for any value v = f(i,j),
   it appears the same number of times in both lists.
*)
Lemma row_diag_same_multiset : forall (f : nat -> nat -> R) (n : nat),
  forall x, count_occ Req_EM_T
    (double_sum_to_list_rows f (S n) (fun i => (n - i + 1)%nat)) x =
    count_occ Req_EM_T
    (double_sum_to_list_diags f (S n)) x.
Proof.
  (* This lemma states that both enumeration methods produce the same multiset.

     Full proof strategy:
     1. Show both lists enumerate exactly {f(i,j) : 0 ≤ i ≤ n, 0 ≤ j ≤ n-i}
     2. For the row enumeration: i ranges over 0..n, j ranges over 0..(n-i)
     3. For the diagonal enumeration: k ranges over 0..n, i ranges over 0..k, j = k-i
     4. Show the bijection: (i,j) in rows ↔ (k=i+j, i) in diagonals
     5. Prove each (i,j) appears exactly once in each enumeration
     6. Since f is applied to the same pairs, count_occ must be equal

     This requires:
     - Lemmas about list membership and count_occ properties
     - Proof that seq produces distinct elements
     - Proof that different rows/diagonals are disjoint
     - Induction on n to build up the equality

     This is a substantial proof that would require 50-100 lines of Coq.
     For now, we admit it as the key remaining technical lemma. *)
Admitted.

(* Main theorem: Triangular summation reindexing

   Proof strategy using sum_enumeration_invariant:

   1. row_list_sum_correct: LHS = fold_right (row list)
   2. diag_list_sum_correct: RHS = fold_right (diagonal list)
   3. row_diag_same_multiset: Both lists have same multiset
   4. sum_enumeration_invariant: Same multiset → equal sums
   5. QED

   All pieces are in place, just need to complete row_diag_same_multiset.
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

  (* Step 3: Apply sum_enumeration_invariant using row_diag_same_multiset *)
  apply sum_enumeration_invariant.
  apply row_diag_same_multiset.
Qed.

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
