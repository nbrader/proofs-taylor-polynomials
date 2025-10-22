# Proof Plan: pair_in_row_list and pair_in_diag_list

## Goal

Prove that every valid pair appears in the respective enumeration lists, analogous to Cantor's proof that the pairing function is surjective onto pairs.

### Lemmas to Prove

```coq
Lemma pair_in_row_list : forall (n i j : nat),
  (i <= n)%nat -> (j < n - i + 1)%nat ->
  In (i, j) (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat)).

Lemma pair_in_diag_list : forall (n i j : nat),
  (i + j <= n)%nat ->
  In (i, j) (pairs_by_diags (S n)).
```

## Cantor's Approach: Key Insight

Cantor proved his pairing function `ℕ × ℕ → ℕ` is a bijection by showing:
1. **Injectivity**: Different pairs map to different naturals
2. **Surjectivity**: Every pair (a,b) appears at position `cantor_pair(a,b)`

For our case, we adapt this to prove **coverage**: every valid pair appears *somewhere* in the enumeration.

## Strategy: Constructive Membership Proofs

Instead of proving via induction on n (which led to misaligned structures), we prove **directly** by construction:

### Core Idea

For any valid pair (i,j), we:
1. **Identify which iteration** of the fixpoint adds this pair
2. **Show it's in the appended segment** at that iteration
3. **Use `in_or_app`** to conclude membership in the full list

This mirrors Cantor's approach: "pair (a,b) appears at diagonal k = a+b, position a within that diagonal"

## Proof Plan for `pair_in_diag_list`

**Easier case** - prove this first as a template.

### Statement
```coq
Lemma pair_in_diag_list : forall (n i j : nat),
  (i + j <= n)%nat ->
  In (i, j) (pairs_by_diags (S n)).
```

### Key Observation

For diagonal enumeration:
- Pair (i,j) appears on diagonal `k = i + j`
- It appears at position `i` within that diagonal
- The diagonal is enumerated as `map (fun i => (i, k-i)) (seq 0 (k+1))`

### Proof Structure

```coq
Proof.
  intros n i j Hij.

  (* Step 1: Identify which diagonal k contains (i,j) *)
  set (k := (i + j)%nat).

  (* Step 2: Show k <= n by hypothesis *)
  assert (Hk: k <= n) by lia.

  (* Step 3: Induction on n to show membership *)
  induction n as [|n' IHn].

  - (* Base case: n = 0 *)
    (* Only pair is (0,0) *)
    assert (i = 0 /\ j = 0) by lia.
    destruct H; subst.
    simpl. left. reflexivity.

  - (* Inductive case: n' -> S n' *)
    destruct (Nat.eq_dec k (S n')).

    + (* k = S n': pair is on the NEW diagonal being added *)
      subst k.
      simpl pairs_by_diags.
      apply in_or_app. right.

      (* Show (i,j) is in the newly appended diagonal *)
      apply in_map_iff.
      exists i.
      split.
      * (* Show map produces (i, j) *)
        simpl. f_equal. lia.
      * (* Show i is in seq 0 (S n' + 1) *)
        apply in_seq. lia.

    + (* k < S n': pair is in previous diagonals *)
      simpl pairs_by_diags.
      apply in_or_app. left.
      apply IHn. lia.
Qed.
```

### Why This Works

- **Constructive**: We explicitly identify which iteration adds the pair
- **No misalignment**: We don't compare incremental additions, we directly place the pair
- **Mirrors Cantor**: "Pair (i,j) is at diagonal k=i+j, so look at iteration k"

## Proof Plan for `pair_in_row_list`

**Harder case** - but same strategy.

### Statement
```coq
Lemma pair_in_row_list : forall (n i j : nat),
  (i <= n)%nat -> (j < n - i + 1)%nat ->
  In (i, j) (pairs_by_rows (S n) (fun i' => (n - i' + 1)%nat)).
```

### Key Observation

For row enumeration:
- Pair (i,j) appears in row `i`
- Row i is enumerated as `map (fun j => (i, j)) (seq 0 (n - i + 1))`
- Row i is appended at iteration `i` of the fixpoint

### Proof Structure

```coq
Proof.
  intros n i j Hi Hj.

  (* Step 1: Identify which iteration adds row i *)
  (* Row i is added at iteration (S i) *)

  (* Step 2: Induction on n *)
  induction n as [|n' IHn].

  - (* Base case: n = 0 *)
    (* Only valid pair is (0,0) *)
    assert (i = 0) by lia.
    assert (j = 0) by lia.
    subst.
    simpl. left. reflexivity.

  - (* Inductive case: n' -> S n' *)
    destruct (Nat.eq_dec i (S n')).

    + (* i = S n': this is the NEW row being added *)
      subst i.
      simpl pairs_by_rows.
      apply in_or_app. right.

      (* Show (S n', j) is in the newly appended row *)
      apply in_map_iff.
      exists j.
      split.
      * (* Map produces (S n', j) *)
        reflexivity.
      * (* j is in seq 0 (n' - n' + 1) = seq 0 1 *)
        apply in_seq.
        (* Need to show: j < row_size for row (S n') *)
        (* row_size = S n' - S n' + 1 = 1 when n' = n *)
        lia.

    + (* i < S n': pair is in previous rows *)
      simpl pairs_by_rows.
      apply in_or_app. left.
      apply IHn.
      * lia.
      * (* Need to adjust bound for smaller n *)
        lia.
Qed.
```

### Challenges

The row case is trickier because:
1. **Row size changes**: Row i has `(n - i + 1)` elements, but this varies with n
2. **Bounds shift**: When going from n' to S n', row sizes increase for i < S n'

### Solution: Careful Arithmetic

The key is showing that if `j < n - i + 1` and `i < S n'`, then also `j < n' - i + 1` (this may not always hold - need to check).

Actually, wait: if `i <= n'` and `j < n - i + 1` where `n = S n'`, then:
- `j < S n' - i + 1 = n' - i + 2`

So the bound is actually **looser** for smaller n if `i` stays the same. This should work!

## Alternative: Prove List Structure Lemmas First

If direct proof is too complex, we could first prove helper lemmas:

### Helper Lemma 1: Row Structure
```coq
Lemma pairs_by_rows_structure : forall n j_func i,
  (i < n)%nat ->
  exists prefix row suffix,
    pairs_by_rows n j_func = prefix ++ row ++ suffix /\
    row = map (fun j => (i, j)) (seq 0 (j_func i)) /\
    In (i, j) row -> In (i, j) (pairs_by_rows n j_func).
```

### Helper Lemma 2: Append Membership
```coq
Lemma in_appended_segment : forall (A : Type) (l : list A) (new_segment : list A) (x : A),
  In x new_segment ->
  In x (l ++ new_segment).
```

These helpers make the main proofs cleaner.

## Verification Strategy

1. **Test with Compute**: Verify specific cases
   ```coq
   Example test_pair_in_row_2_0_1:
     In (0, 1) (pairs_by_rows 3 (fun i => (2 - i + 1)%nat)) = true.
   Proof. simpl. reflexivity. Qed.
   ```

2. **Python verification**: Ensure all pairs in triangular region appear
   ```python
   def verify_all_pairs_present(n):
       row_pairs = set(pairs_by_rows_v1(n))
       expected = {(i,j) for i in range(n+1) for j in range(n-i+1)}
       return row_pairs == expected
   ```

3. **Gradual proof**: Start with small n, prove by hand, extract pattern

## Order of Implementation

1. ✅ Define helper `in_or_app` uses (already in stdlib)
2. ✅ Define helper `in_map_iff` uses (already in stdlib)
3. ✅ Define helper `in_seq` lemmas (already in stdlib)
4. **NEXT**: Prove `pair_in_diag_list` (easier)
5. **THEN**: Prove `pair_in_row_list` (using lessons from diagonal case)
6. **FINALLY**: Prove `pairs_row_diag_permutation` by showing:
   - Each list has no duplicates (via injectivity)
   - Both enumerate the same set (via membership lemmas)
   - Therefore they're permutations (via set equality + no duplicates)

## Success Criteria

✅ Both membership lemmas proven
✅ `pairs_row_diag_permutation` proven
✅ `summation_R_triangular` fully proven (only admits in foundation)
✅ All Compute examples pass
✅ Python verification confirms correctness

---

This approach transforms the induction-based proof into a direct, constructive proof that explicitly identifies where each pair appears, making it much more straightforward and avoiding the structural misalignment issues.
