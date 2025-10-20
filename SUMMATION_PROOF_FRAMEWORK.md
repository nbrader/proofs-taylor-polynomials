# Triangular Summation Proof Framework Using sum_permutation_invariant

## Overview

This document describes the bijection-based framework for proving the triangular summation reindexing lemma using `sum_permutation_invariant`. The approach uses Cantor's pairing function to establish that row-by-row and diagonal-by-diagonal enumerations of the triangular region are permutations of each other.

## The Problem

**Theorem to Prove** (`summation_R_triangular` / `prove_reindex_triangular`):

```coq
∑_{i=0}^n ∑_{j=0}^{n-i} f(i,j) = ∑_{k=0}^n ∑_{i=0}^k f(i, k-i)
```

Both sides sum over the triangular region `{(i,j) : 0 ≤ i ≤ n, 0 ≤ j ≤ n-i}`, just in different orders:
- **LHS**: Row-by-row enumeration
- **RHS**: Diagonal-by-diagonal enumeration (Cantor pairing)

## The Solution Strategy

### Key Insight

The bijection approach recognizes that:
1. Both enumerations cover the **same triangular region**
2. Each pair `(i,j)` appears **exactly once** in each enumeration
3. The enumerations are **permutations** of each other
4. By `sum_permutation_invariant`, **permutations preserve sums**

### Proof Structure

```
1. Convert nested summations to lists (row_list_sum_correct, diag_list_sum_correct)
2. Show lists are permutations (enumerate same multiset)
3. Apply sum_permutation_invariant
4. QED
```

## Infrastructure Built

### Core Theorems (Already Proved)

Located in `Coq/TaylorPolynomials/Summation.v`:

1. **`sum_permutation_invariant`** (lines 255-283)
   ```coq
   Permutation terms1 terms2 →
   fold_right Rplus 0 terms1 = fold_right Rplus 0 terms2
   ```
   Proof by induction on the Permutation relation.

2. **`count_occ_eq_impl_Permutation`** (lines 329-388)
   ```coq
   (∀x, count_occ eq_dec l1 x = count_occ eq_dec l2 x) →
   Permutation l1 l2
   ```
   Proof by induction on l1, using `in_split` and `Permutation_middle`.

3. **`sum_enumeration_invariant`** (lines 393-406)
   ```coq
   (∀x, count_occ Req_EM_T terms1 x = count_occ Req_EM_T terms2 x) →
   fold_right Rplus 0 terms1 = fold_right Rplus 0 terms2
   ```
   Direct application of `count_occ_eq_impl_Permutation` + `sum_permutation_invariant`.

### Bijection Infrastructure

4. **Cantor Pairing Functions** (lines 445-462)
   ```coq
   cantor_pair (i j : nat) : nat := (i + j) * (i + j + 1) / 2 + i
   cantor_diag, cantor_i, cantor_j : nat → nat  (* inverses *)
   ```
   Natural enumeration by diagonals.

5. **Bijection Transformations** (lines 464-484)
   ```coq
   diag_to_row_index (n i j : nat) : nat
   row_index_to_pair (n remaining_idx current_i : nat) : nat * nat
   ```
   Explicit bijection between row and diagonal enumeration indices.

6. **List Enumeration Functions** (lines 486-499)
   ```coq
   double_sum_to_list_rows (f : nat → nat → R) (i_max : nat) (j_func : nat → nat) : list R
   double_sum_to_list_diags (f : nat → nat → R) (k_max : nat) : list R
   ```
   Convert nested summations to flat lists.

### Helper Lemmas (Proved)

7. **`fold_right_Rplus_init`** (lines 501-509) ✅ **PROVED**
   ```coq
   fold_right Rplus a l = fold_right Rplus 0 l + a
   ```
   Key for reorganizing fold_right expressions.

8. **`sum_map_seq`** (lines 511-527) ✅ **PROVED**
   ```coq
   fold_right Rplus 0 (map g (seq 0 n)) = summation_R g n
   ```
   **Critical lemma** connecting list sums to summation_R.
   Proof by induction using `seq_S`, `map_app`, `fold_right_app`, and `fold_right_Rplus_init`.

9. **`extend_inner_sum`** (lines 422-437) ✅ **PROVED**
   ```coq
   (i ≤ n)%nat →
   summation_R (fun j => f i j) (S n - i + 1) =
   summation_R (fun j => f i j) (n - i + 1) + f i (S n - i)
   ```
   Shows how inner summations extend by one term.

10. **`summation_R_rectangular_symmetric`** (lines 605-609) ✅ **PROVED**
    ```coq
    summation_R (fun i => summation_R (fun j => f i j) n) m =
    summation_R (fun j => summation_R (fun i => f i j) m) n
    ```
    Direct application of `summation_R_exchange`.

### Technical Lemmas (Documented Strategies)

11. **`row_list_sum_correct`** (lines 541-553) ⏸️ **ADMITTED**
    ```coq
    fold_right Rplus 0 (double_sum_to_list_rows f (S n) (fun i => n - i + 1)) =
    summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n)
    ```
    **Strategy**: Induction on n, using `sum_map_seq` for inner sums and `fold_right_app` for appends.
    **Challenge**: Nested append structure requires careful management of changing row sizes.

12. **`diag_list_sum_correct`** (lines 567-597) ⏸️ **ADMITTED**
    ```coq
    fold_right Rplus 0 (double_sum_to_list_diags f (S n)) =
    summation_R (fun k => summation_R (fun i => f i (k - i)) (k + 1)) (S n)
    ```
    **Strategy**: Similar to row version, but diagonal structure is more uniform.
    **Challenge**: Nested appends create complex fold_right expressions.

### Main Theorem (Framework Complete)

13. **`prove_reindex_triangular`** (lines 626-655) ⏸️ **FRAMEWORK COMPLETE**
    ```coq
    summation_R (fun i => summation_R (fun j => f i j) (n - i + 1)) (S n) =
    summation_R (fun k => summation_R (fun i => f i (k - i)) (k + 1)) (S n)
    ```
    **Proof Path**:
    1. Apply `row_list_sum_correct` to convert LHS to list sum
    2. Apply `diag_list_sum_correct` to convert RHS to list sum
    3. Prove lists enumerate same multiset (count_occ equal for all values)
    4. Apply `sum_enumeration_invariant`

    **Status**: Framework complete, pending technical lemmas 11-12.

## Computational Verification

File: `/tmp/verify_triangular.py`

Verified for n = 0 to 4:
```python
n = 2:
  LHS terms: [(0,0,0), (0,1,1), (0,2,2), (1,0,10), (1,1,11), (2,0,20)]
  RHS terms: [(0,0,0), (0,1,1), (1,0,10), (0,2,2), (1,1,11), (2,0,20)]
  Same multiset: True ✓
```

Confirms both sides enumerate identical multisets.

## Technical Challenges

### Nested Append Structure

The fixpoint definitions build lists via nested appends:
```coq
double_sum_to_list_diags f (S (S n)) =
  (double_sum_to_list_diags f n ++ diag_n) ++ diag_{S n}
```

This creates complex `fold_right` expressions requiring:
- Multiple applications of `fold_right_app`
- Reorganization with `fold_right_Rplus_init`
- Careful matching of induction hypothesis

### Proof Engineering Required

The remaining technical work is proof engineering rather than conceptual:
- **What**: Prove list conversions handle nested structure correctly
- **How**: Controlled unfolding, strategic rewrites, careful goal management
- **Why tricky**: Coq's simplification sometimes expands too aggressively

## Alternative Approaches Considered

### 1. Direct Induction (Original Attempt)
Expand both sides and show they add same terms at each step.
**Issue**: Complex arithmetic with `lia` on nested indices.

### 2. Rectangular Decomposition
Show both equal a rectangular sum minus upper triangle.
**Issue**: Requires multiple intermediate lemmas.

### 3. Bijection via Lists (Current Approach)
Convert to lists, show permutation, apply invariance.
**Advantage**: Clean separation of concerns, leverages existing theorems.

## Summary of Achievement

✅ **Complete bijection framework** using Cantor's pairing
✅ **All foundational lemmas proved** (`sum_permutation_invariant`, helper lemmas)
✅ **Clear proof path** with documented strategies
✅ **Computational verification** confirms correctness
✅ **All code compiles** and builds successfully

**Remaining**: Technical proof engineering for nested list structures (lemmas 11-12).

## Files

- **Main proof file**: `Coq/TaylorPolynomials/Summation.v`
- **Computational verification**: `/tmp/verify_triangular.py`
- **This documentation**: `SUMMATION_PROOF_FRAMEWORK.md`

## References

- Cantor pairing: https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
- Coq Permutation library: Coq.Sorting.Permutation
- Coq Lists library: Coq.Lists.List

---

**Last updated**: 2025-10-20
**Build status**: ✅ All files compile
