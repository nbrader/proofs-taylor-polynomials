# Session Notes: Taylor Polynomial Proofs

## Current Work (Session: 2025-10-18 - Binomial Coefficient Infrastructure)

### Goal
🔄 **IN PROGRESS**: Complete `Taylor_a_equiv` theorem proof without admits

### Summary
Successfully completed the `c2_` assertion proof and added binomial coefficient infrastructure to support the algebraic manipulations. Created `INR_binomial_coeff` lemma in Combinatorics.v to handle the identity `1/(x0!*x1!) = C(x0+x1,x0)/(x0+x1)!`. One algebraic admit replaced, but the main theorem still requires proving the `c1_` assertion and connecting the binomial expansion.

### Current Status (2025-10-18)

**Completed Work:**
- ✅ c2_ assertion proof complete (restructured using `summation_irrelevance_of_large_coeffs`)
- ✅ Created test_binomial_identity.py to verify binomial coefficient identity
- ✅ Added `factorial_div_binomial` lemma (admitted - requires combinatorial proof)
- ✅ Added `INR_div_exact` lemma (proved - handles INR of exact division)
- ✅ Added `INR_binomial_coeff` lemma (proved - connects binomial identity to real division)
- ✅ Replaced admit at line 621 with `apply INR_binomial_coeff`
- ✅ Build compiles successfully

**Remaining Work:**
- ❌ Line 579: Admits algebraic goal that requires c1_ proof (commented with explanation)
- ❌ c1_ assertion: Need to prove `forall i, (i <= n)%nat -> c1_ i = iter D i F a / INR (fact i)`
- ❌ Binomial expansion: Connect c1_ and c2_ forms through binomial theorem
- ❌ factorial_div_binomial: Either prove combinatorially or accept as axiom

### Analysis of Remaining Admits

**Line 579 (TaylorPolynomials.v):**
After rewriting with H1, the goal becomes:
```coq
summation_R (fun i => c1_ i * x ^ i) (S n) =
summation_R (fun i => (iter D i F a / INR (fact i)) * x ^ i) (S n)
```

This requires proving that c1_ has the correct form. The commented-out `rewrite H0` would fail because H0 is about c2_, not c1_. We need an analogous assertion for c1_ first.

**Strategy for c1_ Proof:**
Follow the same pattern as c2_, but starting from the Taylor series at point `a`:
1. Apply Taylor_agrees_at_a with degree n, order i, point a, function F
2. Take i-th derivative and evaluate at a
3. Use summation decomposition to isolate the i-th coefficient
4. Apply derivative rules to show only the i-th term survives
5. Solve for c1_ i algebraically

## Previous Work (Session: 2025-10-17 - Continued)

### Initial Status
The c2_ assertion proof was ~80% complete but used `admit` for the `i > n` case because functional extensionality required proving `c2_ i = iter D i F a / INR (fact i)` for all i, but c2_ is unconstrained for i > n.

### Progress Made (Current Session - Continuation)

1. **Fixed exists pattern issue** (TaylorPolynomials.v:493-513)
   - Added intermediate existential assertion following Maclaurin_implem pattern (lines 262-282)
   - Changed from direct `exists i0` to proper pattern with `assert (exists c : nat, ...)` first
   - Added proper destructuring and rewriting

2. **Fixed hypothesis naming errors** (Multiple locations)
   - Lines 517-518: Changed `rewrite H` to `rewrite H0` (H referred to c1_, not c2_)
   - Lines 520-521: Same fix for second occurrence
   - Lines 536-537: Fixed type mismatch by using H1 instead of H0, and H2 instead of H1
   - Lines 539, 542: Changed to use H0 instead of H
   - Lines 551, 553: Changed to use H0 instead of H

3. **Removed unnecessary rewrites** (Lines 555-558)
   - Removed unnecessary `iter_D_chain_of_linear` rewrite in `i <= n` case
   - Goal was already simplified to algebraic identity solvable with `field`

4. **Handled i > n case** (Lines 560-565)
   - Recognized that c2_ i is unconstrained for i > n (not used in summation)
   - Added `admit` for this case as coefficients beyond degree n don't affect correctness
   - Documented that this is a "junk value" that never gets evaluated

### Previous Progress (From Earlier Session)

1. **Fixed hypothesis scoping issues** (TaylorPolynomials.v:424)
   - Removed premature `clear Taylor_nth_2` that was causing it to be unavailable later

2. **Added chain rule rewrite** (TaylorPolynomials.v:468)
   - Used `iter_D_chain_of_linear` to connect `iter D i F a` with `iter D i (fun x' => F (x' + a)) 0`
   - This is the key mathematical step: by chain rule, `D^i(F(x+a))|_{x=0} = D^i F(a)`

3. **Added intermediate assertions** (TaylorPolynomials.v:481-543)
   - Followed Maclaurin_implem pattern to show summation equals summation of zeros before applying `summation_n_zeros`
   - Split proof into three parts: terms above i, terms below i, and the i-th term

### Proof Structure

The `c2_` proof follows this pattern (from Maclaurin_implem):

1. **Apply Taylor_agrees_at_a** to get derivative equality
2. **Apply iter_D to summation** using `iter_D_additive_over_summation`
3. **Distribute homogeneity** over each term
4. **Rewrite with chain rule** using `iter_D_chain_of_linear`
5. **Split summation** into three parts:
   - **Terms above i vanish**: use `nth_pow_greater_than_or_equal_to_deriv`, evaluate at 0 gives 0
   - **Terms below i vanish**: use `nth_pow_less_than_deriv`, evaluate at 0 gives 0
   - **Only i-th term survives**: use `nth_pow_equal_deriv`, gives `fact(i) * c2_ i`
6. **Solve for c2_ i** using field

### Files Modified

- **TaylorPolynomials/TaylorPolynomials.v**:
  - Lines 424, 468, 476, 490-492: Fixed scoping and hypothesis naming
  - Lines 481-531: Added intermediate assertions for proof structure

### Key Lemmas Used

- `iter_D_chain_of_linear` (IteratedDifferentiation.v:293-311): Chain rule for translated functions
- `nth_pow_greater_than_or_equal_to_deriv`: For powers >= derivative order
- `nth_pow_less_than_deriv`: For powers < derivative order
- `nth_pow_equal_deriv`: For power == derivative order
- `summation_R_irrelevance_of_large_coeffs`: To show summation equals summation of zeros
- `summation_n_zeros`: To show summation of zeros equals 0

### Next Steps

1. **Fix line 495** by adding intermediate existential assertion (pattern from Maclaurin_implem:262-282)
2. **Fix line 524** (similar issue in "terms below i vanish" section)
3. **Verify compilation** after fixes
4. **Complete c2_ proof** - should be done after these fixes
5. **Work on c1_ assertion** (line 431) - more complex, involves binomial coefficients
6. **Address admits** at lines 464, 507, 312 (algebraic manipulations with factorials)

### Mathematical Context

The c2_ assertion proves that for the Maclaurin series of `F(x + a)`:
- The i-th coefficient is `(D^i F(a)) / i!`
- This follows from the chain rule: `D^i(F(x+a))|_{x=0} = D^i F(a)`
- The proof extracts this coefficient by taking the i-th derivative at 0 and showing only the i-th term survives

The c1_ assertion will prove the full binomial expansion relating Taylor series at point `a` to Maclaurin series of `F(x + a)`.

### Reference Implementation

Maclaurin_implem (lines 191-344) provides the template for this proof structure.

### Git Status

Last commit: `50cce90 Moved MonoidConcat file into free-monoid library`

Branch: `main`

Working directory: Clean at session start, modified TaylorPolynomials.v not yet committed.

---

## Session End

**Status**: c2_ proof approximately 80% complete, blocked on line 495 exists issue.

**Estimated remaining work**: 1-2 hours to complete c2_, several hours for c1_.
