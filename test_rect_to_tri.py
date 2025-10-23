#!/usr/bin/env python3
"""
Test the rectangular to triangular summation conversion.

Coq statement:
summation_R (fun i => summation_R (fun j => f i j) (S n)) (S n) =
summation_R (fun i => summation_R (fun j => f i j) (i + 1)) (S n) +
summation_R (fun i => summation_R (fun j => f j i) (n - i + 1)) n

Note: summation_R goes from 0 to (n-1) when given argument n
So: summation_R g (S n) sums g(0) + g(1) + ... + g(n)
    summation_R g n sums g(0) + g(1) + ... + g(n-1)
"""

def test_rect_to_tri(n, f):
    """
    Test if the rectangular sum equals sum of lower and upper triangular parts.

    LHS: ∑_{i=0}^{n} ∑_{j=0}^{n} f(i,j)  (rectangle: (S n) means n+1 terms, 0..n)
    RHS1: ∑_{i=0}^{n} ∑_{j=0}^{i} f(i,j)  (lower tri including diagonal)
    RHS2: ∑_{i=0}^{n-1} ∑_{j=0}^{n-i} f(j,i)  (upper tri excluding diagonal)
    """
    # LHS: (S n) × (S n) rectangle
    # summation_R ... (S n) means sum from 0 to n inclusive
    lhs = sum(f(i, j) for i in range(n+1) for j in range(n+1))

    # RHS part 1: lower triangular (including diagonal)
    # summation_R (fun i => summation_R (fun j => f i j) (i + 1)) (S n)
    # For each i from 0 to n, sum j from 0 to i
    lower_tri = sum(f(i, j) for i in range(n+1) for j in range(i+1))

    # RHS part 2: upper triangular (excluding diagonal)
    # summation_R (fun i => summation_R (fun j => f j i) (n - i + 1)) n
    # For each i from 0 to n-1, sum j from 0 to (n-i), using f(j,i)
    upper_tri = sum(f(j, i) for i in range(n) for j in range(n-i+1))

    rhs = lower_tri + upper_tri

    print(f"n={n}")
    print(f"LHS (rectangle): {lhs}")
    print(f"RHS (lower tri): {lower_tri}")
    print(f"RHS (upper tri): {upper_tri}")
    print(f"RHS (total): {rhs}")
    print(f"Equal: {lhs == rhs}")
    print()

    # Visualize which (i,j) pairs contribute to which sums
    print("Rectangle - all (i,j) pairs where f(i,j) is summed:")
    rect_pairs = sorted([(i, j) for i in range(n+1) for j in range(n+1)])
    print(f"  {rect_pairs}")

    print("Lower triangle - all (i,j) pairs where f(i,j) is summed:")
    lower_pairs = sorted([(i, j) for i in range(n+1) for j in range(i+1)])
    print(f"  {lower_pairs}")

    print("Upper triangle - all (j,i) shown as (i,j) where f(j,i) is summed:")
    # The upper sum is f(j,i), but to show which f(a,b) values appear, we list (j,i) as (a,b)
    upper_pairs_as_args = sorted([(j, i) for i in range(n) for j in range(n-i+1)])
    print(f"  {upper_pairs_as_args}")

    # Combined
    combined = sorted(set(lower_pairs + upper_pairs_as_args))
    print(f"\nCombined unique (i,j) where f(i,j) appears: {len(combined)} pairs")
    print(f"  {combined}")
    print(f"Rectangle has: {len(rect_pairs)} pairs")
    print(f"All covered: {combined == rect_pairs}")

    return lhs == rhs

# Test with a simple function
def f(i, j):
    return i * 10 + j

# Test for n=0, 1, 2, 3
for n in [0, 1, 2, 3]:
    test_rect_to_tri(n, f)
    print("-" * 60)
